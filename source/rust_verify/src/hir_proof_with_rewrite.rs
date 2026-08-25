//! Redirect `proof_with((extra, ..), f(args))` calls to the verified counterpart
//! of `f` before rustc type checks the crate.
//!
//! `#[verus_spec(with ...)]` generates two functions: the unverified stub `f`,
//! which keeps the original signature and carries
//! `#[verus::internal(unverified_stub)]`, and the verified
//! function `_VERUS_VERIFIED_f`, whose signature also contains the extra
//! ghost/tracked parameters and returns the extra ghost/tracked outputs, and attributes include
//! `#[verus::internal(verified_with)]`.
//!
//! When call `f` in verification mode, we should use `_VERUS_VERIFIED_f`. However,
//! verus macro is not reliable to rewrite the call: since a call may be
//! written as `$path::f(..)`, through a `use` alias, or as a method call. Thus, we
//! need to rewrite the HIR after macro expansion, but before type checking.

use crate::attributes::{Attr, parse_attrs_opt};
use rustc_data_structures::steal::Steal;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{
    Arm, Block, Expr, ExprField, ExprKind, GenericBound, Generics, ItemLocalId, LetExpr,
    MaybeOwner, Node, OwnerNode, ParentedNode, PathSegment, PolyTraitRef, QPath, Stmt, StmtKind,
    TraitRef, Ty, TyKind, WhereBoundPredicate, WherePredicate, WherePredicateKind,
};
use rustc_index::IndexVec;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefIndex;
use rustc_span::symbol::Symbol;
use std::collections::{HashMap, HashSet};

/// Name prefix used by the `verus_spec` macro for the verified counterpart.
/// Must be kept in sync with `builtin_macros::attr_rewrite::VERIFIED`.
const VERIFIED_PREFIX: &str = "_VERUS_VERIFIED";
/// Keep in sync with `builtin_macros::unerased_proxies::VERUS_UNERASED_PROXY`.
const UNERASED_PROXY_PREFIX: &str = "VERUS_UNERASED_PROXY__";

pub(crate) fn hir_proof_with_rewrite<'tcx>(
    mut crate_: rustc_middle::hir::Crate<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> rustc_middle::hir::Crate<'tcx> {
    // See hir_hide_reveal_rewrite: with delayed_ids empty, Crate::owner() returns
    // directly from the internal owners vec without triggering query cycles.
    let delayed_ids = std::mem::take(&mut crate_.delayed_ids);
    let mut new_owners: IndexVec<LocalDefId, MaybeOwner<'tcx>> = IndexVec::new();
    let num_defs = tcx.definitions_untracked().num_definitions();
    for i in 0..num_defs {
        let def_id = LocalDefId { local_def_index: DefIndex::from_usize(i) };
        let owner = new_owners.ensure_contains_elem(def_id, || MaybeOwner::Phantom);
        *owner = crate_.owner(tcx, def_id);
    }

    let owners = new_owners.clone();
    let ctxt = Ctxt::new(tcx, &owners);

    let mut injections: HashMap<LocalDefId, Vec<Injection>> = HashMap::new();
    for i in 0..new_owners.len() {
        let def_id = LocalDefId { local_def_index: DefIndex::from_usize(i) };
        let MaybeOwner::Owner(inner_owner) = new_owners[def_id] else {
            continue;
        };
        if let Some(owner) = rewrite_owner(&ctxt, inner_owner, def_id, &owners, &mut injections) {
            new_owners[def_id] = owner;
        }
    }
    for (def_id, injections) in injections {
        let MaybeOwner::Owner(inner_owner) = new_owners[def_id] else {
            continue;
        };
        if let Some(owner) = inject_bounds(tcx, inner_owner, &injections) {
            new_owners[def_id] = owner;
        }
    }

    rustc_middle::hir::Crate::new(
        new_owners,
        delayed_ids,
        crate_.delayed_resolver,
        crate_.opt_hir_hash.clone(),
    )
}

struct Ctxt<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    /// The owners of this crate, as they were before the rewrite. Attributes are
    /// read from here, since reading them through `tcx` would re-enter the
    /// `hir_crate` query that this pass is part of.
    owners: &'a IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    /// External function -> the verified counterpart declared for it by a local
    /// `assume_specification`. The external function cannot carry a `verified_by`
    /// attribute itself, so the link is indexed the other way round.
    external_targets: HashMap<DefId, DefId>,
    /// Verified counterpart name -> the companion traits that declare a method
    /// with that name. Name resolution keys the traits that are in scope for a
    /// method call by the name written in the source, so the companion trait,
    /// which declares the counterpart and not the method it is the counterpart
    /// of, is never a candidate for the call; the rewrite adds it back, see
    /// `rewrite_owner`.
    companions_by_method: HashMap<Symbol, Vec<DefId>>,
    /// Trait -> the traits it declares as supertraits. Used to find the trait a
    /// companion trait belongs to, and to elaborate the bounds of a caller, see
    /// `Injection`.
    trait_supers: HashMap<DefId, Vec<DefId>>,
}

/// The attributes of a local item, read from the owners this pass was handed.
fn owner_attrs<'tcx>(
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    def_id: LocalDefId,
) -> Option<&'tcx [rustc_hir::Attribute]> {
    let MaybeOwner::Owner(owner) = owners.get(def_id)? else {
        return None;
    };
    Some(owner.attrs.get(ItemLocalId::ZERO))
}

/// The attributes of any item.
///
/// `attrs_for_def` only answers for another crate; for a local item rustc reads the
/// attributes off the HIR owner, which is the `hir_crate` result this pass is
/// computing, so a local item is looked up in the owners this pass was handed.
fn def_attrs<'tcx>(
    tcx: TyCtxt<'tcx>,
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    def_id: DefId,
) -> Option<&'tcx [rustc_hir::Attribute]> {
    match def_id.as_local() {
        Some(local) => owner_attrs(owners, local),
        None => Some(tcx.attrs_for_def(def_id)),
    }
}

/// The function that the local item `parent` declares under `name`, read from the
/// owners this pass was handed: `module_children` and `associated_items` would
/// re-enter the `hir_crate` query that this pass is part of.
fn local_child_fn<'tcx>(
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    parent: LocalDefId,
    name: Symbol,
) -> Option<LocalDefId> {
    let MaybeOwner::Owner(owner) = owners.get(parent)? else {
        return None;
    };
    let children: Vec<LocalDefId> = match owner.node() {
        OwnerNode::Crate(module) => module.item_ids.iter().map(|id| id.owner_id.def_id).collect(),
        OwnerNode::Item(item) => match &item.kind {
            rustc_hir::ItemKind::Mod(_, module) => {
                module.item_ids.iter().map(|id| id.owner_id.def_id).collect()
            }
            rustc_hir::ItemKind::Impl(impl_) => {
                impl_.items.iter().map(|id| id.owner_id.def_id).collect()
            }
            rustc_hir::ItemKind::Trait { items, .. } => {
                items.iter().map(|id| id.owner_id.def_id).collect()
            }
            _ => return None,
        },
        _ => return None,
    };
    children.into_iter().find(|child| local_fn_name(owners, *child) == Some(name))
}

/// The name of a local function item, or `None` if the item is not a function.
fn local_fn_name<'tcx>(
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    def_id: LocalDefId,
) -> Option<Symbol> {
    let MaybeOwner::Owner(owner) = owners.get(def_id)? else {
        return None;
    };
    match owner.node() {
        OwnerNode::Item(item) => match &item.kind {
            rustc_hir::ItemKind::Fn { ident, .. } => Some(ident.name),
            _ => None,
        },
        OwnerNode::ImplItem(item) => match &item.kind {
            rustc_hir::ImplItemKind::Fn(..) => Some(item.ident.name),
            _ => None,
        },
        OwnerNode::TraitItem(item) => match &item.kind {
            rustc_hir::TraitItemKind::Fn(..) => Some(item.ident.name),
            _ => None,
        },
        _ => None,
    }
}

impl<'a, 'tcx> Ctxt<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        owners: &'a IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    ) -> Ctxt<'a, 'tcx> {
        let (companions_by_method, trait_supers) = local_maps(tcx, owners);
        let external_targets = external_target_map(tcx, owners);
        Ctxt { tcx, owners, external_targets, companions_by_method, trait_supers }
    }
}

/// Index what the rewrite needs to know about the items of this crate: the
/// functions, their attributes, the companion traits and the supertraits of
/// every trait.
fn local_maps<'tcx>(
    tcx: TyCtxt<'tcx>,
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
) -> (HashMap<Symbol, Vec<DefId>>, HashMap<DefId, Vec<DefId>>) {
    let mut companion_traits: HashSet<LocalDefId> = HashSet::new();
    let mut trait_supers: HashMap<DefId, Vec<DefId>> = HashMap::new();
    let mut companion_methods: Vec<(Symbol, LocalDefId)> = Vec::new();
    for (def_id, owner) in owners.iter_enumerated() {
        let MaybeOwner::Owner(owner) = owner else {
            continue;
        };
        if let OwnerNode::Item(item) = owner.node()
            && let rustc_hir::ItemKind::Trait { bounds, .. } = &item.kind
        {
            if is_companion_trait(owner.attrs.get(ItemLocalId::ZERO)) {
                companion_traits.insert(def_id);
            }
            trait_supers.insert(def_id.to_def_id(), bound_trait_ids(bounds));
            continue;
        }
        let OwnerNode::TraitItem(item) = owner.node() else {
            continue;
        };
        let rustc_hir::TraitItemKind::Fn(..) = &item.kind else {
            continue;
        };
        if item.ident.name.as_str().starts_with(VERIFIED_PREFIX)
            && let Some(parent) = tcx.opt_local_parent(def_id)
        {
            companion_methods.push((item.ident.name, parent));
        }
    }
    let mut companions_by_method: HashMap<Symbol, Vec<DefId>> = HashMap::new();
    for (name, parent) in companion_methods {
        if companion_traits.contains(&parent) {
            companions_by_method.entry(name).or_default().push(parent.to_def_id());
        }
    }
    external_companion_traits(tcx, &mut companions_by_method, &mut trait_supers);
    (companions_by_method, trait_supers)
}

/// The supertraits a trait of another crate declares.
fn foreign_supertraits<'tcx>(tcx: TyCtxt<'tcx>, trait_def_id: DefId) -> Vec<DefId> {
    tcx.explicit_super_predicates_of(trait_def_id)
        .skip_binder()
        .iter()
        .filter_map(|(clause, _)| Some(clause.as_trait_clause()?.def_id()))
        .collect()
}

/// The traits named by a list of bounds.
fn bound_trait_ids(bounds: &[GenericBound<'_>]) -> Vec<DefId> {
    bounds
        .iter()
        .filter_map(|bound| match bound {
            GenericBound::Trait(poly) => poly.trait_ref.path.res.opt_def_id(),
            _ => None,
        })
        .collect()
}

/// Does one of these attributes mark a companion trait?
fn is_companion_trait(attrs: &[rustc_hir::Attribute]) -> bool {
    parse_attrs_opt(attrs, None).into_iter().any(|a| matches!(a, Attr::VerifiedTrait))
}

/// Index the companion traits declared by the crates this one depends on.
///
/// A companion trait is usually declared next to the `external_trait_specification`
/// of the trait it belongs to, which is commonly in another crate.
fn external_companion_traits<'tcx>(
    tcx: TyCtxt<'tcx>,
    companions_by_method: &mut HashMap<Symbol, Vec<DefId>>,
    trait_supers: &mut HashMap<DefId, Vec<DefId>>,
) {
    for cnum in tcx.crates(()) {
        for trait_def_id in tcx.traits(*cnum) {
            // A companion trait is always named with the reserved prefix, so the
            // cheap name check rules out the overwhelming majority of the
            // dependencies' traits before any attribute is decoded.
            if !tcx.item_name(*trait_def_id).as_str().starts_with(VERIFIED_PREFIX) {
                continue;
            }
            // Verus attributes are `Unparsed`, where `get_all_attrs` is
            // acceptable per its deprecation message.
            #[allow(deprecated)]
            let attrs = tcx.get_all_attrs(*trait_def_id);
            if !is_companion_trait(attrs) {
                continue;
            }
            for assoc in tcx.associated_items(*trait_def_id).in_definition_order() {
                let name = assoc.name();
                if name.as_str().starts_with(VERIFIED_PREFIX) {
                    companions_by_method.entry(name).or_default().push(*trait_def_id);
                }
            }
            trait_supers.insert(*trait_def_id, foreign_supertraits(tcx, *trait_def_id));
        }
    }
}

/// Index the verified counterparts declared for external functions.
///
/// An external function cannot carry a `verified_by` attribute, so the link is
/// written on the local `assume_specification` that specifies it. That item names
/// its target with the trailing call of its body, which name resolution has
/// already resolved to a `DefId` at this point -- unlike `get_external_def_id`,
/// which runs after type checking, this only supports a plain path callee.
fn external_target_map<'tcx>(
    tcx: TyCtxt<'tcx>,
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
) -> HashMap<DefId, DefId> {
    let mut map = HashMap::new();
    for (def_id, owner) in owners.iter_enumerated() {
        let MaybeOwner::Owner(owner) = owner else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let rustc_hir::ItemKind::Fn { body, .. } = &item.kind else {
            continue;
        };
        let attrs = owner.attrs.get(ItemLocalId::ZERO);
        let (mut is_external_fn_spec, mut is_stub) = (false, false);
        for attr in parse_attrs_opt(attrs, None) {
            match attr {
                Attr::ExternalFnSpecification => is_external_fn_spec = true,
                Attr::UnverifiedStub => is_stub = true,
                _ => {}
            }
        }
        if !is_external_fn_spec || !is_stub {
            continue;
        }
        let Some(body) = owner.nodes.bodies.get(&body.hir_id.local_id) else {
            continue;
        };
        let Some(target) = tail_call_target(body.value) else {
            continue;
        };
        if let Some(verified) = counterpart_of(tcx, owners, def_id.to_def_id()) {
            map.insert(target, verified);
        }
    }
    map
}

/// The `DefId` called by the trailing expression of an `assume_specification` body.
fn tail_call_target(mut expr: &Expr<'_>) -> Option<DefId> {
    loop {
        match &expr.kind {
            ExprKind::Block(block, _) => expr = block.expr?,
            ExprKind::Call(callee, _) => {
                let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind else {
                    return None;
                };
                return path.res.opt_def_id();
            }
            _ => {
                return None;
            }
        }
    }
}

impl<'tcx> Ctxt<'_, 'tcx> {
    /// Attributes of `def_id`.
    ///
    /// Note: for local items we must not go through tcx.hir_attrs, which would
    /// re-enter the hir_crate query we are computing.
    fn attrs(&self, def_id: DefId) -> Option<&'tcx [rustc_hir::Attribute]> {
        def_attrs(self.tcx, self.owners, def_id)
    }

    /// Is `callee` a call to the `proof_with`/`proof_with_ret` marker of the builtin
    /// crate?
    ///
    /// The verus items map is not available this early, and `is_diagnostic_item` for an
    /// item of the current crate makes rustc hang (see hir_hide_reveal_rewrite), so read
    /// the `rustc_diagnostic_item` attribute directly. This also identifies the builtin
    /// when it is embedded as a module rather than a crate.
    fn is_proof_with_marker(&self, callee: &Expr<'tcx>) -> bool {
        let ExprKind::Path(QPath::Resolved(None, path)) = &callee.kind else {
            return false;
        };
        let Res::Def(DefKind::Fn, def_id) = path.res else {
            return false;
        };
        let Some(attrs) = self.attrs(def_id) else {
            return false;
        };
        attrs.iter().any(|attr| match attr {
            rustc_hir::Attribute::Parsed(rustc_hir::attrs::AttributeKind::RustcDiagnosticItem(
                name,
            )) => {
                name.as_str() == "verus::verus_builtin::proof_with"
                    || name.as_str() == "verus::verus_builtin::proof_with_ret"
            }
            _ => false,
        })
    }

    /// Is `def_id` the unverified stub of a function declared with `with ..`, and is
    /// it the unerased proxy of a `const fn`?
    fn stub_kind(&self, def_id: DefId) -> (bool, bool) {
        let Some(attrs) = self.attrs(def_id) else {
            return (false, false);
        };
        let (mut is_stub, mut is_proxy) = (false, false);
        for attr in parse_attrs_opt(attrs, None) {
            match attr {
                Attr::UnverifiedStub => is_stub = true,
                Attr::UnerasedProxy => is_proxy = true,
                _ => {}
            }
        }
        (is_stub, is_proxy)
    }

    /// Resolve the verified counterpart of a resolved callee.
    fn verified_counterpart(&self, def_id: DefId) -> Option<DefId> {
        let (is_stub, _) = self.stub_kind(def_id);
        let name = counterpart_name(self.tcx, self.owners, def_id);
        if !is_stub {
            // The callee is not a stub itself: it may be an external function
            // specified by a local `assume_specification`, or a method of an
            // external trait, specified by a proxy.
            if let Some(found) = self.external_targets.get(&def_id) {
                return Some(*found);
            }
            let parent = self.tcx.opt_parent(def_id)?;
            return self.companion_method(parent, name);
        }
        counterpart_of(self.tcx, self.owners, def_id)
            .or_else(|| self.companion_method(self.tcx.opt_parent(def_id)?, name))
    }

    /// The counterpart of a trait method, which the companion trait of the trait
    /// declares.
    fn companion_method(&self, trait_def_id: DefId, name: Symbol) -> Option<DefId> {
        let companion = *self
            .companions_by_method
            .get(&name)?
            .iter()
            .find(|companion| self.supertraits(**companion).contains(&trait_def_id))?;
        match companion.as_local() {
            // A local companion is read from the owners; `associated_items` would
            // re-enter the `hir_crate` computation this pass is part of.
            Some(local) => local_child_fn(self.owners, local, name).map(LocalDefId::to_def_id),
            // A companion of a dependency crate, indexed by `external_companion_traits`,
            // is safe to look up through the query since its `DefId` is foreign.
            None => self
                .tcx
                .associated_items(companion)
                .filter_by_name_unhygienic(name)
                .next()
                .map(|assoc| assoc.def_id),
        }
    }

    /// The supertraits of a trait, which for a trait of this crate are read from
    /// its declaration: the query would re-enter the `hir_crate` computation
    /// this pass is part of.
    fn supertraits(&self, trait_def_id: DefId) -> Vec<DefId> {
        match self.trait_supers.get(&trait_def_id) {
            Some(supers) => supers.clone(),
            None if !trait_def_id.is_local() => foreign_supertraits(self.tcx, trait_def_id),
            None => Vec::new(),
        }
    }

    /// Do these bounds already give the trait that `companion` is the companion
    /// of, so that a bound on `companion` is what is missing?
    ///
    /// The trait may be reached through a supertrait: a caller written with
    /// `A: Y`, where `trait Y: X`, calls the methods of `X` too.
    fn bounds_reach(&self, bounds: &[DefId], companion: DefId) -> bool {
        let targets = self.supertraits(companion);
        let mut todo: Vec<DefId> = bounds.to_vec();
        let mut seen: HashSet<DefId> = HashSet::new();
        while let Some(bound) = todo.pop() {
            if targets.contains(&bound) {
                return true;
            }
            if seen.insert(bound) {
                todo.extend(self.supertraits(bound));
            }
        }
        false
    }
}

/// A bound `param: companion` that a rewritten call needs.
///
/// A companion trait declares the verified counterparts of the methods of the
/// trait it is a subtrait of, so a caller written with `A: Trait` that calls one
/// of them also needs `A: Companion`. Requiring that bound to be spelled out
/// would leak the companion trait into the source, so it is added here instead.
/// The caller still has to prove it, which only a type whose implementation was
/// itself verified with `with` satisfies.
struct Injection {
    /// The type parameter the bound is added to.
    param: DefId,
    companion: DefId,
    /// Span of the bound that the call resolved through.
    span: rustc_span::Span,
}

fn rewrite_owner<'tcx>(
    ctxt: &Ctxt<'_, 'tcx>,
    inner_owner: &'tcx rustc_hir::OwnerInfo<'tcx>,
    def_id: LocalDefId,
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    injections: &mut HashMap<LocalDefId, Vec<Injection>>,
) -> Option<MaybeOwner<'tcx>> {
    let tcx = ctxt.tcx;
    let mut bodies = inner_owner.nodes.bodies.clone();
    let mut nodes = inner_owner.nodes.nodes.clone();
    let mut changed = false;
    let mut extra_traits: HashMap<ItemLocalId, Vec<DefId>> = HashMap::new();

    for (local_id, body) in inner_owner.nodes.bodies.iter() {
        let mut folder = Folder { ctxt, updates: Vec::new(), extra_traits: Vec::new() };
        let Some(value) = folder.fold_expr(body.value) else {
            continue;
        };
        for (id, node) in folder.updates.iter() {
            if let Some(parented) = nodes.get_mut(*id) {
                parented.node = *node;
            }
        }
        for (id, traits) in folder.extra_traits.iter() {
            extra_traits.entry(*id).or_default().extend(traits.iter().copied());
        }
        let body = tcx.hir_arena.alloc(rustc_hir::Body { params: body.params, value });
        bodies[local_id] = body;
        changed = true;
    }
    if !changed {
        return None;
    }
    collect_injections(ctxt, def_id, owners, &extra_traits, injections);

    let nodes = rustc_hir::OwnerNodes {
        opt_hash_including_bodies: inner_owner.nodes.opt_hash_including_bodies,
        nodes,
        bodies,
    };
    let mut trait_map = clone_trait_map(tcx, inner_owner);
    for (id, extra) in extra_traits.iter() {
        let mut candidates = trait_map.get(id).map(|c| c.to_vec()).unwrap_or_default();
        // Reuse the imports recorded for the call, so that a `use` of the trait
        // is not reported as unused when the method is found through the
        // companion trait.
        let import_ids: &'tcx [LocalDefId] =
            candidates.first().map(|c| c.import_ids).unwrap_or(&[]);
        for def_id in extra {
            if candidates.iter().any(|c| c.def_id == *def_id) {
                continue;
            }
            candidates.push(rustc_hir::TraitCandidate {
                def_id: *def_id,
                import_ids,
                lint_ambiguous: false,
            });
        }
        trait_map.insert(*id, tcx.hir_arena.alloc_slice(&candidates));
    }
    let owner_info = mk_owner(tcx, inner_owner, nodes, trait_map);
    Some(MaybeOwner::Owner(owner_info))
}

/// Which type parameters need a bound on one of the companion traits the calls
/// in this owner were redirected to.
///
/// Type checking has not run yet, so the receiver of a rewritten call is not
/// known: the bound is added to every type parameter in scope that is bounded
/// by the trait the companion belongs to. A parameter that is not the receiver
/// picks up a bound it does not need, which only makes the signature more
/// demanding, never less.
fn collect_injections<'tcx>(
    ctxt: &Ctxt<'_, 'tcx>,
    def_id: LocalDefId,
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    extra_traits: &HashMap<ItemLocalId, Vec<DefId>>,
    injections: &mut HashMap<LocalDefId, Vec<Injection>>,
) {
    let tcx = ctxt.tcx;
    let companions: HashSet<DefId> = extra_traits.values().flatten().copied().collect();
    if companions.is_empty() {
        return;
    }

    // The parameter may be declared by the function itself or by the impl or
    // trait that contains it.
    let mut scopes: Vec<&'tcx Generics<'tcx>> = Vec::new();
    let mut add_scope = |owner: &MaybeOwner<'tcx>| {
        if let MaybeOwner::Owner(owner) = owner {
            scopes.extend(owner.node().generics());
        }
    };
    add_scope(&owners[def_id]);
    if let Some(parent) = tcx.opt_local_parent(def_id) {
        if let Some(parent) = owners.get(parent) {
            add_scope(parent);
        }
    }

    for generics in scopes {
        for predicate in generics.predicates {
            let WherePredicateKind::BoundPredicate(bound) = predicate.kind else {
                continue;
            };
            // Only a type parameter, which `Self` is not: a `where Self: T`
            // clause is bounded by the trait that declares `Self`, which cannot
            // be given a further bound here.
            let Some(param) = type_param_of(bound.bounded_ty) else {
                continue;
            };
            let bounded_by = bound_trait_ids(bound.bounds);
            for companion in companions.iter() {
                if bounded_by.contains(companion) {
                    // Already spelled out in the source.
                    continue;
                }
                if !ctxt.bounds_reach(&bounded_by, *companion) {
                    continue;
                }
                let Some(owner) = param.as_local().and_then(|p| tcx.opt_local_parent(p)) else {
                    continue;
                };
                let entry = injections.entry(owner).or_default();
                if entry.iter().any(|i| i.param == param && i.companion == *companion) {
                    continue;
                }
                entry.push(Injection { param, companion: *companion, span: predicate.span });
            }
        }
    }
}

/// The type parameter a type refers to, if it is one.
fn type_param_of<'tcx>(ty: &'tcx Ty<'tcx>) -> Option<DefId> {
    let TyKind::Path(QPath::Resolved(None, path)) = ty.kind else {
        return None;
    };
    match path.res {
        Res::Def(DefKind::TyParam, param) => Some(param),
        _ => None,
    }
}

/// Adds the bounds collected by `collect_injections` to the generics of an owner.
///
/// Each bound needs five new HIR nodes, whose ids are appended to the ones of
/// the owner. They stay dense, as the validator in `rustc_passes` requires,
/// because each of them is reachable from the generics of the owner.
fn inject_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    inner_owner: &'tcx rustc_hir::OwnerInfo<'tcx>,
    injections: &[Injection],
) -> Option<MaybeOwner<'tcx>> {
    let mut nodes = inner_owner.nodes.nodes.clone();
    // An owner without generics cannot take a bound, and `def_id` is only
    // meaningful for the items that can.
    inner_owner.nodes.node().generics()?;
    let owner_id = inner_owner.nodes.node().def_id();

    let mut predicates: Vec<WherePredicate<'tcx>> = Vec::new();
    for injection in injections {
        let Injection { param, companion, span } = injection;
        let base = nodes.next_index().as_u32();
        let id = |offset: u32| rustc_hir::HirId {
            owner: owner_id,
            local_id: ItemLocalId::from_u32(base + offset),
        };
        let (predicate_id, ty_id, param_segment_id, trait_ref_id, trait_segment_id) =
            (id(0), id(1), id(2), id(3), id(4));

        let mk_path = |hir_id: rustc_hir::HirId, res: Res| {
            let name = tcx.item_name(res.def_id());
            let segment = tcx.hir_arena.alloc(PathSegment {
                ident: rustc_span::symbol::Ident::new(name, *span),
                hir_id,
                res,
                args: None,
                infer_args: false,
            });
            let path = tcx.hir_arena.alloc(rustc_hir::Path {
                span: *span,
                res,
                segments: std::slice::from_ref(segment),
            });
            (&*segment, &*path)
        };

        let (param_segment, param_path) =
            mk_path(param_segment_id, Res::Def(DefKind::TyParam, *param));
        let bounded_ty = tcx.hir_arena.alloc(Ty {
            hir_id: ty_id,
            span: *span,
            kind: TyKind::Path(QPath::Resolved(None, param_path)),
        });
        let (trait_segment, trait_path) =
            mk_path(trait_segment_id, Res::Def(DefKind::Trait, *companion));
        let trait_ref =
            tcx.hir_arena.alloc(TraitRef { path: trait_path, hir_ref_id: trait_ref_id });
        let bounds = tcx.hir_arena.alloc_slice(&[GenericBound::Trait(PolyTraitRef {
            bound_generic_params: &[],
            modifiers: rustc_hir::TraitBoundModifiers::NONE,
            trait_ref: *trait_ref,
            span: *span,
        })]);
        let kind = tcx.hir_arena.alloc(WherePredicateKind::BoundPredicate(WhereBoundPredicate {
            origin: rustc_hir::PredicateOrigin::WhereClause,
            bound_generic_params: &[],
            bounded_ty,
            bounds,
        }));
        let predicate =
            tcx.hir_arena.alloc(WherePredicate { hir_id: predicate_id, span: *span, kind });

        let parented =
            |parent: rustc_hir::HirId, node| ParentedNode { parent: parent.local_id, node };
        nodes.push(parented(
            rustc_hir::HirId { owner: owner_id, local_id: ItemLocalId::ZERO },
            Node::WherePredicate(predicate),
        ));
        nodes.push(parented(predicate_id, Node::Ty(bounded_ty)));
        nodes.push(parented(ty_id, Node::PathSegment(param_segment)));
        nodes.push(parented(predicate_id, Node::TraitRef(trait_ref)));
        nodes.push(parented(trait_ref_id, Node::PathSegment(trait_segment)));
        predicates.push(*predicate);
    }
    if predicates.is_empty() {
        return None;
    }

    let node = with_generics(tcx, inner_owner.nodes.node(), |generics| {
        let mut all = generics.predicates.to_vec();
        all.extend(predicates.iter().copied());
        tcx.hir_arena.alloc(Generics {
            params: generics.params,
            predicates: tcx.hir_arena.alloc_slice(&all),
            has_where_clause_predicates: true,
            where_clause_span: generics.where_clause_span,
            span: generics.span,
        })
    })?;
    nodes[ItemLocalId::ZERO].node = node.into();

    let owner_nodes = rustc_hir::OwnerNodes {
        opt_hash_including_bodies: inner_owner.nodes.opt_hash_including_bodies,
        nodes,
        bodies: inner_owner.nodes.bodies.clone(),
    };
    let trait_map = clone_trait_map(tcx, inner_owner);
    Some(MaybeOwner::Owner(mk_owner(tcx, inner_owner, owner_nodes, trait_map)))
}

/// Copy the trait candidates of an owner into the arena of the new crate.
fn clone_trait_map<'tcx>(
    tcx: TyCtxt<'tcx>,
    inner_owner: &'tcx rustc_hir::OwnerInfo<'tcx>,
) -> rustc_hir::ItemLocalMap<&'tcx [rustc_hir::TraitCandidate<'tcx>]> {
    inner_owner
        .trait_map
        .items()
        .map(|(&id, candidates)| {
            let candidates: &'tcx [rustc_hir::TraitCandidate<'tcx>] =
                tcx.hir_arena.alloc_slice(&candidates.to_vec());
            (id, candidates)
        })
        .collect()
}

/// Rebuild an owner with new nodes and trait candidates. `OwnerInfo` is neither
/// `Clone` nor `Copy`, since `delayed_lints` is a `Steal`, so every field has to
/// be listed; the lints of the original owner have already been emitted.
fn mk_owner<'tcx>(
    tcx: TyCtxt<'tcx>,
    inner_owner: &'tcx rustc_hir::OwnerInfo<'tcx>,
    nodes: rustc_hir::OwnerNodes<'tcx>,
    trait_map: rustc_hir::ItemLocalMap<&'tcx [rustc_hir::TraitCandidate<'tcx>]>,
) -> &'tcx rustc_hir::OwnerInfo<'tcx> {
    tcx.hir_arena.alloc(rustc_hir::OwnerInfo {
        nodes,
        parenting: inner_owner.parenting.clone(),
        attrs: rustc_hir::AttributeMap {
            map: inner_owner.attrs.map.clone(),
            opt_hash: inner_owner.attrs.opt_hash,
            define_opaque: inner_owner.attrs.define_opaque,
        },
        trait_map,
        delayed_lints: Steal::new(Vec::new().into_boxed_slice()),
    })
}

/// Rebuilds an owner node with the generics returned by `f`.
fn with_generics<'tcx>(
    tcx: TyCtxt<'tcx>,
    node: OwnerNode<'tcx>,
    f: impl FnOnce(&'tcx Generics<'tcx>) -> &'tcx Generics<'tcx>,
) -> Option<OwnerNode<'tcx>> {
    match node {
        OwnerNode::Item(item) => {
            let mut item = *item;
            match &mut item.kind {
                rustc_hir::ItemKind::Fn { generics, .. } => *generics = f(*generics),
                rustc_hir::ItemKind::Impl(impl_) => impl_.generics = f(impl_.generics),
                rustc_hir::ItemKind::Trait { generics, .. } => *generics = f(*generics),
                _ => return None,
            }
            Some(OwnerNode::Item(tcx.hir_arena.alloc(item)))
        }
        OwnerNode::ImplItem(item) => {
            let mut item = *item;
            item.generics = f(item.generics);
            Some(OwnerNode::ImplItem(tcx.hir_arena.alloc(item)))
        }
        OwnerNode::TraitItem(item) => {
            let mut item = *item;
            item.generics = f(item.generics);
            Some(OwnerNode::TraitItem(tcx.hir_arena.alloc(item)))
        }
        _ => None,
    }
}

/// Rebuilds the spine from the body root down to each rewritten call. HIR is
/// immutable arena data and type checking walks the expression tree through the
/// child pointers of each node, so every ancestor of a replaced expression has to
/// be reallocated with the new child. Hir ids and spans are preserved.
struct Folder<'a, 'tcx> {
    ctxt: &'a Ctxt<'a, 'tcx>,
    updates: Vec<(ItemLocalId, Node<'tcx>)>,
    /// Trait candidates to add for a rewritten call, see `Ctxt::companions_by_method`.
    extra_traits: Vec<(ItemLocalId, &'a [DefId])>,
}

impl<'a, 'tcx> Folder<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctxt.tcx
    }

    fn mk_expr(&mut self, old: &'tcx Expr<'tcx>, kind: ExprKind<'tcx>) -> &'tcx Expr<'tcx> {
        let new: &'tcx Expr<'tcx> =
            self.tcx().hir_arena.alloc(Expr { hir_id: old.hir_id, kind, span: old.span });
        self.updates.push((old.hir_id.local_id, Node::Expr(new)));
        new
    }

    fn alloc_exprs(&self, exprs: Vec<Expr<'tcx>>) -> &'tcx [Expr<'tcx>] {
        self.tcx().hir_arena.alloc_slice(&exprs)
    }

    /// Returns `Some(new)` if anything inside `expr` was rewritten.
    fn fold_expr(&mut self, expr: &'tcx Expr<'tcx>) -> Option<&'tcx Expr<'tcx>> {
        if let Some(new) = self.try_rewrite_proof_with(expr) {
            return Some(new);
        }
        let kind = match &expr.kind {
            ExprKind::Array(elems) => ExprKind::Array(self.fold_exprs(elems)?),
            ExprKind::Tup(elems) => ExprKind::Tup(self.fold_exprs(elems)?),
            ExprKind::Call(callee, args) => {
                let new_callee = self.fold_expr(callee);
                let new_args = self.fold_exprs(args);
                if new_callee.is_none() && new_args.is_none() {
                    return None;
                }
                ExprKind::Call(new_callee.unwrap_or(callee), new_args.unwrap_or(args))
            }
            ExprKind::MethodCall(seg, receiver, args, span) => {
                let new_receiver = self.fold_expr(receiver);
                let new_args = self.fold_exprs(args);
                if new_receiver.is_none() && new_args.is_none() {
                    return None;
                }
                ExprKind::MethodCall(
                    seg,
                    new_receiver.unwrap_or(receiver),
                    new_args.unwrap_or(args),
                    *span,
                )
            }
            ExprKind::Use(e, span) => ExprKind::Use(self.fold_expr(e)?, *span),
            ExprKind::Binary(op, lhs, rhs) => {
                let new_lhs = self.fold_expr(lhs);
                let new_rhs = self.fold_expr(rhs);
                if new_lhs.is_none() && new_rhs.is_none() {
                    return None;
                }
                ExprKind::Binary(*op, new_lhs.unwrap_or(lhs), new_rhs.unwrap_or(rhs))
            }
            ExprKind::Unary(op, e) => ExprKind::Unary(*op, self.fold_expr(e)?),
            ExprKind::Cast(e, ty) => ExprKind::Cast(self.fold_expr(e)?, ty),
            ExprKind::Type(e, ty) => ExprKind::Type(self.fold_expr(e)?, ty),
            ExprKind::DropTemps(e) => ExprKind::DropTemps(self.fold_expr(e)?),
            ExprKind::Let(let_expr) => {
                let init = self.fold_expr(let_expr.init)?;
                ExprKind::Let(self.tcx().hir_arena.alloc(LetExpr { init, ..**let_expr }))
            }
            ExprKind::If(cond, then, els) => {
                let new_cond = self.fold_expr(cond);
                let new_then = self.fold_expr(then);
                let new_els = els.and_then(|e| self.fold_expr(e));
                if new_cond.is_none() && new_then.is_none() && new_els.is_none() {
                    return None;
                }
                ExprKind::If(new_cond.unwrap_or(cond), new_then.unwrap_or(then), new_els.or(*els))
            }
            ExprKind::Loop(block, label, source, span) => {
                ExprKind::Loop(self.fold_block(block)?, *label, *source, *span)
            }
            ExprKind::Match(scrutinee, arms, source) => {
                let new_scrutinee = self.fold_expr(scrutinee);
                let new_arms = self.fold_arms(arms);
                if new_scrutinee.is_none() && new_arms.is_none() {
                    return None;
                }
                ExprKind::Match(
                    new_scrutinee.unwrap_or(scrutinee),
                    new_arms.unwrap_or(arms),
                    *source,
                )
            }
            ExprKind::Block(block, label) => ExprKind::Block(self.fold_block(block)?, *label),
            ExprKind::Assign(lhs, rhs, span) => {
                let new_lhs = self.fold_expr(lhs);
                let new_rhs = self.fold_expr(rhs);
                if new_lhs.is_none() && new_rhs.is_none() {
                    return None;
                }
                ExprKind::Assign(new_lhs.unwrap_or(lhs), new_rhs.unwrap_or(rhs), *span)
            }
            ExprKind::AssignOp(op, lhs, rhs) => {
                let new_lhs = self.fold_expr(lhs);
                let new_rhs = self.fold_expr(rhs);
                if new_lhs.is_none() && new_rhs.is_none() {
                    return None;
                }
                ExprKind::AssignOp(*op, new_lhs.unwrap_or(lhs), new_rhs.unwrap_or(rhs))
            }
            ExprKind::Field(e, ident) => ExprKind::Field(self.fold_expr(e)?, *ident),
            ExprKind::Index(base, idx, span) => {
                let new_base = self.fold_expr(base);
                let new_idx = self.fold_expr(idx);
                if new_base.is_none() && new_idx.is_none() {
                    return None;
                }
                ExprKind::Index(new_base.unwrap_or(base), new_idx.unwrap_or(idx), *span)
            }
            ExprKind::AddrOf(kind, m, e) => ExprKind::AddrOf(*kind, *m, self.fold_expr(e)?),
            ExprKind::Break(dest, e) => ExprKind::Break(*dest, Some(self.fold_expr((*e)?)?)),
            ExprKind::Ret(e) => ExprKind::Ret(Some(self.fold_expr((*e)?)?)),
            ExprKind::Become(e) => ExprKind::Become(self.fold_expr(e)?),
            ExprKind::Struct(qpath, fields, tail) => {
                ExprKind::Struct(qpath, self.fold_fields(fields)?, *tail)
            }
            ExprKind::Repeat(e, count) => ExprKind::Repeat(self.fold_expr(e)?, count),
            ExprKind::Yield(e, source) => ExprKind::Yield(self.fold_expr(e)?, *source),
            ExprKind::UnsafeBinderCast(kind, e, ty) => {
                ExprKind::UnsafeBinderCast(*kind, self.fold_expr(e)?, *ty)
            }
            // Closures and const blocks are separate owners and are visited on
            // their own; the remaining variants have no sub-expressions.
            ExprKind::ConstBlock(..)
            | ExprKind::Closure(..)
            | ExprKind::Lit(..)
            | ExprKind::Path(..)
            | ExprKind::Continue(..)
            | ExprKind::InlineAsm(..)
            | ExprKind::OffsetOf(..)
            | ExprKind::Err(..) => return None,
        };
        Some(self.mk_expr(expr, kind))
    }

    fn fold_exprs(&mut self, exprs: &'tcx [Expr<'tcx>]) -> Option<&'tcx [Expr<'tcx>]> {
        let mut new: Option<Vec<Expr<'tcx>>> = None;
        for (i, e) in exprs.iter().enumerate() {
            if let Some(folded) = self.fold_expr(e) {
                new.get_or_insert_with(|| exprs.to_vec())[i] = *folded;
            }
        }
        new.map(|v| self.alloc_exprs(v))
    }

    fn fold_fields(&mut self, fields: &'tcx [ExprField<'tcx>]) -> Option<&'tcx [ExprField<'tcx>]> {
        let mut new: Option<Vec<ExprField<'tcx>>> = None;
        for (i, f) in fields.iter().enumerate() {
            if let Some(folded) = self.fold_expr(f.expr) {
                new.get_or_insert_with(|| fields.to_vec())[i].expr = folded;
            }
        }
        new.map(|v| &*self.tcx().hir_arena.alloc_slice(&v))
    }

    fn fold_arms(&mut self, arms: &'tcx [Arm<'tcx>]) -> Option<&'tcx [Arm<'tcx>]> {
        let mut new: Option<Vec<Arm<'tcx>>> = None;
        for (i, arm) in arms.iter().enumerate() {
            if let Some(folded) = self.fold_expr(arm.body) {
                new.get_or_insert_with(|| arms.to_vec())[i].body = folded;
            }
        }
        new.map(|v| &*self.tcx().hir_arena.alloc_slice(&v))
    }

    fn fold_block(&mut self, block: &'tcx Block<'tcx>) -> Option<&'tcx Block<'tcx>> {
        let mut new_stmts: Option<Vec<Stmt<'tcx>>> = None;
        for (i, stmt) in block.stmts.iter().enumerate() {
            if let Some(folded) = self.fold_stmt(stmt) {
                new_stmts.get_or_insert_with(|| block.stmts.to_vec())[i] = folded;
            }
        }
        let new_expr = block.expr.and_then(|e| self.fold_expr(e));
        if new_stmts.is_none() && new_expr.is_none() {
            return None;
        }
        let stmts = match new_stmts {
            Some(v) => self.tcx().hir_arena.alloc_slice(&v),
            None => block.stmts,
        };
        let new: &'tcx Block<'tcx> =
            self.tcx().hir_arena.alloc(Block { stmts, expr: new_expr.or(block.expr), ..*block });
        self.updates.push((block.hir_id.local_id, Node::Block(new)));
        Some(new)
    }

    fn fold_stmt(&mut self, stmt: &'tcx Stmt<'tcx>) -> Option<Stmt<'tcx>> {
        let kind = match &stmt.kind {
            StmtKind::Let(let_stmt) => {
                let init = let_stmt.init.and_then(|e| self.fold_expr(e));
                let els = let_stmt.els.and_then(|b| self.fold_block(b));
                if init.is_none() && els.is_none() {
                    return None;
                }
                let new = self.tcx().hir_arena.alloc(rustc_hir::LetStmt {
                    init: init.or(let_stmt.init),
                    els: els.or(let_stmt.els),
                    ..**let_stmt
                });
                StmtKind::Let(new)
            }
            StmtKind::Expr(e) => StmtKind::Expr(self.fold_expr(e)?),
            StmtKind::Semi(e) => StmtKind::Semi(self.fold_expr(e)?),
            StmtKind::Item(_) => return None,
        };
        let new = Stmt { kind, ..*stmt };
        self.updates.push((stmt.hir_id.local_id, Node::Stmt(self.tcx().hir_arena.alloc(new))));
        Some(new)
    }

    /// If `expr` is `proof_with((extra, ..), callee(args))`, produce the call to the
    /// verified counterpart of `callee` with the extra arguments appended.
    fn try_rewrite_proof_with(&mut self, expr: &'tcx Expr<'tcx>) -> Option<&'tcx Expr<'tcx>> {
        let ExprKind::Call(marker, marker_args) = &expr.kind else {
            return None;
        };
        // If the callee is not a valid `proof_with`, skip the rewrite.
        if marker_args.len() != 2 || !self.ctxt.is_proof_with_marker(marker) {
            return None;
        }

        let raw_extra_args: &'tcx [Expr<'tcx>] = match &marker_args[0].kind {
            ExprKind::Tup(elems) => elems,
            _ => std::slice::from_ref(&marker_args[0]),
        };
        // Rewrite anything nested inside the arguments and the call first.
        let extra_args: Vec<Expr<'tcx>> = raw_extra_args
            .iter()
            .map(|e| match self.fold_expr(e) {
                Some(folded) => *folded,
                None => *e,
            })
            .collect();
        let call = &marker_args[1];
        let call = self.fold_expr(call).unwrap_or(call);

        let new_kind = match &call.kind {
            ExprKind::Call(callee, args) => {
                let mut new_args = args.to_vec();
                new_args.extend(extra_args);
                let verified_callee = self.redirect_callee(callee)?;
                ExprKind::Call(verified_callee, self.alloc_exprs(new_args))
            }
            ExprKind::MethodCall(seg, receiver, args, span) => {
                let mut new_args = args.to_vec();
                new_args.extend(extra_args);
                let new_seg = self.rename_segment(seg)?;
                self.record_companion_traits(call.hir_id.local_id, new_seg.ident.name);
                ExprKind::MethodCall(new_seg, receiver, self.alloc_exprs(new_args), *span)
            }
            _ => {
                self.tcx().dcx().span_warn(
                    call.span,
                    "`with` ghost inputs/outputs can only be applied to a function call",
                );
                return None;
            }
        };
        // Reuse the call's hir id: the marker node disappears from the tree.
        Some(self.mk_expr(call, new_kind))
    }

    /// Point a resolved callee path at the verified counterpart of the callee.
    fn redirect_callee(&mut self, callee: &'tcx Expr<'tcx>) -> Option<&'tcx Expr<'tcx>> {
        let ExprKind::Path(qpath) = &callee.kind else {
            self.tcx()
                .dcx()
                .span_err(callee.span, "`with` ghost inputs/outputs: unsupported callee");
            return None;
        };
        let new_qpath = match qpath {
            QPath::Resolved(self_ty, path) => {
                let Res::Def(def_kind, def_id) = path.res else {
                    return None;
                };
                let Some(verified) = self.ctxt.verified_counterpart(def_id) else {
                    // Note: do not name the callee with `def_path_str` here, that reads
                    // the crate attributes and would re-enter the `hir_crate` query.
                    let name = path.segments.last().map(|s| s.ident.to_string());
                    let name = name.unwrap_or_else(|| "function".to_owned());
                    self.tcx().dcx().span_warn(
                        callee.span,
                        format!(
                            "`{name}` does not accept extra ghost/tracked arguments: \
                             it is not declared with `#[verus_spec(with ..)]`"
                        ),
                    );
                    return Some(callee);
                };
                QPath::Resolved(*self_ty, self.redirect_path(path, def_kind, verified)?)
            }
            // Resolved during type checking; renaming the segment is enough.
            QPath::TypeRelative(ty, seg) => {
                let new_seg = self.rename_segment(seg)?;
                self.record_companion_traits(callee.hir_id.local_id, new_seg.ident.name);
                QPath::TypeRelative(ty, new_seg)
            }
        };
        Some(self.mk_expr(callee, ExprKind::Path(new_qpath)))
    }

    /// Point a resolved path at the verified counterpart. The counterpart is not
    /// always named after the callee: an external function is specified by an
    /// `assume_specification` of another name, and the counterpart of a trait
    /// method is declared by the companion trait, which the segment naming the
    /// trait in a qualified call `Trait::f(..)` then has to name.
    fn redirect_path(
        &self,
        path: &'tcx rustc_hir::Path<'tcx>,
        def_kind: DefKind,
        verified: DefId,
    ) -> Option<&'tcx rustc_hir::Path<'tcx>> {
        let tcx = self.tcx();
        let rename = |seg: &PathSegment<'tcx>, res: Res| PathSegment {
            ident: rustc_span::symbol::Ident::new(tcx.item_name(res.def_id()), seg.ident.span),
            res,
            ..*seg
        };
        let res = Res::Def(def_kind, verified);
        let mut segments = path.segments.to_vec();
        let declares = tcx.opt_parent(verified);
        if let Some(companion) = declares
            && declares != tcx.opt_parent(path.res.def_id())
            && matches!(tcx.def_kind(companion), DefKind::Trait)
        {
            let i = segments.len().checked_sub(2)?;
            segments[i] = rename(&segments[i], Res::Def(DefKind::Trait, companion));
        }
        let last = *segments.last()?;
        *segments.last_mut()? = rename(&last, res);
        Some(tcx.hir_arena.alloc(rustc_hir::Path {
            span: path.span,
            res,
            segments: tcx.hir_arena.alloc_slice(&segments),
        }))
    }

    /// Remember that the companion traits declaring `name` have to be treated as
    /// in scope for the rewritten call.
    fn record_companion_traits(&mut self, id: ItemLocalId, name: Symbol) {
        if let Some(traits) = self.ctxt.companions_by_method.get(&name) {
            self.extra_traits.push((id, traits.as_slice()));
        }
    }

    fn rename_segment(
        &mut self,
        seg: &'tcx rustc_hir::PathSegment<'tcx>,
    ) -> Option<&'tcx rustc_hir::PathSegment<'tcx>> {
        let ident = rustc_span::symbol::Ident::new(verified_name(seg.ident.name), seg.ident.span);
        Some(self.tcx().hir_arena.alloc(rustc_hir::PathSegment { ident, ..*seg }))
    }
}

fn verified_name(name: Symbol) -> Symbol {
    Symbol::intern(&format!("{VERIFIED_PREFIX}_{name}"))
}

/// The verified counterpart of the unverified stub `def_id`: the function with the
/// counterpart name in the same module or impl.
fn counterpart_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    def_id: DefId,
) -> Option<DefId> {
    let name = counterpart_name(tcx, owners, def_id);
    let parent = tcx.opt_parent(def_id)?;
    if let Some(parent) = parent.as_local() {
        // The queries below would re-enter the `hir_crate` computation this pass
        // is part of, so a local counterpart is looked up in the owners instead.
        return local_child_fn(owners, parent, name).map(LocalDefId::to_def_id);
    }
    match tcx.def_kind(parent) {
        DefKind::Mod => tcx
            .module_children(parent)
            .iter()
            .find(|child| child.ident.name == name)
            .and_then(|child| child.res.opt_def_id()),
        DefKind::Impl { .. } | DefKind::Trait => tcx
            .associated_items(parent)
            .filter_by_name_unhygienic(name)
            .next()
            .map(|assoc| assoc.def_id),
        _ => None,
    }
}

/// The name of the verified counterpart of the unverified stub `def_id`. A `const fn`
/// is also split into an erased item and an unerased proxy, and both are stubs, but
/// the counterpart is named after the function the user wrote, without the prefix
/// the proxy carries.
fn counterpart_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    def_id: DefId,
) -> Symbol {
    let is_unerased_proxy = parse_attrs_opt(def_attrs(tcx, owners, def_id).unwrap_or(&[]), None)
        .iter()
        .any(|a| matches!(a, Attr::UnerasedProxy));
    let name = tcx.item_name(def_id);
    let name = name.as_str();
    let name = match is_unerased_proxy {
        true => name.strip_prefix(UNERASED_PROXY_PREFIX).unwrap_or(name),
        false => name,
    };
    verified_name(Symbol::intern(name))
}
