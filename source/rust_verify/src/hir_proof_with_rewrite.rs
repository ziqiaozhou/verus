//! Pre-typeck HIR pass that rewrites `proof_with(extras, f(args))` into
//! `_VERUS_WITH_f(args, extras)`, so rustc type-checks, borrow-checks and
//! region-checks the `with` clause extras as ordinary arguments.
//!
//! The rewrite has to run after name resolution — the callee may have been
//! brought into scope by a `use` inside a function body, which a macro cannot
//! see — and before type checking, which is what does the actual checking.

use crate::attributes::{Attr, parse_attrs_opt};
use rustc_data_structures::steal::Steal;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{
    Arm, Block, Expr, ExprField, ExprKind, ItemLocalId, LetExpr, MaybeOwner, Node, OwnerNode,
    PathSegment, QPath, Stmt, StmtKind, StructTailExpr,
};
use rustc_index::IndexVec;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;
use rustc_span::def_id::DefIndex;

const WITH_SHIM_PREFIX: &str = "_VERUS_WITH_";
const WITH_RET_SHIM_PREFIX: &str = "_VERUS_WITH_RET_";
/// The trait/impl conformance companion. Verus itself calls it, from the check it
/// plants in an impl method's body, so this pass leaves it alone; a call the user
/// wrote is rejected once the callee is resolved, in `fn_call_to_vir`.
const WITH_ARG_SHIM_PREFIX: &str = "_VERUS_WITH_ARG_";
/// A trait method's shims live on this sibling of the trait, blanket-implemented
/// for every implementor, rather than on the trait itself.
const WITH_SHIM_TRAIT_PREFIX: &str = "_VERUS_WITH_TR_";

fn shim_name(target: Symbol, with_outputs: bool) -> Symbol {
    let prefix = if with_outputs { WITH_RET_SHIM_PREFIX } else { WITH_SHIM_PREFIX };
    Symbol::intern(&format!("{prefix}{target}"))
}

fn shim_trait_name(trait_name: Symbol) -> Symbol {
    Symbol::intern(&format!("{WITH_SHIM_TRAIT_PREFIX}{trait_name}"))
}

fn is_with_shim_trait(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    debug_assert!(!def_id.is_local());
    crate::attributes::is_with_shim_trait(tcx.attrs_for_def(def_id))
}

pub(crate) fn hir_proof_with_rewrite<'tcx>(
    mut crate_: rustc_middle::hir::Crate<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> rustc_middle::hir::Crate<'tcx> {
    // With no delayed ids, `Crate::owner` reads the owners vector without entering
    // another query. See `hir_hide_reveal_rewrite`.
    let delayed_ids = std::mem::take(&mut crate_.delayed_ids);
    let mut new_owners: IndexVec<LocalDefId, MaybeOwner<'tcx>> = IndexVec::new();
    let num_defs = tcx.definitions_untracked().num_definitions();
    for i in 0..num_defs {
        let def_id = LocalDefId { local_def_index: DefIndex::from_usize(i) };
        let owner = new_owners.ensure_contains_elem(def_id, || MaybeOwner::Phantom);
        *owner = crate_.owner(tcx, def_id);
    }

    let owners = new_owners.clone();
    let ctxt = Ctxt { tcx, owners: &owners };

    for i in 0..new_owners.len() {
        let def_id = LocalDefId { local_def_index: DefIndex::from_usize(i) };
        let MaybeOwner::Owner(inner_owner) = new_owners[def_id] else {
            continue;
        };
        if let Some(owner) = rewrite_owner(&ctxt, inner_owner) {
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
    /// Local HIR must be read here because `tcx` would re-enter `hir_crate`.
    owners: &'a IndexVec<LocalDefId, MaybeOwner<'tcx>>,
}

fn owner_attrs<'tcx>(
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    def_id: LocalDefId,
) -> Option<&'tcx [rustc_hir::Attribute]> {
    let MaybeOwner::Owner(owner) = owners.get(def_id)? else {
        return None;
    };
    Some(owner.attrs.get(ItemLocalId::ZERO))
}

impl<'a, 'tcx> Ctxt<'a, 'tcx> {
    fn attrs(&self, def_id: DefId) -> &'tcx [rustc_hir::Attribute] {
        match def_id.as_local() {
            Some(local) => owner_attrs(self.owners, local).unwrap_or(&[]),
            None => self.tcx.attrs_for_def(def_id),
        }
    }

    fn is_with_shim(&self, def_id: DefId) -> bool {
        parse_attrs_opt(self.attrs(def_id), None).iter().any(|a| matches!(a, Attr::WithShim))
    }

    fn is_proof_with_marker(&self, callee: &Expr<'_>) -> Option<bool> {
        let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind else { return None };
        let Res::Def(DefKind::Fn, def_id) = path.res else { return None };
        let crate_name = self.tcx.crate_name(def_id.krate);
        if crate_name.as_str() != "builtin" && crate_name.as_str() != "verus_builtin" {
            return None;
        }
        match self.tcx.item_name(def_id).as_str() {
            "proof_with" => Some(false),
            "proof_with_ret" => Some(true),
            _ => None,
        }
    }

    /// The shim standing in for `callee_def_id`, named `_VERUS_WITH_<name>` (or
    /// `_VERUS_WITH_RET_<name>`): the sibling of the same parent, or, for a trait
    /// method, the method of the trait's shim trait.
    fn find_shim(&self, callee_def_id: DefId, with_outputs: bool) -> Option<DefId> {
        if !matches!(self.tcx.def_kind(callee_def_id), DefKind::Fn | DefKind::AssocFn) {
            return None;
        }
        let name = shim_name(self.tcx.item_name(callee_def_id), with_outputs);
        let parent = self.tcx.opt_parent(callee_def_id)?;
        let parent = match self.tcx.def_kind(parent) {
            DefKind::Trait => self.find_shim_trait(parent)?,
            _ => parent,
        };
        let shim = match parent.as_local() {
            // Local child queries would re-enter `hir_crate`.
            Some(local_parent) => local_child_fn(self.owners, local_parent, name)?.to_def_id(),
            None => match self.tcx.def_kind(parent) {
                DefKind::Trait | DefKind::Impl { .. } => self
                    .tcx
                    .associated_items(parent)
                    .filter_by_name_unhygienic(name)
                    .find(|assoc| matches!(assoc.kind, rustc_middle::ty::AssocKind::Fn { .. }))
                    .map(|assoc| assoc.def_id)?,
                _ => self
                    .tcx
                    .module_children(parent)
                    .iter()
                    .find(|child| child.ident.name == name)
                    .and_then(|child| child.res.opt_def_id())?,
            },
        };
        self.is_with_shim(shim).then_some(shim)
    }

    /// The shim trait generated beside `trait_def_id`, holding the shims of its
    /// methods. Absent when the trait declares no `with` clause at all.
    fn find_shim_trait(&self, trait_def_id: DefId) -> Option<DefId> {
        let name = shim_trait_name(self.tcx.item_name(trait_def_id));
        let module = self.tcx.opt_parent(trait_def_id)?;
        let shim_trait = match module.as_local() {
            Some(local_module) => local_child_trait(self.owners, local_module, name)?.to_def_id(),
            None => self
                .tcx
                .module_children(module)
                .iter()
                .find(|child| child.ident.name == name)
                .and_then(|child| child.res.opt_def_id())?,
        };
        let is_shim_trait = parse_attrs_opt(self.attrs(shim_trait), None)
            .iter()
            .any(|a| matches!(a, Attr::WithShimTrait));
        is_shim_trait.then_some(shim_trait)
    }
}

/// The shim standing in for a function in another crate. Unlike `Ctxt::find_shim`
/// this runs after the HIR pass, so it may use `tcx` freely; it is how a caller
/// recovers a foreign callee's extras, which are not in this crate's HIR.
pub(crate) fn find_extern_with_shim<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: DefId,
    with_outputs: bool,
) -> Option<DefId> {
    if callee_def_id.is_local() {
        return None;
    }
    if !matches!(tcx.def_kind(callee_def_id), DefKind::Fn | DefKind::AssocFn) {
        return None;
    }
    let name = shim_name(tcx.item_name(callee_def_id), with_outputs);
    let parent = tcx.opt_parent(callee_def_id)?;
    let parent = match tcx.def_kind(parent) {
        DefKind::Trait => find_extern_shim_trait(tcx, parent)?,
        _ => parent,
    };
    let shim = match tcx.def_kind(parent) {
        DefKind::Trait | DefKind::Impl { .. } => tcx
            .associated_items(parent)
            .filter_by_name_unhygienic(name)
            .find(|assoc| matches!(assoc.kind, rustc_middle::ty::AssocKind::Fn { .. }))
            .map(|assoc| assoc.def_id)?,
        _ => tcx
            .module_children(parent)
            .iter()
            .find(|child| child.ident.name == name)
            .and_then(|child| child.res.opt_def_id())?,
    };
    let is_shim =
        parse_attrs_opt(tcx.attrs_for_def(shim), None).iter().any(|a| matches!(a, Attr::WithShim));
    is_shim.then_some(shim)
}

/// The shim trait generated beside a foreign trait.
fn find_extern_shim_trait<'tcx>(tcx: TyCtxt<'tcx>, trait_def_id: DefId) -> Option<DefId> {
    let name = shim_trait_name(tcx.item_name(trait_def_id));
    let module = tcx.opt_parent(trait_def_id)?;
    let shim_trait = tcx
        .module_children(module)
        .iter()
        .find(|child| child.ident.name == name)
        .and_then(|child| child.res.opt_def_id())?;
    is_with_shim_trait(tcx, shim_trait).then_some(shim_trait)
}

/// Local children must bypass `module_children` and `associated_items`, which
/// re-enter `hir_crate`.
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

/// A local trait declared in `parent` (a module or the crate root).
fn local_child_trait<'tcx>(
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    parent: LocalDefId,
    name: Symbol,
) -> Option<LocalDefId> {
    let MaybeOwner::Owner(owner) = owners.get(parent)? else {
        return None;
    };
    let item_ids = match owner.node() {
        OwnerNode::Crate(module) => module.item_ids,
        OwnerNode::Item(item) => match &item.kind {
            rustc_hir::ItemKind::Mod(_, module) => module.item_ids,
            _ => return None,
        },
        _ => return None,
    };
    item_ids
        .iter()
        .map(|id| id.owner_id.def_id)
        .find(|child| local_trait_name(owners, *child) == Some(name))
}

fn local_trait_name<'tcx>(
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    def_id: LocalDefId,
) -> Option<Symbol> {
    let MaybeOwner::Owner(owner) = owners.get(def_id)? else {
        return None;
    };
    match owner.node() {
        OwnerNode::Item(item) => match &item.kind {
            rustc_hir::ItemKind::Trait { ident, .. } => Some(ident.name),
            _ => None,
        },
        _ => None,
    }
}

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

enum Reparent {
    To(ItemLocalId),
    /// The replacement call inherits the removed marker's parent during write-back.
    AdoptFrom(ItemLocalId),
}

fn rewrite_owner<'tcx>(
    ctxt: &Ctxt<'_, 'tcx>,
    inner_owner: &'tcx rustc_hir::OwnerInfo<'tcx>,
) -> Option<MaybeOwner<'tcx>> {
    let tcx = ctxt.tcx;
    // A `with` shim's own body is `unimplemented!()`, and its parameter list is
    // the only thing that matters; nothing in it needs rewriting.
    let mut bodies = inner_owner.nodes.bodies.clone();
    let mut nodes = inner_owner.nodes.nodes.clone();
    let mut changed = false;
    let mut extra_traits: Vec<(ItemLocalId, DefId)> = Vec::new();

    // Every body of the owner, which covers closures as well as the item itself.
    for (local_id, body) in inner_owner.nodes.bodies.iter() {
        let mut folder = Folder {
            ctxt,
            owner: inner_owner,
            updates: Vec::new(),
            reparents: Vec::new(),
            extra_traits: Vec::new(),
        };
        let Some(value) = folder.fold_expr(body.value) else {
            continue;
        };
        for (id, node) in folder.updates.iter() {
            if let Some(parented) = nodes.get_mut(*id) {
                parented.node = *node;
            }
        }
        // Reparenting prevents upward HIR walks from reaching the removed marker.
        // Abandoned entries are harmless because traversals start from body trees.
        for (id, reparent) in folder.reparents.iter() {
            let parent = match reparent {
                Reparent::To(parent) => Some(*parent),
                Reparent::AdoptFrom(other) => nodes.get(*other).map(|p| p.parent),
            };
            if let (Some(parent), Some(parented)) = (parent, nodes.get_mut(*id)) {
                parented.parent = parent;
            }
        }
        extra_traits.extend(folder.extra_traits.iter().copied());
        let body = tcx.hir_arena.alloc(rustc_hir::Body { params: body.params, value });
        bodies[local_id] = body;
        changed = true;
    }
    if !changed {
        return None;
    }

    let nodes = rustc_hir::OwnerNodes {
        opt_hash_including_bodies: inner_owner.nodes.opt_hash_including_bodies,
        nodes,
        bodies,
    };
    let mut trait_map: rustc_hir::ItemLocalMap<&'tcx [rustc_hir::TraitCandidate<'tcx>]> = inner_owner
        .trait_map
        .items()
        .map(|(&id, candidates)| {
            let candidates: &'tcx [rustc_hir::TraitCandidate<'tcx>] =
                tcx.hir_arena.alloc_slice(&candidates.to_vec());
            (id, candidates)
        })
        .collect();
    // A shim trait is not named by the user, so it is put in scope here rather
    // than by an import. Reusing the recorded imports keeps the import that
    // brought the original trait in from being reported as unused.
    for (id, shim_trait) in extra_traits {
        let mut candidates = trait_map.get(&id).map(|c| c.to_vec()).unwrap_or_default();
        if candidates.iter().any(|c| c.def_id == shim_trait) {
            continue;
        }
        let import_ids = candidates.first().map(|c| c.import_ids).unwrap_or(&[]);
        candidates.push(rustc_hir::TraitCandidate {
            def_id: shim_trait,
            import_ids,
            lint_ambiguous: false,
        });
        trait_map.insert(id, tcx.hir_arena.alloc_slice(&candidates));
    }
    // `OwnerInfo` cannot be copied because `delayed_lints` is a `Steal`; the
    // original lints have already been emitted.
    let owner_info = tcx.hir_arena.alloc(rustc_hir::OwnerInfo {
        nodes,
        parenting: inner_owner.parenting.clone(),
        attrs: rustc_hir::AttributeMap {
            map: inner_owner.attrs.map.clone(),
            opt_hash: inner_owner.attrs.opt_hash,
            define_opaque: inner_owner.attrs.define_opaque,
        },
        trait_map,
        delayed_lints: Steal::new(Vec::new().into_boxed_slice()),
    });
    Some(MaybeOwner::Owner(owner_info))
}

/// Immutable HIR requires reallocating each ancestor of a rewritten expression.
struct Folder<'a, 'tcx> {
    ctxt: &'a Ctxt<'a, 'tcx>,
    owner: &'tcx rustc_hir::OwnerInfo<'tcx>,
    updates: Vec<(ItemLocalId, Node<'tcx>)>,
    reparents: Vec<(ItemLocalId, Reparent)>,
    /// Shim traits that must be in scope at a rewritten method call.
    extra_traits: Vec<(ItemLocalId, DefId)>,
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

    /// `None` means the expression is unchanged.
    ///
    /// The match below is exhaustive on purpose: a new `ExprKind` in a future
    /// toolchain must be a compile error here rather than a position in which a
    /// `proof_with` is silently left unchecked.
    fn fold_expr(&mut self, expr: &'tcx Expr<'tcx>) -> Option<&'tcx Expr<'tcx>> {
        self.reject_direct_shim_reference(expr);
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
                let new_fields = self.fold_fields(fields);
                let new_tail = match tail {
                    StructTailExpr::Base(base) => self.fold_expr(base).map(StructTailExpr::Base),
                    StructTailExpr::None
                    | StructTailExpr::DefaultFields(_)
                    | StructTailExpr::NoneWithError(_) => None,
                };
                if new_fields.is_none() && new_tail.is_none() {
                    return None;
                }
                ExprKind::Struct(qpath, new_fields.unwrap_or(fields), new_tail.unwrap_or(*tail))
            }
            ExprKind::Repeat(e, count) => ExprKind::Repeat(self.fold_expr(e)?, count),
            ExprKind::Yield(e, source) => ExprKind::Yield(self.fold_expr(e)?, *source),
            ExprKind::UnsafeBinderCast(kind, e, ty) => {
                ExprKind::UnsafeBinderCast(*kind, self.fold_expr(e)?, *ty)
            }
            // Const blocks have their own owners, and closure bodies have separate
            // entries in the enclosing owner's body map; both are reached from the
            // loop over bodies instead.
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

    /// A shim has the original's signature plus the extras and no contract at
    /// all, so calling one directly would obtain the original's result — which
    /// may be a tracked capability — with none of its preconditions.
    fn reject_direct_shim_reference(&self, expr: &'tcx Expr<'tcx>) {
        let name = match &expr.kind {
            ExprKind::Path(QPath::Resolved(_, path)) => match path.res.opt_def_id() {
                Some(def_id) if self.ctxt.is_with_shim(def_id) => self.tcx().item_name(def_id),
                _ => return,
            },
            ExprKind::Path(QPath::TypeRelative(_, seg)) => seg.ident.name,
            ExprKind::MethodCall(seg, ..) => seg.ident.name,
            _ => return,
        };
        if !name.as_str().starts_with(WITH_SHIM_PREFIX)
            || name.as_str().starts_with(WITH_ARG_SHIM_PREFIX)
        {
            return;
        }
        self.tcx().dcx().span_err(
            expr.span,
            format!(
                "`{name}` is a shim generated by Verus for a function declared with \
                 extra ghost/tracked arguments; call that function and pass the extras \
                 with `proof_with`"
            ),
        );
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
            let new_guard = arm.guard.and_then(|g| self.fold_expr(g));
            let new_body = self.fold_expr(arm.body);
            if new_guard.is_none() && new_body.is_none() {
                continue;
            }
            let arm = &mut new.get_or_insert_with(|| arms.to_vec())[i];
            if let Some(guard) = new_guard {
                arm.guard = Some(guard);
            }
            if let Some(body) = new_body {
                arm.body = body;
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
                StmtKind::Let(self.tcx().hir_arena.alloc(rustc_hir::LetStmt {
                    init: init.or(let_stmt.init),
                    els: els.or(let_stmt.els),
                    ..**let_stmt
                }))
            }
            StmtKind::Expr(e) => StmtKind::Expr(self.fold_expr(e)?),
            StmtKind::Semi(e) => StmtKind::Semi(self.fold_expr(e)?),
            StmtKind::Item(_) => return None,
        };
        let new = Stmt { kind, ..*stmt };
        self.updates.push((stmt.hir_id.local_id, Node::Stmt(self.tcx().hir_arena.alloc(new))));
        Some(new)
    }

    fn try_rewrite_proof_with(&mut self, expr: &'tcx Expr<'tcx>) -> Option<&'tcx Expr<'tcx>> {
        let ExprKind::Call(marker, marker_args) = &expr.kind else {
            return None;
        };
        let with_outputs = self.ctxt.is_proof_with_marker(marker)?;
        if marker_args.len() != 2 {
            return None;
        }

        // The extras are a single expression, or a tuple of them.
        let raw_extras: &'tcx [Expr<'tcx>] = match &marker_args[0].kind {
            ExprKind::Tup(elems) => elems,
            _ => std::slice::from_ref(&marker_args[0]),
        };
        let extras: Vec<Expr<'tcx>> =
            raw_extras.iter().map(|e| self.fold_expr(e).copied().unwrap_or(*e)).collect();
        let call = &marker_args[1];
        let call = self.fold_expr(call).unwrap_or(call);
        let extra_ids: Vec<ItemLocalId> = extras.iter().map(|e| e.hir_id.local_id).collect();

        let new_kind = match &call.kind {
            ExprKind::Call(callee, args) => {
                let mut new_args = args.to_vec();
                new_args.extend(extras);
                let shim_callee = self.redirect_callee(callee, with_outputs)?;
                ExprKind::Call(shim_callee, self.alloc_exprs(new_args))
            }
            ExprKind::MethodCall(seg, receiver, args, span) => {
                let mut new_args = args.to_vec();
                new_args.extend(extras);
                self.bring_shim_traits_into_scope(call.hir_id.local_id);
                let new_seg = self.rename_segment(seg, with_outputs);
                ExprKind::MethodCall(new_seg, receiver, self.alloc_exprs(new_args), *span)
            }
            _ => {
                self.tcx().dcx().span_err(
                    call.span,
                    "extra ghost/tracked arguments can only be applied to a function call",
                );
                return None;
            }
        };
        // The retained call inherits the removed marker's parent, while the extra
        // arguments become children of that call.
        let new = self.mk_expr(call, new_kind);
        for id in extra_ids {
            self.reparents.push((id, Reparent::To(call.hir_id.local_id)));
        }
        self.reparents.push((call.hir_id.local_id, Reparent::AdoptFrom(expr.hir_id.local_id)));
        Some(new)
    }

    fn redirect_callee(
        &mut self,
        callee: &'tcx Expr<'tcx>,
        with_outputs: bool,
    ) -> Option<&'tcx Expr<'tcx>> {
        let ExprKind::Path(qpath) = &callee.kind else {
            self.tcx()
                .dcx()
                .span_err(callee.span, "unsupported callee for extra ghost/tracked arguments");
            return None;
        };
        let new_qpath = match qpath {
            // The qualifying type resolves later, so only the name can be changed
            // here; an absent shim then surfaces as an unresolved method.
            QPath::TypeRelative(ty, seg) => {
                self.bring_shim_traits_into_scope(callee.hir_id.local_id);
                QPath::TypeRelative(ty, self.rename_segment(seg, with_outputs))
            }
            QPath::Resolved(self_ty, path) => {
                let Res::Def(def_kind, def_id) = path.res else {
                    return None;
                };
                let Some(shim) = self.ctxt.find_shim(def_id, with_outputs) else {
                    let name = self.tcx().item_name(def_id);
                    let what = match with_outputs {
                        true => "extra ghost/tracked outputs",
                        false => "extra ghost/tracked arguments",
                    };
                    self.tcx()
                        .dcx()
                        .span_err(callee.span, format!("`{name}` is not declared with {what}"));
                    return None;
                };
                let tcx = self.tcx();
                let res = Res::Def(def_kind, shim);
                let mut segments = path.segments.to_vec();
                let last = segments.last_mut()?;
                *last = PathSegment {
                    ident: rustc_span::symbol::Ident::new(tcx.item_name(shim), last.ident.span),
                    res,
                    ..*last
                };
                QPath::Resolved(
                    *self_ty,
                    tcx.hir_arena.alloc(rustc_hir::Path {
                        span: path.span,
                        res,
                        segments: tcx.hir_arena.alloc_slice(&segments),
                    }),
                )
            }
        };
        Some(self.mk_expr(callee, ExprKind::Path(new_qpath)))
    }

    /// A trait method's shim lives on a shim trait the user never names, so
    /// method resolution would not consider it. Every trait that was in scope for
    /// the original call contributes its shim trait, if it has one; the receiver's
    /// type is not known before type checking, so the choice among them is left to
    /// method resolution, exactly as it is for the original call.
    fn bring_shim_traits_into_scope(&mut self, id: ItemLocalId) {
        let Some(candidates) = self.owner.trait_map.get(&id) else {
            return;
        };
        let shim_traits: Vec<DefId> = candidates
            .iter()
            .filter_map(|candidate| self.ctxt.find_shim_trait(candidate.def_id))
            .collect();
        self.extra_traits.extend(shim_traits.into_iter().map(|def_id| (id, def_id)));
    }

    /// An inherent method's shim lives in the same impl, so the call resolves the
    /// same way once the name is changed.
    fn rename_segment(
        &mut self,
        seg: &'tcx PathSegment<'tcx>,
        with_outputs: bool,
    ) -> &'tcx PathSegment<'tcx> {
        let ident =
            rustc_span::symbol::Ident::new(shim_name(seg.ident.name, with_outputs), seg.ident.span);
        self.tcx().hir_arena.alloc(PathSegment { ident, res: Res::Err, ..*seg })
    }
}
