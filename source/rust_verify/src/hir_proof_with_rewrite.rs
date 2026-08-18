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
    Arm, Block, Expr, ExprField, ExprKind, ItemLocalId, LetExpr, MaybeOwner, Node, OwnerNode,
    PathSegment, QPath, Stmt, StmtKind,
};
use rustc_index::IndexVec;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefIndex;
use rustc_span::symbol::Symbol;
use std::collections::HashMap;

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

    let ctxt = Ctxt::new(tcx, &new_owners);

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

struct Ctxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// (parent def, item name) -> def id, for all local functions.
    local_fns: HashMap<(DefId, Symbol), DefId>,
    /// Attributes of local items. Reading them through `tcx` would re-enter the
    /// `hir_crate` query that this pass is part of.
    local_attrs: HashMap<LocalDefId, &'tcx [rustc_hir::Attribute]>,
}

impl<'tcx> Ctxt<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>) -> Ctxt<'tcx> {
        let (local_fns, local_attrs) = local_maps(tcx, owners);
        Ctxt { tcx, local_fns, local_attrs }
    }
}

/// Index the functions of this crate and their attributes.
fn local_maps<'tcx>(
    tcx: TyCtxt<'tcx>,
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
) -> (HashMap<(DefId, Symbol), DefId>, HashMap<LocalDefId, &'tcx [rustc_hir::Attribute]>) {
    let mut map = HashMap::new();
    let mut attrs = HashMap::new();
    for (def_id, owner) in owners.iter_enumerated() {
        let MaybeOwner::Owner(owner) = owner else {
            continue;
        };
        let ident = match owner.node() {
            OwnerNode::Item(item) => match &item.kind {
                rustc_hir::ItemKind::Fn { ident, .. } => *ident,
                _ => continue,
            },
            OwnerNode::ImplItem(item) => match &item.kind {
                rustc_hir::ImplItemKind::Fn(..) => item.ident,
                _ => continue,
            },
            _ => continue,
        };
        let Some(parent) = tcx.opt_local_parent(def_id) else {
            continue;
        };
        map.insert((parent.to_def_id(), ident.name), def_id.to_def_id());
        attrs.insert(def_id, owner.attrs.get(ItemLocalId::ZERO));
    }
    (map, attrs)
}

impl<'tcx> Ctxt<'tcx> {
    /// Attributes of `def_id`.
    ///
    /// Note: for local items we must not go through tcx.hir_attrs, which would
    /// re-enter the hir_crate query we are computing.
    fn attrs(&self, def_id: DefId) -> Option<&'tcx [rustc_hir::Attribute]> {
        if let Some(local) = def_id.as_local() {
            self.local_attrs.get(&local).copied()
        } else {
            Some(self.tcx.attrs_for_def(def_id))
        }
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
        let (is_stub, is_proxy) = self.stub_kind(def_id);
        if !is_stub {
            return None;
        }
        counterpart_of(self.tcx, &self.local_fns, def_id, is_proxy)
    }
}

fn rewrite_owner<'tcx>(
    ctxt: &Ctxt<'tcx>,
    inner_owner: &'tcx rustc_hir::OwnerInfo<'tcx>,
) -> Option<MaybeOwner<'tcx>> {
    let tcx = ctxt.tcx;
    let mut bodies = inner_owner.nodes.bodies.clone();
    let mut nodes = inner_owner.nodes.nodes.clone();
    let mut changed = false;

    for (local_id, body) in inner_owner.nodes.bodies.iter() {
        let mut folder = Folder { ctxt, updates: Vec::new() };
        let Some(value) = folder.fold_expr(body.value) else {
            continue;
        };
        for (id, node) in folder.updates.iter() {
            if let Some(parented) = nodes.get_mut(*id) {
                parented.node = *node;
            }
        }
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
    let trait_map = clone_trait_map(tcx, inner_owner);
    let owner_info = mk_owner(tcx, inner_owner, nodes, trait_map);
    Some(MaybeOwner::Owner(owner_info))
}

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

/// Rebuilds the spine from the body root down to each rewritten call. HIR is
/// immutable arena data and type checking walks the expression tree through the
/// child pointers of each node, so every ancestor of a replaced expression has to
/// be reallocated with the new child. Hir ids and spans are preserved.
struct Folder<'a, 'tcx> {
    ctxt: &'a Ctxt<'tcx>,
    updates: Vec<(ItemLocalId, Node<'tcx>)>,
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
            QPath::TypeRelative(ty, seg) => QPath::TypeRelative(ty, self.rename_segment(seg)?),
        };
        Some(self.mk_expr(callee, ExprKind::Path(new_qpath)))
    }

    /// Point a resolved path at the verified counterpart, which an external
    /// function specified by an `assume_specification` does not share a name
    /// with.
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
        let last = *segments.last()?;
        *segments.last_mut()? = rename(&last, res);
        Some(tcx.hir_arena.alloc(rustc_hir::Path {
            span: path.span,
            res,
            segments: tcx.hir_arena.alloc_slice(&segments),
        }))
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
fn counterpart_of(
    tcx: TyCtxt<'_>,
    local_fns: &HashMap<(DefId, Symbol), DefId>,
    def_id: DefId,
    is_unerased_proxy: bool,
) -> Option<DefId> {
    let name = counterpart_name(tcx.item_name(def_id), is_unerased_proxy);
    let parent = tcx.opt_parent(def_id)?;
    if let Some(found) = local_fns.get(&(parent, name)) {
        return Some(*found);
    }
    if parent.is_local() {
        // A local counterpart is in `local_fns` already, and the queries below
        // would re-enter the `hir_crate` computation this pass is part of.
        return None;
    }
    match tcx.def_kind(parent) {
        DefKind::Mod => tcx
            .module_children(parent)
            .iter()
            .find(|child| child.ident.name == name)
            .and_then(|child| child.res.opt_def_id()),
        DefKind::Impl { .. } => tcx
            .associated_items(parent)
            .filter_by_name_unhygienic(name)
            .next()
            .map(|assoc| assoc.def_id),
        _ => None,
    }
}

/// The name of the verified counterpart of the unverified stub `name`. A `const fn`
/// is also split into an erased item and an unerased proxy, and both are stubs, but
/// the counterpart is named after the function the user wrote, without the prefix
/// the proxy carries.
fn counterpart_name(name: Symbol, is_unerased_proxy: bool) -> Symbol {
    let name = name.as_str();
    let name = match is_unerased_proxy {
        true => name.strip_prefix(UNERASED_PROXY_PREFIX).unwrap_or(name),
        false => name,
    };
    verified_name(Symbol::intern(name))
}
