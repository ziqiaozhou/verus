//! Validates calls redirected by `hir_proof_with_rewrite` to the verified
//! counterparts of functions declared `#[verus_spec(with ..)]`.
//!
//! The rewrite runs before type checking so that rustc checks the extra ghost/tracked
//! arguments, but at that point a method call has only a name, not a resolved
//! receiver type. Rust prefers an inherent method over a trait method of the same
//! name. Redirecting such a call to the trait method's counterpart would therefore
//! verify a contract for a method that the compiled program does not run.

use crate::attributes::{VERIFIED_PREFIX, is_unverified_stub, is_verified_counterpart};
use crate::util::err_span;
use rustc_hir::{Expr, ExprKind, QPath};
use rustc_middle::ty::fast_reject::{TreatParams, simplify_type};
use rustc_middle::ty::{Ty, TyCtxt, TyKind, TypingEnv};
use rustc_span::def_id::DefId;
use rustc_span::symbol::Symbol;
use vir::ast::VirErr;

/// Rejects redirected calls whose verified counterpart can differ from the method
/// selected by Rust for the compiled program.
///
/// This check runs for every call lowered to VIR. Unredirected calls return early
/// because their names lack [`VERIFIED_PREFIX`].
pub(crate) fn check_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    types: &rustc_middle::ty::TypeckResults<'tcx>,
    expr: &Expr<'tcx>,
    resolved: DefId,
) -> Result<(), VirErr> {
    let Some((name, self_ty)) = call_form(types, expr) else {
        return Ok(());
    };
    let Some(name) = name.as_str().strip_prefix(VERIFIED_PREFIX) else {
        return Ok(());
    };
    if !is_verified_counterpart(def_attrs(tcx, resolved)) {
        return err_span(
            expr.span,
            format!(
                "`{name}` does not accept extra ghost/tracked arguments: \
                 it is not declared with `#[verus_spec(with ..)]`"
            ),
        );
    }
    // An inherent counterpart is declared alongside the original inherent method,
    // so resolving to it cannot substitute a trait contract.
    if tcx.trait_of_assoc(resolved).is_none() {
        return Ok(());
    }
    let Some(self_ty) = self_ty else {
        return Ok(());
    };
    let typing_env = TypingEnv::post_analysis(tcx, expr.hir_id.owner.to_def_id());
    let Some(shadowing) = inherent_method(tcx, typing_env, self_ty, Symbol::intern(name)) else {
        return Ok(());
    };
    // Local inherent counterparts are available to the pre-type-check rewrite.
    // Foreign inherent impls cannot be enumerated by name at that stage, so a
    // legitimate foreign `with` method may instead reach an in-scope trait
    // counterpart. A type-relative call defers that choice to Rust's resolution.
    if is_unverified_stub(def_attrs(tcx, shadowing)) {
        return err_span(
            expr.span,
            format!(
                "`{name}` is an inherent method of another crate, and a trait method \
                 of that name is in scope. Verus cannot tell which of the two a call \
                 with ghost/tracked arguments means before type checking, so this is \
                 a limitation of `#[verus_spec(with ..)]`: call the method as \
                 `Type::{name}(receiver, ..)`, naming the type it belongs to"
            ),
        );
    }
    err_span(
        expr.span,
        format!(
            "`{name}` resolves to an inherent method, which shadows the trait \
             method of that name and is not declared with `#[verus_spec(with ..)]`"
        ),
    )
}

/// Returns the source-level method name and the type on which an inherent method
/// could shadow it.
///
/// Only the calls whose callee name resolution leaves to type checking are
/// returned. `hir_proof_with_rewrite` knows what a resolved path names and reports
/// a callee that takes no ghost/tracked arguments itself, so such a call is left
/// out here, where a name a user chose could not be told from a redirected one.
fn call_form<'tcx>(
    types: &rustc_middle::ty::TypeckResults<'tcx>,
    expr: &Expr<'tcx>,
) -> Option<(Symbol, Option<Ty<'tcx>>)> {
    match &expr.kind {
        ExprKind::MethodCall(seg, receiver, ..) => {
            Some((seg.ident.name, Some(types.expr_ty(receiver))))
        }
        ExprKind::Call(callee, _) => match &callee.kind {
            ExprKind::Path(QPath::TypeRelative(qself, seg)) => {
                Some((seg.ident.name, Some(types.node_type(qself.hir_id))))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Finds the inherent method that Rust would prefer over a trait method of `name`.
///
/// Rust looks for a method along the autoderef chain of the receiver type, so a
/// receiver of type `Box<S>` reaches the inherent methods of `S`. Following the
/// same chain here keeps a smart pointer from hiding a shadowing method.
fn inherent_method<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    name: Symbol,
) -> Option<DefId> {
    let mut ty = ty;
    // A `Deref` implementation may cycle; Rust bounds the chain the same way.
    for _ in 0..MAX_AUTODEREF_STEPS {
        if let Some(found) = inherent_method_of(tcx, ty, name) {
            return Some(found);
        }
        ty = deref_target(tcx, typing_env, ty)?;
    }
    None
}

const MAX_AUTODEREF_STEPS: usize = 32;

fn inherent_method_of<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, name: Symbol) -> Option<DefId> {
    let impls: &[DefId] = match ty.kind() {
        TyKind::Adt(adt, _) => tcx.inherent_impls(adt.did()),
        // Types that no crate owns, such as primitives and slices, carry their
        // inherent methods in implementations keyed by shape instead.
        _ => match simplify_type(tcx, ty, TreatParams::InstantiateWithInfer) {
            Some(simplified) => tcx.incoherent_impls(simplified),
            None => return None,
        },
    };
    impls.iter().find_map(|impl_id| {
        Some(tcx.associated_items(*impl_id).filter_by_name_unhygienic(name).next()?.def_id)
    })
}

fn deref_target<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Option<Ty<'tcx>> {
    if let Some(inner) = ty.builtin_deref(true) {
        return Some(inner);
    }
    let target = tcx.lang_items().deref_target()?;
    let projection = Ty::new_projection(tcx, target, [ty]);
    let normalized = tcx
        .try_normalize_erasing_regions(typing_env, rustc_middle::ty::Unnormalized::new(projection))
        .ok()?;
    (normalized != projection).then_some(normalized)
}

fn def_attrs<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> &'tcx [rustc_hir::Attribute] {
    match def_id.as_local() {
        Some(local) => tcx.hir_attrs(tcx.local_def_id_to_hir_id(local)),
        None => tcx.attrs_for_def(def_id),
    }
}
