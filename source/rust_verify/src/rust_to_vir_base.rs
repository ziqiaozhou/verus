use crate::attributes::get_verifier_attrs;
use crate::context::BodyCtxt;
use crate::util::{err_span_str, unsupported_err_span};
use crate::{unsupported, unsupported_err, unsupported_err_unless};
use rustc_ast::{IntTy, Mutability, UintTy};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::definitions::DefPath;
use rustc_hir::{
    GenericBound, GenericParam, GenericParamKind, Generics, HirId, ItemKind, LifetimeParamKind,
    ParamName, PathSegment, PolyTraitRef, PrimTy, QPath, TraitBoundModifier, TraitFn,
    TraitItemKind, Ty, Visibility, VisibilityKind,
};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::{AdtDef, TyCtxt, TyKind};
use rustc_span::def_id::{DefId, LOCAL_CRATE};
use rustc_span::symbol::{kw, Ident};
use rustc_span::Span;
use rustc_trait_selection::infer::InferCtxtExt;
use std::sync::Arc;
use vir::ast::{GenericBoundX, IntRange, Mode, Path, PathX, Typ, TypBounds, TypX, Typs, VirErr};
use vir::ast_util::types_equal;

pub(crate) fn def_path_to_vir_path<'tcx>(tcx: TyCtxt<'tcx>, def_path: DefPath) -> Path {
    let krate = if def_path.krate == LOCAL_CRATE {
        None
    } else {
        Some(Arc::new(tcx.crate_name(def_path.krate).to_string()))
    };
    let segments =
        Arc::new(def_path.data.iter().map(|d| Arc::new(format!("{}", d))).collect::<Vec<_>>());
    Arc::new(PathX { krate, segments })
}

fn get_function_def_impl_item_node<'tcx>(
    tcx: TyCtxt<'tcx>,
    hir_id: rustc_hir::HirId,
) -> Option<(&'tcx rustc_hir::FnSig<'tcx>, &'tcx rustc_hir::BodyId)> {
    let node = tcx.hir().get(hir_id);
    match node {
        rustc_hir::Node::ImplItem(rustc_hir::ImplItem {
            kind: rustc_hir::ImplItemKind::Fn(fn_sig, body_id),
            ..
        }) => Some((fn_sig, body_id)),
        _ => None,
    }
}

pub(crate) fn get_function_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    hir_id: rustc_hir::HirId,
) -> (&'tcx rustc_hir::FnSig<'tcx>, &'tcx rustc_hir::BodyId) {
    get_function_def_impl_item_node(tcx, hir_id)
        .or_else(|| match tcx.hir().get(hir_id) {
            rustc_hir::Node::Item(item) => match &item.kind {
                ItemKind::Fn(fn_sig, _, body_id) => Some((fn_sig, body_id)),
                _ => None,
            },
            rustc_hir::Node::TraitItem(item) => match &item.kind {
                TraitItemKind::Fn(fn_sig, TraitFn::Provided(body_id)) => Some((fn_sig, body_id)),
                _ => None,
            },
            node => unsupported!("extern functions, or other function Node", node),
        })
        .expect("function expected")
}

pub(crate) fn typ_path_and_ident_to_vir_path<'tcx>(path: &Path, ident: vir::ast::Ident) -> Path {
    let mut path = (**path).clone();
    Arc::make_mut(&mut path.segments).push(ident);
    Arc::new(path)
}

pub(crate) fn fn_item_hir_id_to_self_def_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    hir_id: HirId,
) -> Option<DefId> {
    let parent_id = tcx.hir().get_parent_node(hir_id);
    let parent_node = tcx.hir().get(parent_id);
    match parent_node {
        rustc_hir::Node::Item(rustc_hir::Item {
            kind: rustc_hir::ItemKind::Impl(impll), ..
        }) => match &impll.self_ty.kind {
            rustc_hir::TyKind::Path(QPath::Resolved(
                None,
                rustc_hir::Path { res: rustc_hir::def::Res::Def(_, self_def_id), .. },
            )) => Some(*self_def_id),
            _ => {
                panic!("impl type is not given by a path");
            }
        },
        _ => None,
    }
}

pub(crate) fn def_id_to_vir_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Path {
    // The path that rustc gives a DefId might be given in terms of an 'impl' path
    // However, it makes for a better path name to use the path to the *type*.
    // So first, we check if the given DefId is the definition of a fn inside an impl.
    // If so, we construct a VIR path based on the VIR path for the type.
    if let Some(local_id) = def_id.as_local() {
        let hir = tcx.hir().local_def_id_to_hir_id(local_id);
        if get_function_def_impl_item_node(tcx, hir).is_some() {
            if let Some(self_def_id) = fn_item_hir_id_to_self_def_id(tcx, hir) {
                let ty_path = def_path_to_vir_path(tcx, tcx.def_path(self_def_id));
                return typ_path_and_ident_to_vir_path(&ty_path, def_to_path_ident(tcx, def_id));
            }
        }
    }
    // Otherwise build a path based on the segments rustc gives us
    // without doing anything fancy.
    def_path_to_vir_path(tcx, tcx.def_path(def_id))
}

pub(crate) fn def_to_path_ident<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> vir::ast::Ident {
    let def_path = tcx.def_path(def_id);
    match def_path.data.last().expect("unexpected empty impl path").data {
        rustc_hir::definitions::DefPathData::ValueNs(name) => Arc::new(name.to_string()),
        _ => panic!("unexpected name of impl"),
    }
}

pub(crate) fn def_id_to_datatype<'tcx, 'hir>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    typ_args: Typs,
) -> TypX {
    TypX::Datatype(def_id_to_vir_path(tcx, def_id), typ_args)
}

pub(crate) fn def_id_to_datatype_typ_args<'tcx, 'hir>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    segments: &'hir [PathSegment<'hir>],
) -> (Path, Typs) {
    let typ_args: Vec<Typ> = match &segments.last().expect("type must have a segment").args {
        None => vec![],
        Some(args) => args
            .args
            .iter()
            .filter_map(|a| match a {
                rustc_hir::GenericArg::Type(t) => Some(ty_to_vir(tcx, &t)),
                rustc_hir::GenericArg::Lifetime(_) => None,
                _ => panic!("unexpected type arguments"),
            })
            .collect(),
    };
    (def_id_to_vir_path(tcx, def_id), Arc::new(typ_args))
}

pub(crate) fn def_id_to_datatype_typx<'tcx, 'hir>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    segments: &'hir [PathSegment<'hir>],
) -> TypX {
    let (path, typ_args) = def_id_to_datatype_typ_args(tcx, def_id, segments);
    TypX::Datatype(path, typ_args)
}

// TODO: proper handling of def_ids
// use https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/ty/context/struct.TyCtxt.html#method.lang_items ?
pub(crate) fn hack_get_def_name<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> String {
    let debug_name = tcx.def_path_debug_str(def_id);
    let last_colon = debug_name.rfind(':').unwrap();
    debug_name[last_colon + 1..].to_string()
}

pub(crate) fn ident_to_var<'tcx>(ident: &Ident) -> String {
    ident.to_string()
}

pub(crate) fn is_visibility_private(vis_kind: &VisibilityKind, inherited_is_private: bool) -> bool {
    match vis_kind {
        VisibilityKind::Inherited => inherited_is_private,
        VisibilityKind::Public => false,
        VisibilityKind::Crate(_) => false,
        VisibilityKind::Restricted { .. } => unsupported!("restricted visibility"),
    }
}

pub(crate) fn mk_visibility<'tcx>(
    owning_module: &Option<Path>,
    vis: &Visibility<'tcx>,
    inherited_is_private: bool,
) -> vir::ast::Visibility {
    vir::ast::Visibility {
        owning_module: owning_module.clone(),
        is_private: is_visibility_private(&vis.node, inherited_is_private),
    }
}

pub(crate) fn get_range(typ: &Typ) -> IntRange {
    match &**typ {
        TypX::Int(range) => *range,
        _ => panic!("get_range {:?}", typ),
    }
}

pub(crate) fn mk_range<'tcx>(ty: rustc_middle::ty::Ty<'tcx>) -> IntRange {
    match ty.kind() {
        TyKind::Adt(_, _) if ty.to_string() == crate::typecheck::BUILTIN_INT => IntRange::Int,
        TyKind::Adt(_, _) if ty.to_string() == crate::typecheck::BUILTIN_NAT => IntRange::Nat,
        TyKind::Uint(rustc_middle::ty::UintTy::U8) => IntRange::U(8),
        TyKind::Uint(rustc_middle::ty::UintTy::U16) => IntRange::U(16),
        TyKind::Uint(rustc_middle::ty::UintTy::U32) => IntRange::U(32),
        TyKind::Uint(rustc_middle::ty::UintTy::U64) => IntRange::U(64),
        TyKind::Uint(rustc_middle::ty::UintTy::U128) => IntRange::U(128),
        TyKind::Uint(rustc_middle::ty::UintTy::Usize) => IntRange::USize,
        TyKind::Int(rustc_middle::ty::IntTy::I8) => IntRange::I(8),
        TyKind::Int(rustc_middle::ty::IntTy::I16) => IntRange::I(16),
        TyKind::Int(rustc_middle::ty::IntTy::I32) => IntRange::I(32),
        TyKind::Int(rustc_middle::ty::IntTy::I64) => IntRange::I(64),
        TyKind::Int(rustc_middle::ty::IntTy::I128) => IntRange::I(128),
        TyKind::Int(rustc_middle::ty::IntTy::Isize) => IntRange::ISize,
        _ => panic!("mk_range {:?}", ty),
    }
}

pub(crate) fn mid_ty_simplify<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    allow_mut_ref: bool,
) -> rustc_middle::ty::Ty<'tcx> {
    match ty.kind() {
        TyKind::Ref(_, t, Mutability::Not) => mid_ty_simplify(tcx, t, allow_mut_ref),
        TyKind::Ref(_, t, Mutability::Mut) if allow_mut_ref => {
            mid_ty_simplify(tcx, t, allow_mut_ref)
        }
        TyKind::Adt(AdtDef { did, .. }, args) => {
            let def_name = vir::ast_util::path_as_rust_name(&def_id_to_vir_path(tcx, *did));
            let is_box = Some(*did) == tcx.lang_items().owned_box() && args.len() == 2;
            let is_smart_ptr = (def_name == "alloc::rc::Rc"
                || def_name == "alloc::sync::Arc"
                || def_name == "builtin::Ghost"
                || def_name == "builtin::Tracked")
                && args.len() == 1;
            if is_box || is_smart_ptr {
                if let rustc_middle::ty::subst::GenericArgKind::Type(t) = args[0].unpack() {
                    mid_ty_simplify(tcx, t, false)
                } else {
                    panic!("unexpected type argument")
                }
            } else {
                ty
            }
        }
        _ => ty,
    }
}

pub(crate) fn mid_ty_to_mode<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<Mode> {
    match ty.kind() {
        TyKind::Adt(AdtDef { did, .. }, _args) => {
            let def_name = vir::ast_util::path_as_rust_name(&def_id_to_vir_path(tcx, *did));
            if def_name == "builtin::Ghost" {
                Some(Mode::Spec)
            } else if def_name == "builtin::Tracked" {
                Some(Mode::Proof)
            } else {
                None
            }
        }
        _ => None,
    }
}

// TODO review and cosolidate type translation, e.g. with `ty_to_vir`, if possible

// returns VIR Typ and whether Ghost/Tracked was erased from around the outside of the VIR Typ
pub(crate) fn mid_ty_to_vir_ghost<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    allow_mut_ref: bool,
) -> (Typ, bool) {
    match ty.kind() {
        TyKind::Bool => (Arc::new(TypX::Bool), false),
        TyKind::Uint(_) | TyKind::Int(_) => (Arc::new(TypX::Int(mk_range(ty))), false),
        TyKind::Ref(_, tys, rustc_ast::Mutability::Not) => {
            mid_ty_to_vir_ghost(tcx, tys, allow_mut_ref)
        }
        TyKind::Ref(_, tys, rustc_ast::Mutability::Mut) if allow_mut_ref => {
            mid_ty_to_vir_ghost(tcx, tys, allow_mut_ref)
        }
        TyKind::Param(param) if param.name == kw::SelfUpper => {
            (Arc::new(TypX::TypParam(vir::def::trait_self_type_param())), false)
        }
        TyKind::Param(param) => (Arc::new(TypX::TypParam(Arc::new(param.name.to_string()))), false),
        TyKind::Never => {
            // All types are inhabited in SMT; we pick an arbitrary inhabited type for Never
            (Arc::new(TypX::Tuple(Arc::new(vec![]))), false)
        }
        TyKind::Tuple(_) => {
            let typs: Vec<Typ> =
                ty.tuple_fields().map(|t| mid_ty_to_vir_ghost(tcx, t, allow_mut_ref).0).collect();
            (Arc::new(TypX::Tuple(Arc::new(typs))), false)
        }
        TyKind::Adt(AdtDef { did, .. }, args) => {
            let s = ty.to_string();
            // TODO use lang items instead of string comparisons
            if s == crate::typecheck::BUILTIN_INT {
                (Arc::new(TypX::Int(IntRange::Int)), false)
            } else if s == crate::typecheck::BUILTIN_NAT {
                (Arc::new(TypX::Int(IntRange::Nat)), false)
            } else {
                let typ_args: Vec<(Typ, bool)> = args
                    .iter()
                    .filter_map(|arg| match arg.unpack() {
                        rustc_middle::ty::subst::GenericArgKind::Type(t) => {
                            Some(mid_ty_to_vir_ghost(tcx, t, allow_mut_ref))
                        }
                        rustc_middle::ty::subst::GenericArgKind::Lifetime(_) => None,
                        _ => panic!("unexpected type argument"),
                    })
                    .collect();
                if Some(*did) == tcx.lang_items().owned_box() && typ_args.len() == 2 {
                    return typ_args[0].clone();
                }
                let def_name = vir::ast_util::path_as_rust_name(&def_id_to_vir_path(tcx, *did));
                if (def_name == "alloc::rc::Rc" || def_name == "alloc::sync::Arc")
                    && typ_args.len() == 1
                {
                    return typ_args[0].clone();
                }
                if (def_name == "builtin::Ghost" || def_name == "builtin::Tracked")
                    && typ_args.len() == 1
                {
                    return (typ_args[0].0.clone(), true);
                }
                let typ_args = typ_args.into_iter().map(|(t, _)| t).collect();
                (Arc::new(def_id_to_datatype(tcx, *did, Arc::new(typ_args))), false)
            }
        }
        TyKind::Closure(_def, substs) => {
            let sig = substs.as_closure().sig();
            let args: Vec<Typ> = sig
                .inputs()
                .skip_binder()
                .iter()
                .map(|t| mid_ty_to_vir_ghost(tcx, t, allow_mut_ref).0)
                .collect();
            let ret = mid_ty_to_vir_ghost(tcx, sig.output().skip_binder(), allow_mut_ref).0;
            (Arc::new(TypX::Lambda(Arc::new(args), ret)), false)
        }
        _ => {
            unsupported!(format!("type {:?}", ty))
        }
    }
}

pub(crate) fn mid_ty_to_vir<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    allow_mut_ref: bool,
) -> Typ {
    mid_ty_to_vir_ghost(tcx, ty, allow_mut_ref).0
}

pub(crate) fn is_type_std_rc_or_arc<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    match ty.kind() {
        TyKind::Adt(AdtDef { did, .. }, _args) => {
            let def_name = vir::ast_util::path_as_rust_name(&def_id_to_vir_path(tcx, *did));
            if def_name == "alloc::rc::Rc" || def_name == "alloc::sync::Arc" {
                return true;
            }
        }
        _ => {}
    }
    false
}

// TODO remove if unused
pub(crate) fn _ty_resolved_path_to_debug_path(_tcx: TyCtxt<'_>, ty: &Ty) -> String {
    let Ty { hir_id: _, kind, span: _ } = ty;
    match kind {
        rustc_hir::TyKind::Path(QPath::Resolved(None, path)) => path
            .segments
            .iter()
            .map(|x| x.ident.name.to_ident_string())
            .collect::<Vec<_>>()
            .join("::"),
        _ => panic!("{:?} does not have a resolved path", ty),
    }
}

pub(crate) fn impl_def_id_to_self_ty<'tcx>(tcx: TyCtxt<'tcx>, impl_def_id: DefId) -> Typ {
    let local_id = impl_def_id.as_local().expect("impl_def_id_to_self_ty expects local id");
    let hir_id = tcx.hir().local_def_id_to_hir_id(local_id);
    let node = tcx.hir().get(hir_id);
    match node {
        rustc_hir::Node::Item(rustc_hir::Item {
            kind: rustc_hir::ItemKind::Impl(impll), ..
        }) => ty_to_vir(tcx, &impll.self_ty),
        _ => {
            panic!("impl_def_id_to_self_ty expected an Impl node");
        }
    }
}

pub(crate) fn ty_to_vir<'tcx>(tcx: TyCtxt<'tcx>, ty: &Ty) -> Typ {
    let Ty { hir_id: _, kind, span } = ty;
    match kind {
        rustc_hir::TyKind::Tup(tys) => {
            Arc::new(TypX::Tuple(Arc::new(tys.iter().map(|t| ty_to_vir(tcx, t)).collect())))
        }
        rustc_hir::TyKind::Rptr(
            _,
            rustc_hir::MutTy { ty: tys, mutbl: rustc_ast::Mutability::Not },
        ) => ty_to_vir(tcx, tys),
        rustc_hir::TyKind::Path(QPath::Resolved(None, path)) => Arc::new(match path.res {
            Res::PrimTy(PrimTy::Bool) => TypX::Bool,
            Res::PrimTy(PrimTy::Uint(UintTy::U8)) => TypX::Int(IntRange::U(8)),
            Res::PrimTy(PrimTy::Uint(UintTy::U16)) => TypX::Int(IntRange::U(16)),
            Res::PrimTy(PrimTy::Uint(UintTy::U32)) => TypX::Int(IntRange::U(32)),
            Res::PrimTy(PrimTy::Uint(UintTy::U64)) => TypX::Int(IntRange::U(64)),
            Res::PrimTy(PrimTy::Uint(UintTy::U128)) => TypX::Int(IntRange::U(128)),
            Res::PrimTy(PrimTy::Uint(UintTy::Usize)) => TypX::Int(IntRange::USize),
            Res::PrimTy(PrimTy::Int(IntTy::I8)) => TypX::Int(IntRange::I(8)),
            Res::PrimTy(PrimTy::Int(IntTy::I16)) => TypX::Int(IntRange::I(16)),
            Res::PrimTy(PrimTy::Int(IntTy::I32)) => TypX::Int(IntRange::I(32)),
            Res::PrimTy(PrimTy::Int(IntTy::I64)) => TypX::Int(IntRange::I(64)),
            Res::PrimTy(PrimTy::Int(IntTy::I128)) => TypX::Int(IntRange::I(128)),
            Res::PrimTy(PrimTy::Int(IntTy::Isize)) => TypX::Int(IntRange::ISize),

            Res::Def(DefKind::TyParam, def_id) => {
                let path = def_id_to_vir_path(tcx, def_id);
                let name = path.segments.last().unwrap();
                if **name == kw::SelfUpper.to_string() {
                    TypX::TypParam(vir::def::trait_self_type_param())
                } else {
                    TypX::TypParam(name.clone())
                }
            }
            Res::Def(DefKind::Struct, def_id) => {
                // TODO: consider using #[rust_diagnostic_item] and https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/ty/query/query_stored/type.diagnostic_items.html for the builtin lib
                let def_name = vir::ast_util::path_as_rust_name(&def_id_to_vir_path(tcx, def_id));
                if def_name == "builtin::int" {
                    TypX::Int(IntRange::Int)
                } else if def_name == "builtin::nat" {
                    TypX::Int(IntRange::Nat)
                } else if Some(def_id) == tcx.lang_items().owned_box()
                    || def_name == "alloc::rc::Rc"
                    || def_name == "alloc::sync::Arc"
                    || def_name == "builtin::Ghost"
                    || def_name == "builtin::Tracked"
                {
                    match &path.segments[0].args.expect("Box/Rc/Arc/Ghost/Tracked arg").args[0] {
                        rustc_hir::GenericArg::Type(t) => return ty_to_vir(tcx, t),
                        _ => panic!("unexpected arg to Box/Rc/Arc/Ghost/Tracked"),
                    }
                } else {
                    def_id_to_datatype_typx(tcx, def_id, &path.segments)
                }
            }
            Res::Def(DefKind::Enum, def_id) => def_id_to_datatype_typx(tcx, def_id, &path.segments),
            Res::SelfTy(None, Some((impl_def_id, false))) => {
                return impl_def_id_to_self_ty(tcx, impl_def_id);
            }

            Res::Def(DefKind::TyAlias, def_id) => {
                match &path.segments.last().expect("type must have a segment").args {
                    None => {}
                    Some(_) => {
                        unsupported!(format!(
                            "use of type alias with generic type args here: {:?}",
                            span
                        ));
                    }
                }

                let ty = tcx.type_of(def_id);
                return mid_ty_to_vir(tcx, ty, false);
            }

            _ => {
                unsupported!(format!("type {:#?} {:?} {:?}", kind, path.res, span))
            }
        }),
        _ => {
            unsupported!(format!("type {:#?} {:?}", kind, span))
        }
    }
}

pub(crate) fn typ_of_node<'tcx>(bctx: &BodyCtxt<'tcx>, id: &HirId, allow_mut_ref: bool) -> Typ {
    mid_ty_to_vir(bctx.ctxt.tcx, bctx.types.node_type(*id), allow_mut_ref)
}

pub(crate) fn typ_of_node_expect_mut_ref<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    id: &HirId,
    span: Span,
) -> Result<Typ, VirErr> {
    let ty = bctx.types.node_type(*id);
    if let TyKind::Ref(_, _tys, rustc_ast::Mutability::Mut) = ty.kind() {
        Ok(mid_ty_to_vir(bctx.ctxt.tcx, ty, true))
    } else {
        err_span_str(span, "a mutable reference is expected here")
    }
}

pub(crate) fn implements_structural<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: &'tcx rustc_middle::ty::TyS<'tcx>,
) -> bool {
    let structural_def_id = tcx
        .get_diagnostic_item(rustc_span::Symbol::intern("builtin::Structural"))
        .expect("structural trait is not defined");
    let substs_ref = tcx.mk_substs([].iter());
    let ty_impls_structural = tcx.infer_ctxt().enter(|infcx| {
        infcx
            .type_implements_trait(
                structural_def_id,
                ty,
                substs_ref,
                rustc_middle::ty::ParamEnv::empty(),
            )
            .must_apply_modulo_regions()
    });
    ty_impls_structural
}

// Do equality operations on these operands translate into the SMT solver's == operation?
pub(crate) fn is_smt_equality<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    _span: Span,
    id1: &HirId,
    id2: &HirId,
) -> bool {
    let (t1, t2) = (typ_of_node(bctx, id1, false), typ_of_node(bctx, id2, false));
    match (&*t1, &*t2) {
        (TypX::Bool, TypX::Bool) => true,
        (TypX::Int(_), TypX::Int(_)) => true,
        (TypX::Datatype(..), TypX::Datatype(..)) if types_equal(&t1, &t2) => {
            let ty = bctx.types.node_type(*id1);
            implements_structural(bctx.ctxt.tcx, &ty)
        }
        _ => false,
    }
}

// Do arithmetic operations on these operands translate into the SMT solver's <=, +, =>, etc.?
// (possibly with clipping/wrapping for finite-size integers?)
pub(crate) fn is_smt_arith<'tcx>(bctx: &BodyCtxt<'tcx>, id1: &HirId, id2: &HirId) -> bool {
    match (&*typ_of_node(bctx, id1, false), &*typ_of_node(bctx, id2, false)) {
        (TypX::Bool, TypX::Bool) => true,
        (TypX::Int(_), TypX::Int(_)) => true,
        _ => false,
    }
}

pub(crate) fn check_generic_bound<'tcx>(
    tcx: TyCtxt<'tcx>,
    span: Span,
    bound: &'tcx GenericBound<'tcx>,
) -> Result<vir::ast::GenericBound, VirErr> {
    match bound {
        GenericBound::Trait(
            PolyTraitRef { bound_generic_params: [], trait_ref, span: _ },
            TraitBoundModifier::None,
        ) => {
            let path = &trait_ref.path;
            let def_id = match path.res {
                rustc_hir::def::Res::Def(_, def_id) => def_id,
                _ => return unsupported_err!(span, "generic bounds"),
            };
            if Some(def_id) == tcx.lang_items().fn_trait() {
                let args = &path.segments.last().expect("last segment").args.expect("GenericArgs");
                unsupported_err_unless!(args.args.len() == 1, span, "generic bounds");
                unsupported_err_unless!(args.bindings.len() == 1, span, "generic bounds");
                unsupported_err_unless!(
                    args.bindings[0].gen_args.args.len() == 0,
                    span,
                    "generic bounds"
                );
                let t_args = match &args.args[0] {
                    rustc_hir::GenericArg::Type(t) => ty_to_vir(tcx, &t),
                    _ => panic!("unexpected arg to Fn"),
                };
                let t_ret = match &args.bindings[0].kind {
                    rustc_hir::TypeBindingKind::Equality { ty } => ty_to_vir(tcx, ty),
                    _ => panic!("unexpected arg to Fn"),
                };
                let args = match &*t_args {
                    TypX::Tuple(args) => args.clone(),
                    _ => panic!("unexpected arg to Fn"),
                };
                Ok(Arc::new(GenericBoundX::FnSpec(args, t_ret)))
            } else if Some(def_id) == tcx.lang_items().sized_trait()
                || Some(def_id) == tcx.lang_items().copy_trait()
                || Some(def_id) == tcx.lang_items().unpin_trait()
                || Some(def_id) == tcx.lang_items().sync_trait()
                || Some(def_id) == tcx.get_diagnostic_item(rustc_span::sym::Send)
            {
                // Rust language marker traits are ignored in VIR
                Ok(Arc::new(GenericBoundX::Traits(vec![])))
            } else {
                let typx = def_id_to_datatype_typx(tcx, def_id, &path.segments);
                if let TypX::Datatype(trait_name, _args) = typx {
                    Ok(Arc::new(GenericBoundX::Traits(vec![trait_name])))
                } else {
                    panic!("unexpected trait bound");
                }
            }
        }
        _ => {
            unsupported_err!(span, "generic bounds")
        }
    }
}

pub(crate) fn check_generics_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    generics: &'tcx Generics<'tcx>,
    check_that_external_body_datatype_declares_positivity: bool,
) -> Result<Vec<(vir::ast::Ident, vir::ast::GenericBound, bool)>, VirErr> {
    let Generics { params, where_clause, span: _ } = generics;
    let mut typ_params: Vec<(vir::ast::Ident, vir::ast::GenericBound, bool)> = Vec::new();
    for param in params.iter() {
        let vattrs = get_verifier_attrs(tcx.hir().attrs(param.hir_id))?;
        let neg = vattrs.maybe_negative;
        let pos = vattrs.strictly_positive;
        if neg && pos {
            return err_span_str(
                param.span,
                "type parameter cannot be both maybe_negative and strictly_positive",
            );
        }
        let strictly_positive = !neg; // strictly_positive is the default
        let GenericParam { hir_id: _, name, bounds, span, pure_wrt_drop, kind } = param;

        if let GenericParamKind::Type { .. } = kind {
            if check_that_external_body_datatype_declares_positivity && !neg && !pos {
                return err_span_str(
                    param.span,
                    "in external_body datatype, each type parameter must be either #[verifier(maybe_negative)] or #[verifier(strictly_positive)] (maybe_negative is always safe to use)",
                );
            }
        }

        unsupported_err_unless!(!pure_wrt_drop, *span, "generic pure_wrt_drop");
        match (name, kind) {
            (ParamName::Plain(id), GenericParamKind::Type { default: None, synthetic: false }) => {
                // lifetime bounds can be ignored for VIR, since they are only relevant
                // for rustc's borrow-checking pass
                let bounds: Vec<&GenericBound> =
                    bounds.iter().filter(|bound| !is_lifetime_bound(bound)).collect();

                // trait/function bounds
                let ident = Arc::new(id.name.as_str().to_string());
                let mut trait_bounds: Vec<Path> = Vec::new();
                let mut fn_bounds: Vec<vir::ast::GenericBound> = Vec::new();
                for bound in bounds {
                    let vir_bound = check_generic_bound(tcx, *span, bound)?;
                    match &*vir_bound {
                        GenericBoundX::Traits(ts) => {
                            trait_bounds.extend(ts.clone());
                        }
                        GenericBoundX::FnSpec(..) => fn_bounds.push(vir_bound),
                    }
                }
                unsupported_err_unless!(fn_bounds.len() <= 1, *span, "multiple function bounds");
                unsupported_err_unless!(
                    fn_bounds.len() == 0 || trait_bounds.len() == 0,
                    *span,
                    "combined trait/function bounds"
                );
                let bound = if fn_bounds.len() == 1 {
                    fn_bounds[0].clone()
                } else {
                    Arc::new(GenericBoundX::Traits(trait_bounds))
                };
                typ_params.push((ident, bound, strictly_positive));
            }
            (
                ParamName::Plain(_id),
                GenericParamKind::Lifetime { kind: LifetimeParamKind::Explicit },
            ) => {}
            (
                ParamName::Fresh(_),
                GenericParamKind::Lifetime { kind: LifetimeParamKind::Elided },
            ) => {}
            _ => unsupported_err!(*span, "complex generics", generics),
        }
    }
    unsupported_err_unless!(where_clause.predicates.len() == 0, generics.span, "where clause");
    Ok(typ_params)
}

pub(crate) fn check_generics_bounds_fun<'tcx>(
    tcx: TyCtxt<'tcx>,
    generics: &'tcx Generics<'tcx>,
) -> Result<TypBounds, VirErr> {
    Ok(Arc::new(
        check_generics_bounds(tcx, generics, false)?.into_iter().map(|(a, b, _)| (a, b)).collect(),
    ))
}

pub(crate) fn is_lifetime_bound(bound: &GenericBound) -> bool {
    match bound {
        GenericBound::Trait(..) => false,
        GenericBound::LangItemTrait(..) => false,
        GenericBound::Outlives(..) => true,
    }
}
