#![cfg_attr(
    verus_keep_ghost,
    feature(proc_macro_span),
    feature(proc_macro_tracked_env),
    feature(proc_macro_quote),
    feature(proc_macro_expand),
    feature(proc_macro_diagnostic)
)]

#[cfg(verus_keep_ghost)]
use std::sync::OnceLock;
use synstructure::{decl_attribute, decl_derive};

#[macro_use]
mod syntax;
mod atomic_ghost;
mod attr_block_trait;
mod attr_rewrite;
mod calc_macro;
mod enum_synthesize;
mod fndecl;
mod is_variant;
mod rustdoc;
mod struct_decl_inv;
mod structural;
mod topological_sort;

decl_derive!([Structural] => structural::derive_structural);

decl_attribute!([is_variant] => is_variant::attribute_is_variant);
decl_attribute!([is_variant_no_deprecation_warning] => is_variant::attribute_is_variant_no_deprecation_warning);

#[proc_macro_attribute]
pub fn verus_enum_synthesize(
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    enum_synthesize::attribute_verus_enum_synthesize(&cfg_erase(), attr, input)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum EraseGhost {
    /// keep all ghost code
    Keep,
    /// erase ghost code, but leave ghost stubs
    Erase,
    /// erase all ghost code
    EraseAll,
}

impl EraseGhost {
    fn keep(&self) -> bool {
        match self {
            EraseGhost::Keep => true,
            EraseGhost::Erase | EraseGhost::EraseAll => false,
        }
    }

    fn erase(&self) -> bool {
        match self {
            EraseGhost::Keep => false,
            EraseGhost::Erase | EraseGhost::EraseAll => true,
        }
    }

    fn erase_all(&self) -> bool {
        match self {
            EraseGhost::Keep | EraseGhost::Erase => false,
            EraseGhost::EraseAll => true,
        }
    }
}

// Proc macros must reside at the root of the crate
#[proc_macro]
pub fn fndecl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    proc_macro::TokenStream::from(fndecl::fndecl(proc_macro2::TokenStream::from(input)))
}

#[proc_macro]
pub fn verus_keep_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, EraseGhost::Keep, true)
}

#[proc_macro]
pub fn verus_erase_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, EraseGhost::Erase, true)
}

#[proc_macro]
pub fn verus(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, cfg_erase(), true)
}

#[proc_macro]
pub fn verus_proof_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(EraseGhost::Keep, true, input)
}

#[proc_macro]
pub fn verus_exec_expr_keep_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(EraseGhost::Keep, false, input)
}

#[proc_macro]
pub fn verus_exec_expr_erase_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(EraseGhost::Keep, false, input)
}

#[proc_macro]
pub fn verus_exec_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(cfg_erase(), false, input)
}

#[cfg(verus_keep_ghost)]
pub(crate) fn cfg_erase() -> EraseGhost {
    let ts: proc_macro::TokenStream = quote::quote! { ::core::cfg!(verus_keep_ghost_body) }.into();
    let ts_stubs: proc_macro::TokenStream = quote::quote! { ::core::cfg!(verus_keep_ghost) }.into();
    let (bool_ts, bool_ts_stubs) = match (ts.expand_expr(), ts_stubs.expand_expr()) {
        (Ok(name), Ok(name_stubs)) => (name.to_string(), name_stubs.to_string()),
        _ => {
            panic!("cfg_erase call failed")
        }
    };
    match (bool_ts.as_str(), bool_ts_stubs.as_str()) {
        ("true", "true" | "false") => EraseGhost::Keep,
        ("false", "true") => EraseGhost::Erase,
        ("false", "false") => EraseGhost::EraseAll,
        _ => {
            panic!("cfg_erase call failed")
        }
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) fn cfg_erase() -> EraseGhost {
    EraseGhost::EraseAll
}

#[cfg(verus_keep_ghost)]
pub(crate) fn cfg_verify_core() -> bool {
    static CFG_VERIFY_CORE: OnceLock<bool> = OnceLock::new();
    *CFG_VERIFY_CORE.get_or_init(|| {
        let ts: proc_macro::TokenStream = quote::quote! { ::core::cfg!(verus_verify_core) }.into();
        let bool_ts = match ts.expand_expr() {
            Ok(name) => name.to_string(),
            _ => {
                panic!("cfg_verify_core call failed")
            }
        };
        match bool_ts.as_str() {
            "true" => true,
            "false" => false,
            _ => {
                panic!("cfg_verify_core call failed")
            }
        }
    })
}

// Because 'expand_expr' is unstable, we need a different impl when `not(verus_keep_ghost)`.
#[cfg(not(verus_keep_ghost))]
pub(crate) fn cfg_verify_core() -> bool {
    false
}

#[cfg(verus_keep_ghost)]
pub(crate) fn cfg_verify_vstd() -> bool {
    static CFG_VERIFY_VSTD: OnceLock<bool> = OnceLock::new();
    *CFG_VERIFY_VSTD.get_or_init(|| {
        let ts: proc_macro::TokenStream = quote::quote! { ::core::module_path!() }.into();
        let str_ts = match ts.expand_expr() {
            Ok(name) => name.to_string(),
            _ => {
                panic!("cfg_verify_core call failed")
            }
        };
        str_ts.starts_with("\"vstd::")
    })
}

// For not(verus_keep_ghost), we can't use the ideal implementation (above). The following works
// as long as IS_VSTD is set whenever it's necessary. If we fail to set it, then
// the CI should fail to build Verus.

static IS_VSTD: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

#[cfg(not(verus_keep_ghost))]
pub(crate) fn cfg_verify_vstd() -> bool {
    IS_VSTD.load(std::sync::atomic::Ordering::Relaxed)
}

/// verus_proof_macro_exprs!(f!(exprs)) applies verus syntax to transform exprs into exprs',
/// then returns f!(exprs'),
/// where exprs is a sequence of expressions separated by ",", ";", and/or "=>".
#[proc_macro]
pub fn verus_proof_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_exprs(EraseGhost::Keep, true, input)
}

#[proc_macro]
pub fn verus_exec_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_exprs(cfg_erase(), false, input)
}

// This is for expanding the body of an open_*_invariant in exec mode
#[proc_macro]
pub fn verus_exec_inv_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // We pass `treat_elements_as_ghost: false` to treat all elements besides
    // the third ($eexpr) as ghost.
    syntax::inv_macro_exprs(cfg_erase(), false, input)
}

// This is for expanding the body of an open_*_invariant in `proof` mode
#[proc_macro]
pub fn verus_ghost_inv_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // We pass `treat_elements_as_ghost: true` to treat all elements as ghost.
    syntax::inv_macro_exprs(cfg_erase(), true, input)
}

/// `verus_proof_macro_explicit_exprs!(f!(tts))` applies verus syntax to transform `tts` into
/// `tts'`, then returns `f!(tts')`, only applying the transform to any of the exprs within it that
/// are explicitly prefixed with `@@`, leaving the rest as-is. Contrast this to
/// [`verus_proof_macro_exprs`] which is likely what you want to try first to see if it satisfies
/// your needs.
#[proc_macro]
pub fn verus_proof_macro_explicit_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_explicit_exprs(EraseGhost::Keep, true, input)
}

#[proc_macro]
pub fn struct_with_invariants(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    struct_decl_inv::struct_decl_inv(input)
}

#[proc_macro]
pub fn struct_with_invariants_vstd(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    IS_VSTD.store(true, std::sync::atomic::Ordering::Relaxed);
    struct_decl_inv::struct_decl_inv(input)
}

#[proc_macro]
pub fn atomic_with_ghost_helper(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    atomic_ghost::atomic_ghost(input)
}

#[proc_macro]
pub fn calc_proc_macro(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    calc_macro::calc_macro(input)
}

/*** Verus small macro definition for executable items ***/

// If no #[verus_verify] on the item, it is verifier::external by default.
// When compiling code with verus:
// #[verus_verify] annotates the item with verifier::verify
// #[verus_verify(external_body)] annotates the item with verifier::external_body
// When compiling code with standard rust tool, the item has no verifier annotation.
#[proc_macro_attribute]
pub fn verus_verify(
    args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let args = syn::parse_macro_input!(args with syn::punctuated::Punctuated::<syn::Ident, syn::Token![,]>::parse_terminated);
    let args = args.into_iter().collect();
    attr_rewrite::rewrite_verus_attribute(&cfg_erase(), args, input.into()).into()
}

#[proc_macro_attribute]
pub fn verus_spec(
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let erase = cfg_erase();
    if erase.keep() {
        attr_rewrite::rewrite_verus_spec(erase, attr.into(), input.into()).into()
    } else {
        input
    }
}

#[proc_macro]
pub fn proof(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    attr_rewrite::proof_rewrite(cfg_erase(), input.into()).into()
}

#[proc_macro_attribute]
pub fn verus_io(
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let ret = attr_rewrite::verus_io(&cfg_erase(), attr, input)
        .expect("Misuse of #[verus_io()]. Must used on ExprCall");
    //println!("{}", ret);
    ret
}

#[proc_macro]
pub fn verus_extra_stmts(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let erase = cfg_erase();
    if erase.keep() {
        syntax::rewrite_stmt(cfg_erase(), false, input.into())
    } else {
        proc_macro::TokenStream::new()
    }
}

#[proc_macro]
pub fn verus_extra_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let erase = cfg_erase();
    if erase.keep() {
        syntax::rewrite_expr(cfg_erase(), false, input.into())
    } else {
        proc_macro::TokenStream::new()
    }
}

#[proc_macro]
pub fn verus_exec_stmts(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_stmt(cfg_erase(), false, input.into())
}
/*** End of verus small macro definition for executable items ***/
