#![feature(proc_macro_span)]

use synstructure::{decl_attribute, decl_derive};
mod fndecl;
mod is_variant;
mod structural;
mod syntax;

decl_derive!([Structural] => structural::derive_structural);

decl_attribute!([is_variant] => is_variant::attribute_is_variant);

// Proc macros must reside at the root of the crate
#[proc_macro]
pub fn fndecl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    proc_macro::TokenStream::from(fndecl::fndecl(proc_macro2::TokenStream::from(input)))
}

#[proc_macro]
pub fn verus_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let mut state = syntax::ExprState::new();
    let t = proc_macro::TokenStream::from(syntax::rewrite_expr_stream(
        &mut state,
        proc_macro2::TokenStream::from(input),
    ));
    let t = syntax::rewrite_expr(state, t);
    t
}

#[proc_macro]
pub fn verus(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let t = proc_macro::TokenStream::from(syntax::rewrite_items_stream(
        proc_macro2::TokenStream::from(input),
    ));
    t
}
