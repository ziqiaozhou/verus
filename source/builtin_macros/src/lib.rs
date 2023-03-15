#![feature(box_patterns)]
#![feature(proc_macro_span)]
#![feature(proc_macro_tracked_env)]

use synstructure::{decl_attribute, decl_derive};
mod fndecl;
mod is_variant;
mod rustdoc;
mod struct_decl_inv;
mod structural;
mod syntax;
mod topological_sort;

decl_derive!([Structural] => structural::derive_structural);

decl_attribute!([is_variant] => is_variant::attribute_is_variant);

// Proc macros must reside at the root of the crate
#[proc_macro]
pub fn fndecl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    proc_macro::TokenStream::from(fndecl::fndecl(proc_macro2::TokenStream::from(input)))
}

#[proc_macro]
pub fn verus(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, true, true)
    /*
    let c = syntax::rewrite_items(input, true, true);
    use std::io::Write;
    unsafe {
        let mut file = std::fs::File::create(".verus-gen/verus-".to_owned()+ &COUNT.to_string()+ ".rs").expect("create failed");
        writeln!(&mut file, "{}", c).unwrap();
        COUNT = COUNT + 1;
    }
    c*/
}

#[proc_macro_attribute]
pub fn verus_fn(_attribute: proc_macro::TokenStream, item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // Parse the input tokens into a syntax tree.
    let c = syntax::rewrite_fn_item(item, true, true);
    c
}

#[proc_macro]
pub fn verus_old_todo_replace_this(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, false, true)
}

#[proc_macro]
pub fn verus_old_todo_no_ghost_blocks(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, true, false)
}

#[proc_macro]
pub fn verus_proof_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(true, input)
}

#[proc_macro]
pub fn verus_exec_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(false, input)
}

/// verus_proof_macro_exprs!(f!(exprs)) applies verus syntax to transform exprs into exprs',
/// then returns f!(exprs'),
/// where exprs is a sequence of expressions separated by ",", ";", and/or "=>".
#[proc_macro]
pub fn verus_proof_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_exprs(true, input)
}

#[proc_macro]
pub fn verus_exec_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_exprs(false, input)
}

#[proc_macro]
pub fn struct_with_invariants(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    struct_decl_inv::struct_decl_inv(input)
}
