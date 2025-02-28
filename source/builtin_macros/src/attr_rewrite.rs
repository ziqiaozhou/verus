/// Macros defined in this module enables developers to annotate Rust code in
/// standard Rust code, eliminating the need to wrap exec code inside `verus!
/// {}`.
///
/// Usage:
/// - Items (struct, const) used for verification need to be annotated
///   with `#[verus_verify].
/// - Functions used for verification need to be annotated with `#[verus_spec ...]`
///   or `#[verus_spec pattern => ...]`
///   where ... is a block of requires, ensures, decreases, etc. in the verus! syntax
/// - To apply `ensures`, `invariant`, `decreases` in `exec`,
///   developers should call the corresponding macros at the beginning of the loop
/// - To use proof block, add proof!{...} inside function body.
///
/// Rationale:
/// - This approach avoids introducing new syntax into existing Rust executable
///   code, allowing verification and non-verification developers to collaborate
///   without affecting each other.
///   Thus, this module uses syn instead of syn_verus in most cases.
///   For developers who do not understand verification, they can easily ignore
///   verus code via feature/cfg selection and use standard rust tools like
///   `rustfmt` and `rust-analyzer`.
///
/// Limitations:
/// - #[verus_verify] does not support all `verus` syntax, particularly
///   those constructs not accepted by `rustc`.
/// - For defining complex `verus` specifications or proof functions, developers
///   should still use `verus! {}`.
/// - Use of tracked variable is possible but in a different style.
///
/// Example:
/// - Refer to `example/syntax_attr.rs`.
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::{parse2, spanned::Spanned, Expr, ExprCall, Item, Stmt};

use crate::{
    attr_block_trait::{AnyAttrBlock, AnyFnOrLoop},
    syntax,
    syntax::mk_verus_attr_syn,
    EraseGhost,
};

pub fn rewrite_verus_attribute(
    erase: &EraseGhost,
    attr_args: Vec<syn::Ident>,
    input: TokenStream,
) -> TokenStream {
    if erase.keep() {
        let item: Item = parse2(input).expect("#[verus_verify] must be applied to an item");
        let mut attributes = Vec::new();
        const VERIFIER_ATTRS: [&str; 2] = ["external", "external_body"];
        for arg in attr_args {
            if VERIFIER_ATTRS.contains(&arg.to_string().as_str()) {
                attributes.push(mk_verus_attr_syn(arg.span(), quote! { #arg }));
            } else {
                let span = arg.span();
                return proc_macro2::TokenStream::from(quote_spanned!(span =>
                    compile_error!("unsupported parameters {:?} in #[verus_verify(...)]");
                ));
            }
        }
        if attributes.len() == 0 {
            attributes.push(mk_verus_attr_syn(item.span(), quote! { verus_macro }));
        }

        quote_spanned! {item.span()=>
            #(#attributes)*
            #item
        }
    } else {
        input
    }
}

pub fn rewrite_verus_spec(
    erase: EraseGhost,
    outer_attr_tokens: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let f = match syn::parse::<AnyFnOrLoop>(input) {
        Ok(f) => f,
        Err(err) => {
            // Make sure at least one error is reported, just in case Rust parses the function
            // successfully but syn fails to parse it.
            // (In the normal case, this results in a redundant extra error message after
            // the normal Rust syntax error, but it's a reasonable looking error message.)
            return proc_macro::TokenStream::from(
                quote_spanned!(err.span() => compile_error!("Misuse of #[verus_spec]");),
            );
        }
    };

    match f {
        AnyFnOrLoop::Fn(mut fun) => {
            let spec_attr =
                syn_verus::parse_macro_input!(outer_attr_tokens as syn_verus::SignatureSpecAttr);
            // Note: trait default methods appear in this case,
            // since they look syntactically like non-trait functions
            let spec_stmts = syntax::sig_specs_attr(erase, spec_attr, &mut fun.sig);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            let _ = fun.block_mut().unwrap().stmts.splice(0..0, new_stmts);
            fun.attrs.push(mk_verus_attr_syn(fun.span(), quote! { verus_macro }));

            proc_macro::TokenStream::from(fun.to_token_stream())
        }
        AnyFnOrLoop::TraitMethod(mut method) => {
            let spec_attr =
                syn_verus::parse_macro_input!(outer_attr_tokens as syn_verus::SignatureSpecAttr);
            // Note: default trait methods appear in the AnyFnOrLoop::Fn case, not here
            let spec_stmts = syntax::sig_specs_attr(erase, spec_attr, &mut method.sig);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            let mut spec_fun_opt = syntax::split_trait_method_syn(&method, erase.erase());
            let spec_fun = spec_fun_opt.as_mut().unwrap_or(&mut method);
            let _ = spec_fun.block_mut().unwrap().stmts.splice(0..0, new_stmts);
            method.attrs.push(mk_verus_attr_syn(method.span(), quote! { verus_macro }));
            let mut new_stream = TokenStream::new();
            spec_fun_opt.to_tokens(&mut new_stream);
            method.to_tokens(&mut new_stream);
            proc_macro::TokenStream::from(new_stream)
        }
        AnyFnOrLoop::ForLoop(forloop) => {
            let spec_attr = syn_verus::parse_macro_input!(outer_attr_tokens as syn_verus::LoopSpec);
            syntax::for_loop_spec_attr(erase, spec_attr, forloop).to_token_stream().into()
        }
        AnyFnOrLoop::Loop(mut l) => {
            let spec_attr = syn_verus::parse_macro_input!(outer_attr_tokens as syn_verus::LoopSpec);
            let spec_stmts = syntax::while_loop_spec_attr(erase, spec_attr);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            if erase.keep() {
                l.body.stmts.splice(0..0, new_stmts);
            }
            l.to_token_stream().into()
        }
        AnyFnOrLoop::While(mut l) => {
            let spec_attr = syn_verus::parse_macro_input!(outer_attr_tokens as syn_verus::LoopSpec);
            let spec_stmts = syntax::while_loop_spec_attr(erase, spec_attr);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            if erase.keep() {
                l.body.stmts.splice(0..0, new_stmts);
            }
            l.to_token_stream().into()
        }
    }
}

pub fn proof_rewrite(erase: EraseGhost, input: TokenStream) -> proc_macro::TokenStream {
    if erase.keep() {
        let block: TokenStream =
            syntax::proof_block(erase, quote_spanned!(input.span() => {#input}).into()).into();
        quote! {
            #[verifier::proof_block]
            {
                #[verus::internal(const_header_wrapper)]||#block;
            }
        }
        .into()
    } else {
        proc_macro::TokenStream::new()
    }
}

struct StmtOrExpr(pub Stmt);

impl syn::parse::Parse for StmtOrExpr {
    fn parse(input: syn::parse::ParseStream) -> syn::parse::Result<StmtOrExpr> {
        use syn::parse::discouraged::Speculative;
        let fork = input.fork();
        if let Ok(stmt) = fork.parse() {
            input.advance_to(&fork);
            return Ok(StmtOrExpr(stmt));
        }

        let expr: Expr = input.parse().expect("Need stmt or expression");
        return Ok(StmtOrExpr(Stmt::Expr(expr, None)));
    }
}

pub(crate) fn verus_io(
    erase: &EraseGhost,
    attr_input: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> Result<proc_macro::TokenStream, syn::Error> {
    if !erase.keep() {
        return Ok(input);
    }
    println!("{}", input);
    let StmtOrExpr(s) = syn::parse::<StmtOrExpr>(input).expect("failed to parse Stmt verusio");
    let with_in_out = syn_verus::parse::<syn_verus::CallWithSpec>(attr_input)
        .expect("failed to parse syn_verus::TrackedIO");
    let ret = call_with_in_out(erase, s, with_in_out).into();
    println!("{}", ret);
    Ok(ret)
}

// Return some pre-statements
fn expr_call_with_inputs<ExtraArgs: IntoIterator<Item = syn_verus::Expr>>(
    erase: &EraseGhost,
    e: &mut Expr,
    extra_args: ExtraArgs,
    pat: Option<(syn_verus::Pat, syn_verus::Pat)>, // new_pat, old_pat
) {
    match e {
        Expr::Call(ExprCall { args, .. }) => {
            for arg in extra_args {
                let arg =
                    syntax::rewrite_expr(erase.clone(), false, arg.into_token_stream().into());
                args.push(syn::Expr::Verbatim(arg.into()));
            }
        }
        Expr::MethodCall(syn::ExprMethodCall { args, .. }) => {
            for arg in extra_args {
                let arg =
                    syntax::rewrite_expr(erase.clone(), false, arg.into_token_stream().into());
                args.push(syn::Expr::Verbatim(arg.into()));
            }
        }
        _ => {
            panic!("(with ...) cannot be applied to non-call expr")
        }
    }

    if let Some((mut pat, out_pat)) = pat {
        let (_, x_assigns) = syntax::rewrite_exe_pat(&mut pat);
        *e = syn::Expr::Verbatim(quote_spanned! {e.span() => {
            let #pat = #e;
            proof!{#(#x_assigns)*}
            #out_pat
        }})
    }
}

fn call_with_in_out(
    erase: &EraseGhost,
    s: Stmt,
    with_in_out: syn_verus::CallWithSpec,
) -> TokenStream {
    let syn_verus::CallWithSpec { inputs, outputs, follows, .. } = with_in_out;
    if inputs.len() == 0 && outputs.is_none() && follows.is_none() {
        return s.into_token_stream();
    }
    let follows: Option<TokenStream> = follows.map(|(_, f)| {
        syntax::rewrite_expr(erase.clone(), false, f.into_token_stream().into()).into()
    });
    let tmp_pat = syn_verus::Pat::Ident(syn_verus::PatIdent {
        attrs: vec![],
        by_ref: None,
        mutability: None,
        ident: syn_verus::Ident::new("__verus_tmp_var_", s.span()),
        subpat: None,
    });
    let mk_new_pat = |old_pat: syn_verus::Pat| {
        if let Some((_, extra_pat)) = outputs {
            let mut elems =
                syn_verus::punctuated::Punctuated::<syn_verus::Pat, syn_verus::Token![,]>::new();
            elems.push(old_pat);
            elems.push(extra_pat);
            syn_verus::Pat::Tuple(syn_verus::PatTuple {
                attrs: vec![],
                paren_token: syn_verus::token::Paren::default(),
                elems,
            })
        } else {
            old_pat
        }
    };
    let mut s = s;
    match &mut s {
        Stmt::Local(syn::Local { pat, init, .. }) => match init {
            Some(syn::LocalInit { expr, .. }) => {
                if follows.is_some() {
                    return proc_macro2::TokenStream::from(quote_spanned!(s.span() =>
                        compile_error!("with attribute is misused");
                    ));
                }
                let mut new_pat = mk_new_pat(syn_verus::Pat::Verbatim(pat.into_token_stream()));
                let (x_declares, x_assigns) = syntax::rewrite_exe_pat(&mut new_pat);
                *pat = syn::Pat::Verbatim(new_pat.into_token_stream());
                expr_call_with_inputs(erase, expr, inputs, None);
                quote! {
                    #(#x_declares)*
                    #s
                    proof!{#(#x_assigns)*}
                }
                .into()
            }
            _ => {
                return proc_macro2::TokenStream::from(quote_spanned!(s.span() =>
                    compile_error!("with attribute cannot be applied to a local without init");
                ));
            }
        },
        Stmt::Expr(expr, _) => {
            let mut pat = mk_new_pat(tmp_pat.clone());
            if matches!(expr, Expr::Call(_) | Expr::MethodCall(_)) {
                expr_call_with_inputs(erase, expr, inputs, Some((pat, tmp_pat)));
            }
            if let Some(follow) = follows {
                *expr = Expr::Verbatim(quote_spanned!(expr.span() => (#expr, #follow)));
            }
            s.into_token_stream()
        }
        _ => {
            println!("here2");
            return proc_macro2::TokenStream::from(quote_spanned!(s.span() =>
                compile_error!("with attribute cannot be applied here");
            ));
        }
    }
}
