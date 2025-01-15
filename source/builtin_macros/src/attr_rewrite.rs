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
use core::convert::TryFrom;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::{
    parse::Parse, parse::ParseStream, parse2, spanned::Spanned, Attribute, AttributeArgs, Expr,
    Ident, Item, ReturnType, Stmt,
};

use crate::{
    attr_block_trait::{AnyAttrBlock, AnyFnOrLoop},
    syntax,
    syntax::mk_verus_attr_syn,
    EraseGhost,
};

#[derive(Debug)]
pub enum SpecAttributeKind {
    Requires,
    Ensures,
    Decreases,
    Invariant,
    InvariantExceptBreak,
}

struct SpecAttributeApply {
    pub on_function: bool,
    pub on_loop: bool,
}

type SpecAttrWithArgs = (SpecAttributeKind, TokenStream);

impl SpecAttributeKind {
    fn applies_to(&self) -> SpecAttributeApply {
        let (on_function, on_loop) = match self {
            SpecAttributeKind::Requires => (true, false),
            SpecAttributeKind::Ensures => (true, true),
            SpecAttributeKind::Decreases => (true, true),
            SpecAttributeKind::Invariant => (false, true),
            SpecAttributeKind::InvariantExceptBreak => (false, true),
        };
        SpecAttributeApply { on_function, on_loop }
    }

    fn applies_to_function(&self) -> bool {
        self.applies_to().on_function
    }

    fn applies_to_loop(&self) -> bool {
        self.applies_to().on_loop
    }
}

impl TryFrom<String> for SpecAttributeKind {
    type Error = String;

    fn try_from(name: String) -> Result<Self, Self::Error> {
        match name.as_str() {
            "requires" => Ok(SpecAttributeKind::Requires),
            "ensures" => Ok(SpecAttributeKind::Ensures),
            "decreases" => Ok(SpecAttributeKind::Decreases),
            "invariant" => Ok(SpecAttributeKind::Invariant),
            _ => Err(name),
        }
    }
}

// Add brackets for requires, invariant.
// Add brackets for ensures if it could not be parsed as a syn_verus::Expr.
fn insert_brackets(attr_type: &SpecAttributeKind, tokens: TokenStream) -> TokenStream {
    // Parse the TokenStream into a Syn Expression
    match attr_type {
        SpecAttributeKind::Ensures => {
            // if the tokens are not valid verus expr, it might need a bracket.
            syn_verus::parse2::<syn_verus::Expr>(tokens.clone())
                .map_or(quote! {[#tokens]}, |e| quote! {#e})
        }
        SpecAttributeKind::Decreases => tokens,
        _ => {
            quote! {[#tokens]}
        }
    }
}

fn expand_verus_attribute(
    erase: EraseGhost,
    verus_attrs: Vec<SpecAttrWithArgs>,
    any_with_attr_block: &mut dyn AnyAttrBlock,
    function_or_loop: bool,
) {
    if !erase.keep() {
        return;
    }
    // rewrite based on different spec attributes
    for (attr_kind, attr_tokens) in verus_attrs {
        if function_or_loop {
            assert!(attr_kind.applies_to_function());
        }
        if !function_or_loop {
            assert!(attr_kind.applies_to_loop());
        }
        match attr_kind {
            SpecAttributeKind::Invariant => {
                insert_spec_call(any_with_attr_block, "invariant", attr_tokens)
            }
            SpecAttributeKind::Decreases => {
                insert_spec_call(any_with_attr_block, "decreases", attr_tokens)
            }
            SpecAttributeKind::Ensures => {
                insert_spec_call(any_with_attr_block, "ensures", attr_tokens)
            }
            SpecAttributeKind::Requires => {
                insert_spec_call(any_with_attr_block, "requires", attr_tokens)
            }
            SpecAttributeKind::InvariantExceptBreak => {
                insert_spec_call(any_with_attr_block, "invariant_except_break", attr_tokens)
            }
        }
    }
}

fn insert_spec_call(any_fn: &mut dyn AnyAttrBlock, call: &str, verus_expr: TokenStream) {
    let fname = Ident::new(call, verus_expr.span());
    let tokens: TokenStream =
        syntax::rewrite_expr(EraseGhost::Keep, true, verus_expr.into()).into();
    any_fn.block_mut().unwrap().stmts.insert(
        0,
        parse2(quote! { #[verus::internal(const_header_wrapper)]||{::builtin::#fname(#tokens);};})
            .unwrap(),
    );
}

struct StmtOrExpr(pub Stmt);

impl Parse for StmtOrExpr {
    fn parse(input: ParseStream) -> syn::parse::Result<StmtOrExpr> {
        use syn::parse::discouraged::Speculative;
        let fork = input.fork();
        if let Ok(stmt) = fork.parse() {
            input.advance_to(&fork);
            return Ok(StmtOrExpr(stmt));
        }

        let expr: Expr = input.parse().expect("Need stmt or expression");
        return Ok(StmtOrExpr(Stmt::Expr(expr)));
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
    let mut s = syn::parse::<StmtOrExpr>(input).expect("failed to parse StmtOrExpr").0;
    let tracked_in_out = syn_verus::parse::<syn_verus::TrackedIO>(attr_input)
        .expect("failed to parse syn_verus::TrackedIO");
    tracks_stmt_in_out(&mut s, tracked_in_out).map(|t| t.into())
}

fn tracks_stmt_in_out(
    s: &mut Stmt,
    tracked_in_out: syn_verus::TrackedIO,
) -> syn::Result<proc_macro::TokenStream> {
    let mut pre_stmts = Vec::new();
    let syn_verus::TrackedIO { input, out } = tracked_in_out;
    if input.is_none() && out.is_none() {
        return Ok(quote! {#s}.into());
    }
    let span = s.span();

    let tracked_in_out = syn_verus::TrackedIO { input, out: None };
    let mut x_assigns = Vec::new();
    let tmp_var = Ident::new("_verus_tmp_var_", span);

    let out_pat: Option<syn::Pat> = match out {
        Some((_, out_vars)) => {
            let out_vars = out_vars.into_iter();
            let mut out_pat: syn_verus::Pat = syn_verus::parse2(quote_spanned!(
                span => (#tmp_var #(, #out_vars)*)))
            .expect("invalid Pat");
            (_, x_assigns) = syntax::rewrite_exe_pat(&mut out_pat);
            Some(parse2(quote! {#out_pat})?)
        }
        _ => None,
    };
    match s {
        Stmt::Local(syn::Local { pat, init, .. }) => {
            match init {
                Some((_, expr)) => {
                    pre_stmts.extend(tracks_expr_in_out(expr, tracked_in_out, None, &tmp_var)?);
                }
                _ => {}
            }
            match out_pat {
                Some(p) => {
                    *pat = p;
                }
                _ => {}
            }
        }
        Stmt::Expr(e) => {
            pre_stmts.extend(tracks_expr_in_out(e, tracked_in_out, out_pat, &tmp_var)?);
            // s must be in the end.
            return Ok(quote! {{#(#pre_stmts)* proof!{#(#x_assigns)*} #s}}.into());
        }
        Stmt::Semi(e, ..) => {
            pre_stmts.extend(tracks_expr_in_out(e, tracked_in_out, out_pat, &tmp_var)?);
        }
        _ => {
            unimplemented!("item not supported")
        }
    }
    Ok(quote! {#(#pre_stmts)* #s proof!{#(#x_assigns)*}}.into())
}

fn tracks_expr_in_out(
    e: &mut Expr,
    tracked_in_out: syn_verus::TrackedIO,
    out_pat: Option<syn::Pat>,
    tmp_var: &Ident,
) -> syn::Result<Vec<Stmt>> {
    let mut pre_stmts = Vec::new();
    let syn_verus::TrackedIO { input, out } = tracked_in_out;
    if input.is_none() && out.is_none() {
        return Ok(pre_stmts);
    }
    let erase = EraseGhost::Keep;
    let extra_inputs: Vec<Expr> = match &input {
        Some(i) => i
            .into_iter()
            .map(|c| {
                let e = syntax::create_tracked_ghost_vars(
                    &erase,
                    syntax::is_tracked_or_ghost_call(&c).expect("Tracked or Ghost"),
                    false,
                    c.span(),
                    c.args[0].clone(),
                );
                Expr::Verbatim(quote! {#e})
            })
            .collect(),
        _ => Vec::new(),
    };
    match e {
        Expr::MethodCall(call) => {
            call.args.extend(extra_inputs);
            //insert_arguments_to_call(&mut call.args, inputs, true)?;
            match out_pat {
                Some(pat) => {
                    pre_stmts.push(parse2(quote_spanned! {call.span() => let #pat = #call;})?);
                    *e = Expr::Verbatim(quote_spanned! {
                        call.span() => #tmp_var
                    });
                }
                _ => {}
            }
        }
        Expr::Call(call) => {
            call.args.extend(extra_inputs);
            match out_pat {
                Some(pat) => {
                    pre_stmts.push(parse2(quote_spanned! {call.span() => let #pat = #call;})?);
                    *e = Expr::Verbatim(quote_spanned! {
                        call.span() => #tmp_var
                    });
                }
                _ => {}
            }
        }
        Expr::Assign(syn::ExprAssign { left, right, .. }) => {
            pre_stmts.extend(tracks_expr_in_out(
                right,
                syn_verus::TrackedIO { input, out: None },
                None,
                tmp_var,
            )?);
            match out_pat {
                Some(pat) => {
                    pre_stmts.push(parse2(quote_spanned! {right.span() =>  let #pat = #right;})?);
                    *e = Expr::Verbatim(quote_spanned!(left.span() =>
                        #left = #tmp_var
                    ));
                }
                _ => {}
            }
        }
        _ => return Err(syn::Error::new(e.span(), "expected ExprMethodCall or ExprCall")),
    }
    Ok(pre_stmts)
}

pub fn rewrite_verus_attribute(
    erase: &EraseGhost,
    attr_args: AttributeArgs,
    input: TokenStream,
) -> TokenStream {
    if erase.keep() {
        let item: Item = parse2(input).expect("#[verus_verify] must be applied to an item");
        let mut attributes: Vec<Attribute> = vec![];
        const VERIFIER_ATTRS: [&str; 2] = ["external", "external_body"];
        for arg in attr_args {
            if let syn::NestedMeta::Meta(m) = arg {
                if VERIFIER_ATTRS.contains(&m.to_token_stream().to_string().as_str()) {
                    attributes.push(mk_verus_attr_syn(m.span(), quote! { #m }));
                } else {
                    panic!(
                        "unsupported parameters {:?} in #[verus_verify(...)]",
                        m.to_token_stream().to_string()
                    );
                }
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

pub fn rewrite_sig_verus_spec(
    spec_attr: syn_verus::SignatureSpecAttr,
    sig: &mut syn::Signature,
) -> Vec<Stmt> {
    let erase = EraseGhost::Keep;
    // Note: trait default methods appear in this case,
    // since they look syntactically like non-trait functions
    let ret = if let Some(r) = &spec_attr.spec.return_tracks {
        r.args
            .iter()
            .map(|arg| {
                if let syn_verus::FnArgKind::Typed(p) = &arg.kind {
                    p.ty.clone()
                } else {
                    panic!("Must be PatType")
                }
            })
            .collect()
    } else {
        Vec::new()
    };
    if ret.len() > 0 {
        match &mut sig.output {
            ReturnType::Default => {
                if ret.len() > 0 {
                    let ty = parse2(quote_spanned!(
                        sig.output.span() => (() #(,#ret)*)
                    ))
                    .expect("failed parse new output type");
                    sig.output = ReturnType::Type(syn::token::RArrow::default(), ty);
                }
            }
            ReturnType::Type(_, ty) => {
                if ret.len() > 0 {
                    *ty = parse2(quote_spanned!(
                        ty.span() => (#ty #(,#ret)*)
                    ))
                    .expect("failed parse new output type");
                }
            }
        }
    }
    let mut spec_attr = spec_attr;
    let tracks = spec_attr.spec.tracks;
    spec_attr.spec.tracks = None;
    let mut spec_stmts: Vec<syn_verus::Stmt> = Vec::new();
    if let Some(syn_verus::Tracks { mut args, .. }) = tracks {
        for arg in args.iter_mut() {
            spec_stmts.extend(syntax::sig_update_track_ghost(&erase, arg, false));
        }
        sig.inputs.extend(
            args.into_iter()
                .map(|a| a.kind)
                .map(|k| parse2::<syn::FnArg>(quote! { #k }).expect("takes more args")),
        );
    }
    spec_stmts.extend(syntax::sig_specs_attr(erase, spec_attr, sig));
    spec_stmts
        .into_iter()
        .map(|s| parse2(quote! { #s }).expect(format!("spec to new stmts {:?}", s).as_str()))
        .collect()
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
                quote_spanned!(err.span() => compile_error!("syntax error in function");),
            );
        }
    };
    let spec_attr =
        syn_verus::parse_macro_input!(outer_attr_tokens as syn_verus::SignatureSpecAttr);

    match f {
        AnyFnOrLoop::Fn(mut fun) => {
            let new_stmts = rewrite_sig_verus_spec(spec_attr, &mut fun.sig);
            fun.block_mut().unwrap().stmts.splice(0..0, new_stmts);
            fun.attrs.push(mk_verus_attr_syn(fun.span(), quote! { verus_macro }));
            proc_macro::TokenStream::from(fun.to_token_stream())
        }
        AnyFnOrLoop::TraitMethod(mut method) => {
            // Note: default trait methods appear in the AnyFnOrLoop::Fn case, not here
            let new_stmts = rewrite_sig_verus_spec(spec_attr, &mut method.sig);
            let mut spec_fun_opt = syntax::split_trait_method_syn(&method, erase.erase());
            let spec_fun = spec_fun_opt.as_mut().unwrap_or(&mut method);
            let _ = spec_fun.block_mut().unwrap().stmts.splice(0..0, new_stmts);
            method.attrs.push(mk_verus_attr_syn(method.span(), quote! { verus_macro }));
            let mut new_stream = TokenStream::new();
            spec_fun_opt.to_tokens(&mut new_stream);
            method.to_tokens(&mut new_stream);
            proc_macro::TokenStream::from(new_stream)
        }
        _ => {
            let span = spec_attr.span();
            proc_macro::TokenStream::from(
                quote_spanned!(span => compile_error!("'verus_spec' is not allowed here");),
            )
        }
    }
}

pub fn rewrite(
    erase: EraseGhost,
    outer_attr: SpecAttributeKind,
    outer_attr_tokens: TokenStream,
    input: TokenStream,
) -> Result<TokenStream, syn::Error> {
    let span = outer_attr_tokens.span();
    let outer_attr_tokens = insert_brackets(&outer_attr, outer_attr_tokens);
    let verus_attrs = vec![(outer_attr, outer_attr_tokens)];
    let f = parse2::<AnyFnOrLoop>(input)?;
    match f {
        AnyFnOrLoop::Loop(mut l) => {
            expand_verus_attribute(erase, verus_attrs, &mut l, false);
            Ok(quote_spanned! {l.span()=>#l})
        }
        AnyFnOrLoop::ForLoop(mut l) => {
            expand_verus_attribute(erase, verus_attrs, &mut l, false);
            Ok(quote_spanned! {l.span()=>#l})
        }
        AnyFnOrLoop::While(mut l) => {
            expand_verus_attribute(erase, verus_attrs, &mut l, false);
            Ok(quote_spanned! {l.span()=>#l})
        }
        AnyFnOrLoop::Fn(_) | AnyFnOrLoop::TraitMethod(_) => Ok(
            quote_spanned!(span => compile_error!("'verus_spec' attribute expected on function");),
        ),
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

pub fn verus_out_rewrite(
    erase: EraseGhost,
    input: TokenStream,
) -> syn::Result<proc_macro::TokenStream> {
    let tracked_expr = syn_verus::parse2::<syn_verus::VerusOut>(input)
        .expect("Tracked(..) or Ghost(...) => expr ");
    let syn_verus::VerusOut { tracked, expr } = tracked_expr;
    if !erase.keep() {
        return match expr {
            Some((e, _t)) => Ok(quote_spanned!(e.span() => #e).into()),
            _ => Ok(quote!().into()),
        };
    }
    let tracked_vars = tracked.into_iter().map(|e| {
        if let syn_verus::Expr::Call(ref call) = e {
            match syntax::is_tracked_or_ghost_call(&call) {
                Some(is_tracked) => syntax::create_tracked_ghost_vars(
                    &erase,
                    is_tracked,
                    false,
                    call.span(),
                    call.args[0].clone(),
                ),
                _ => e,
            }
        } else {
            e
        }
    });
    if expr.is_some() {
        let (e, _t) = expr.unwrap();
        Ok(quote! {
            (#e #(, #tracked_vars)*)
        }
        .into())
    } else {
        Ok(quote! {
            (() #(, #tracked_vars)*)
        }
        .into())
    }
}
