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
/// - To Add tracked/ghost in signature, use #[verus_spec(with ...)] in function definition.
///   To pass and get tracked/ghost from function call, use #[verus_spec(with ...)] in
///   call expr or local statement. Unverified code does not need to change arguments or outputs.
///
/// Rationale:
/// - This approach avoids introducing new syntax into existing Rust executable
///   code, allowing verification and non-verification developers to collaborate
///   without affecting each other.
///   Thus, this module uses syn instead of verus_syn in most cases.
///   For developers who do not understand verification, they can easily ignore
///   verus code via feature/cfg selection and use standard rust tools like
///   `rustfmt` and `rust-analyzer`.
/// - Unverified code does not need additional annotation to interact with verified.
///
/// Limitations:
/// - #[verus_verify] does not support all `verus` syntax, particularly
///   those constructs not accepted by `rustc`.
/// - For defining complex `verus` specifications or proof functions, developers
///   should still use `verus! {}`.
/// - Use of tracked variable is possible but in a different style.
///
/// Example:
/// - Refer to `examples/syntax_attr.rs`.
use proc_macro2::TokenStream;
use quote::{ToTokens, quote, quote_spanned};
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::visit_mut::VisitMut;
use syn::{Expr, Item, ItemConst, parse2, spanned::Spanned};

use crate::{
    EraseGhost,
    attr_block_trait::{AnyAttrBlock, AnyFnOrLoop},
    syntax::{self, has_external_code_syn, mk_verifier_attr_syn, mk_verus_attr_syn},
    syntax_trait,
    unerased_proxies::VERUS_UNERASED_PROXY,
};

pub const VERIFIED: &str = "_VERUS_VERIFIED";
/// Name prefix of the companion trait that holds the verified counterparts of
/// the methods of a trait. The name is derived from the name of that trait so
/// that an implementation does not have to spell it out.
pub const VERIFIED_TRAIT_PREFIX: &str = "_VERUS_VERIFIED_TRAIT";

pub const DUAL_SPEC_PREFIX: &str = "__VERUS_SPEC";

const VERUS_SPEC: &str = "verus_spec";

enum VerusIOTarget {
    Local(syn::Local),
    Expr(syn::Expr),
}

impl quote::ToTokens for VerusIOTarget {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            VerusIOTarget::Local(local) => local.to_tokens(tokens),
            VerusIOTarget::Expr(expr) => expr.to_tokens(tokens),
        }
    }
}

enum VerusSpecTarget {
    IOTarget(VerusIOTarget),
    FnOrLoop(AnyFnOrLoop),
    ItemConst(ItemConst),
    ItemStatic(syn::ItemStatic),
}

impl syn::parse::Parse for VerusSpecTarget {
    fn parse(input: syn::parse::ParseStream) -> syn::parse::Result<VerusSpecTarget> {
        use syn::parse::discouraged::Speculative;
        let fork = input.fork();
        if let Ok(fn_or_loop) = fork.parse() {
            input.advance_to(&fork);
            return Ok(VerusSpecTarget::FnOrLoop(fn_or_loop));
        }
        let fork = input.fork();
        if let Ok(stmt) = fork.parse() {
            if let syn::Stmt::Local(local) = stmt {
                input.advance_to(&fork);
                return Ok(VerusSpecTarget::IOTarget(VerusIOTarget::Local(local)));
            }
        }
        let fork = input.fork();
        if let Ok(item_const) = fork.parse::<ItemConst>() {
            input.advance_to(&fork);
            return Ok(VerusSpecTarget::ItemConst(item_const));
        }
        let fork = input.fork();
        if let Ok(item_static) = fork.parse::<syn::ItemStatic>() {
            input.advance_to(&fork);
            return Ok(VerusSpecTarget::ItemStatic(item_static));
        }

        let expr: Expr = input.parse()?;
        return Ok(VerusSpecTarget::IOTarget(VerusIOTarget::Expr(expr)));
    }
}

/// The counterparts a crate compiled in `Erase` mode declares: the companion
/// trait of a trait, and the companion implementation of an implementation of
/// one. See `rewrite_unverified_func` for what a counterpart is declared for.
fn erase_verus_attribute(
    attr_args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let parser = syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated;
    let Ok(args) = syn::parse::Parser::parse(parser, attr_args) else {
        return input;
    };
    let has_arg =
        |name: &str| args.iter().any(|arg| arg.path().get_ident().map_or(false, |id| id == name));
    let Ok(mut item) = syn::parse::<syn::Item>(input.clone()) else {
        return input;
    };
    let is_proxy = has_arg("external_trait_specification")
        || matches!(&item, syn::Item::Trait(item_trait) if item_trait.attrs.iter().any(|attr| {
            attr.path().segments.last().map_or(false, |seg| seg.ident == "external_trait_specification")
        }));
    let span = item.span();
    let companion_impl = match split_trait_impl(&mut item) {
        Ok(companion_impl) => companion_impl,
        Err(error_tokens) => return error_tokens.into(),
    };
    let companion_trait = match companion_trait_of(&mut item, is_proxy) {
        Ok(companion_trait) => companion_trait,
        Err(error_tokens) => return error_tokens.into(),
    };
    if companion_impl.is_none() && companion_trait.is_none() {
        return input;
    }
    let mut new_stream = quote_spanned! {span=> #item };
    if let Some(mut companion_impl) = companion_impl {
        prepare_items_for_verus_spec(span, &mut companion_impl, true);
        companion_impl.to_tokens(&mut new_stream);
    }
    if let Some(mut companion_trait) = companion_trait {
        prepare_items_for_verus_spec(span, &mut companion_trait, true);
        quote_spanned! {span=>
            #[allow(non_camel_case_types)]
            #[verus::internal(verified_trait)]
            #companion_trait
        }
        .to_tokens(&mut new_stream);
    }
    new_stream.into()
}

pub(crate) fn rewrite_verus_attribute(
    erase: &EraseGhost,
    attr_args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    if erase.erase_all() {
        // `#[verus_spec]` is a no-op in this mode, so nothing declares the
        // counterparts the companion items would collect.
        return input;
    }
    if !erase.keep() {
        return erase_verus_attribute(attr_args, input);
    }

    let mut item = syn::parse_macro_input!(input as Item);
    let args = syn::parse_macro_input!(attr_args with syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated);

    let mut attributes = Vec::new();
    let mut contains_non_external = false;
    let mut contains_external = false;
    let mut spec_fun = None;
    const VERIFY_ATTRS: [&str; 4] = ["rlimit", "spinoff_prover", "external_derive", "ext_equal"];
    const DUAL_ATTR: &str = "dual_spec";
    const IGNORE_VERIFY_ATTRS: [&str; 3] =
        ["external", "external_body", "external_type_specification"];
    const EXTERNAL_TRAIT_SPECIFICATION: &str = "external_trait_specification";
    let mut is_external_trait_proxy = match &item {
        syn::Item::Trait(item_trait) => item_trait.attrs.iter().any(|attr| {
            attr.path()
                .segments
                .last()
                .map_or(false, |seg| seg.ident == EXTERNAL_TRAIT_SPECIFICATION)
        }),
        _ => false,
    };
    // Modifier attrs are compatible with both external and non-external attrs.
    // They neither set contains_external nor contains_non_external.
    const MODIFIER_ATTRS: [&str; 3] = [
        "reject_recursive_types",
        "reject_recursive_types_in_ground_variants",
        "accept_recursive_types",
    ];

    for arg in &args {
        let path = arg.path().get_ident().expect("Invalid verus verifier attribute");
        if EXTERNAL_TRAIT_SPECIFICATION == path.to_string().as_str() {
            is_external_trait_proxy = true;
            contains_external = true;
            attributes.push(quote_spanned!(arg.span() => #[verifier::#arg]));
        } else if IGNORE_VERIFY_ATTRS.contains(&path.to_string().as_str()) {
            contains_external = true;
            attributes.push(quote_spanned!(arg.span() => #[verifier::#arg]));
        } else if VERIFY_ATTRS.contains(&path.to_string().as_str()) {
            contains_non_external = true;
            attributes.push(quote_spanned!(arg.span() => #[verifier::#arg]));
        } else if MODIFIER_ATTRS.contains(&path.to_string().as_str()) {
            attributes.push(quote_spanned!(arg.span() => #[verifier::#arg]));
        } else if DUAL_ATTR == path.to_string().as_str() {
            // This is a macro-level hack to support dual mode.
            // Thus, only a limited number of pure compute functions are
            // supported.
            // The real dual mode is not ready yet (e.g., verifier::dual_spec).
            // The spec function is generated with the name _VERUS_SPEC_<name>
            // if no name is given.
            if let syn::Item::Fn(f) = &mut item {
                let mut spec_f = f.clone();
                let ident = if let syn::Meta::List(list) = arg {
                    syn::parse2(list.tokens.clone())
                        .expect("unsupported tokens in verus_verify(dual_spec(...))")
                } else {
                    syn::Ident::new(
                        &format!("{DUAL_SPEC_PREFIX}_{}", f.sig.ident),
                        f.sig.ident.span(),
                    )
                };
                spec_f.sig.ident = ident.clone();
                spec_f.attrs = vec![mk_verus_attr_syn(f.span(), quote! { spec })];
                // remove proof-related macros
                replace_block(EraseGhost::Erase, spec_f.block_mut().unwrap(), false);
                spec_fun = Some(spec_f);

                attributes
                    .push(quote_spanned!(arg.span() => #[verifier::when_used_as_spec(#ident)]));
            }
        } else {
            let span = arg.span();
            return proc_macro::TokenStream::from(quote_spanned!(span =>
                compile_error!("unsupported parameters {:?} in #[verus_verify(...)]", arg);
            ));
        }
    }
    if contains_external && contains_non_external {
        return proc_macro::TokenStream::from(quote_spanned!(args.span() =>
            compile_error!("conflict parameters in #[verus_verify(...)]");
        ));
    }
    if !contains_external {
        attributes.push(quote_spanned!(item.span() => #[verifier::verify]));
    }

    // Define the verified counterparts of the methods with a `with` clause in an
    // implementation of the companion trait, leaving the unverified stubs here.
    let mut companion_impl = None;
    if matches!(&item, syn::Item::Impl(item_impl) if item_impl.trait_.is_some()) {
        match split_trait_impl(&mut item) {
            Ok(companion_item) => companion_impl = companion_item,
            Err(error_tokens) => return error_tokens.into(),
        }
    }

    // Collect the verified counterparts of the methods with a `with` clause into
    // a companion trait.
    let companion_trait = match companion_trait_of(&mut item, is_external_trait_proxy) {
        Ok(companion_item) => companion_item,
        Err(error_tokens) => return error_tokens.into(),
    };

    // Inject #[verus_spec] where missing and stamp impl methods with the sentinel marker.
    prepare_items_for_verus_spec(args.span(), &mut item, false);

    let mut new_stream = quote_spanned! {item.span()=>
        #(#attributes)*
        #item
    };
    if let Some(mut companion_impl) = companion_impl {
        prepare_items_for_verus_spec(args.span(), &mut companion_impl, true);
        quote_spanned! {companion_impl.span()=>
            #(#attributes)*
            #companion_impl
        }
        .to_tokens(&mut new_stream);
    }
    if let Some(mut companion_trait) = companion_trait {
        prepare_items_for_verus_spec(args.span(), &mut companion_trait, true);
        quote_spanned! {companion_trait.span()=>
            #[allow(non_camel_case_types)]
            #[verus::internal(verified_trait)]
            #[verifier::verify]
            #companion_trait
        }
        .to_tokens(&mut new_stream);
    }
    spec_fun.map(|f| f.to_tokens(&mut new_stream));
    new_stream.into()
}

struct ExecReplacer {
    erase: EraseGhost,
    inside_external_code: bool,
}

impl VisitMut for ExecReplacer {
    // Enable the hack only when needed
    #[cfg(feature = "vpanic")]
    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        syn::visit_mut::visit_macro_mut(self, mac);
        // Only replace in verification mode
        if !self.erase.keep() || self.inside_external_code {
            return;
        }
        if let Some(x) = mac.path.segments.first_mut() {
            let ident = x.ident.to_string();
            if ident == "panic" {
                // The builtin panic macro could not be supported due to
                // the use of panic_fmt takes Argument and Argument is created via Arguments::new_v1
                // with a private struct rt::Argument.
                // Directly replacing panic macro is the simpliest solution.
                // Build the full path: std::prelude::vpanic
                let mut segments = syn::punctuated::Punctuated::new();
                segments.push(syn::Ident::new("vstd", x.span()).into());
                segments.push(syn::Ident::new("vpanic", x.span()).into());
                mac.path = syn::Path { leading_colon: None, segments };
            }
        }
    }

    fn visit_attribute_mut(&mut self, node: &mut syn::Attribute) {
        // Ignore verus_spec in non-verification mode.
        // Thus, non-verification mode does not need to use unstable features.
        if self.erase.keep() {
            return;
        }
        if let Some(last) = node.path().segments.last() {
            if last.ident == VERUS_SPEC {
                *node = syn::parse_quote! {
                    #[doc = r"verus_spec is applied only in verification mode"]
                }
            }
        }
    }

    /// convert proof_with macro to functin with ghost/tracked argumemts.
    /// In order to apply `with` to expr/stmt without using unstable feature.
    /// proof_with!(Tracked(x), Ghost(y);
    /// f(a);
    /// Also supports struct constructors with ghost/tracked fields:
    /// proof_with!{ p: Tracked(p) }
    /// STest { u }
    fn visit_block_mut(&mut self, block: &mut syn::Block) {
        // Don't call visit_block_mut to recurse on the whole block --
        // skip statements that will be processed by their own #[verus_spec] attribute.
        // syn::visit_mut::visit_block_mut(self, block);
        for stmt in &mut block.stmts {
            // Don't recurse here into Fn and Const.
            // Instead, let a subsequent expansion of #[verus_spec] handle the visit
            let span = stmt.span();
            match stmt {
                syn::Stmt::Item(Item::Fn(item)) => {
                    add_verus_spec_if_needed(&mut item.attrs, span);
                }
                syn::Stmt::Item(Item::Const(item)) => {
                    add_verus_spec_if_needed(&mut item.attrs, span);
                }
                _ => self.visit_stmt_mut(stmt),
            }
        }

        // If we are in non-verification mode, we erase all proof-related statements.
        if !self.erase.keep() {
            block.stmts.retain(|stmt| !is_verus_proof_stmt(stmt));
            return;
        }

        let mut with_args: TokenStream = TokenStream::new();
        for stmt in &mut block.stmts {
            match stmt {
                syn::Stmt::Macro(syn::StmtMacro { mac, .. }) if mac.path.is_ident("proof_with") => {
                    verus_syn::Token![with](mac.span()).to_tokens(&mut with_args);
                    mac.tokens.to_tokens(&mut with_args);
                }
                syn::Stmt::Local(syn::Local { attrs, init: Some(_), .. })
                    if !with_args.is_empty() =>
                {
                    attrs.push(crate::syntax::mk_rust_attr_syn(
                        with_args.span(),
                        VERUS_SPEC,
                        with_args,
                    ));
                    with_args = TokenStream::new();
                }
                syn::Stmt::Expr(expr, _) if !with_args.is_empty() => {
                    let call_with_spec = verus_syn::parse2(with_args.clone()).unwrap_or_else(|e| {
                        panic!("Failed to parse proof_with {:?}: {:?}", with_args, e)
                    });
                    rewrite_with_expr(self.erase.clone(), expr, call_with_spec);
                    with_args = TokenStream::new();
                }
                _ if with_args.is_empty() => {
                    // do nothing
                }
                _ => {
                    panic!(
                        "Expected a function call or struct constructor after proof_with! macro"
                    );
                }
            };
        }
    }

    fn visit_expr_for_loop_mut(&mut self, for_loop: &mut syn::ExprForLoop) {
        syn::visit_mut::visit_expr_for_loop_mut(self, for_loop);

        if !self.erase.keep() || self.inside_external_code {
            return;
        }

        // In verification mode, even without verus spec on the loop, we still
        // need to desugar the for loop.
        // So, if there's no `verus_spec` attribute, we need to add an empty one.
        let span = for_loop.span();
        add_verus_spec_if_needed(&mut for_loop.attrs, span);
    }
}

/// Check for misuse of `#[verus_spec]` and `#[verus_verify]`.
/// Returns `true` if a verus_macro has already been applied.
///
/// 1. Reject duplicate `#[verus_spec]` attributes.
///    Duplicate `#[verus_spec]` attributes introduce unnecessary complexity
///    and extra rewriting overhead.
///
/// 2. Reject `#[verus_verify]` applied after `#[verus_spec]`.
///    `#[verus_verify]` invokes `prepare_verus_spec`, which inserts
///    `#[verus_spec]` when needed. Applying it after an existing
///    `#[verus_spec]` may accidentally introduce duplicate attributes.
///
/// 3. Warn when `#[verus_spec]` is used inside a `verus!` block.
///    Using `#[verus_spec]` inside a `verus!` block may lead to problems since they are
///    not designed to work together. If allow_verus_macro is false, we reject such usage.
fn check_misuse_verus_spec(
    attrs: &[syn::Attribute],
    allow_verus_macro: bool,
) -> Result<bool, proc_macro::TokenStream> {
    let attr_span = proc_macro::Span::call_site();
    let mut verus_macro_applied = false;
    for attr in attrs {
        if let Some(ident) = attr.path().get_ident() {
            if ident == VERUS_SPEC {
                return Err(quote_spanned! { attr_span.into() => compile_error!(
                    "Multiple #[verus_spec] attributes are not allowed.
                    This may be caused by incorrect usage or a bug in builtin_macros");
                }
                .into());
            } else if ident == "verus_verify" {
                return Err(quote_spanned! { attr_span.into() => compile_error!(
                    "#[verus_verify] attributes should be applied before #[verus_spec].");
                }
                .into());
            }
        }
        if is_verus_macro_applied(&attr) {
            verus_macro_applied = true;
            if !allow_verus_macro {
                return Err(quote_spanned! { attr_span.into() => compile_error!(
                    "verus! macro is already applied.");
                }
                .into());
            }
        }
    }
    if verus_macro_applied {
        // Leave a warning when user mistakenly mixed them.
        #[cfg(verus_keep_ghost)]
        proc_macro::Diagnostic::spanned(
            attr_span,
            proc_macro::Level::Warning,
            "#[verus_spec] is likely used inside a verus! block.
            Consider move it out of verus! or remove #[verus_spec].",
        )
        .emit();
    }
    Ok(verus_macro_applied)
}

/// Check whether a Verus macro might have already been applied.
///
/// Both `#[verus_spec]` and `verus!` may be the source of the `#[verus::internal(...)]`.
/// The source of #[verus_spec] is ruled out if it is applied in `verus_spec`
/// rewriting and after `check_misuse_verus_spec` has been executed.
fn is_verus_macro_applied(attrs: &syn::Attribute) -> bool {
    attrs.path().segments.len() == 2
        && attrs.path().segments[0].ident == "verus"
        && attrs.path().segments[1].ident == "internal"
}

/// The verified counterpart of a method of a trait lives in a companion trait,
/// declared next to the trait, so that the trait itself keeps the exact
/// signature its callers and its implementors see. An implementation of the
/// trait is therefore split along the same line, without any annotation: a
/// method with a `with` clause defines its counterpart in an implementation of
/// the companion trait, and what is left in the implementation of the trait is
/// the unverified stub of that counterpart.
///
/// Given `impl T for S`, a method
///
/// ```ignore
/// #[verus_spec(with Ghost(g): Ghost<u64>)]
/// fn f(&self, a: u64) -> u64 { BODY }
/// ```
///
/// becomes a counterpart in `impl _VERUS_VERIFIED_TRAIT_T for S`
///
/// ```ignore
/// #[verus_spec(with Ghost(g): Ghost<u64>)]
/// fn _VERUS_VERIFIED_f(&self, a: u64, Ghost(g): Ghost<u64>) -> u64 { BODY }
/// ```
///
/// while `impl T for S` keeps the stub, which is `external_body` and inherits
/// `requires(false)` from the declaration of `f`. In erase mode nothing is
/// split: the stub keeps the real body and is what is executed.
fn split_trait_impl(item: &mut syn::Item) -> Result<Option<syn::Item>, TokenStream> {
    let span = item.span();
    let syn::Item::Impl(item_impl) = item else {
        return Ok(None);
    };
    let Some((_, trait_path, _)) = &item_impl.trait_ else {
        return Ok(None);
    };
    let companion = companion_trait_path(trait_path);
    let mut companion_items: Vec<syn::ImplItem> = Vec::new();
    for impl_item in item_impl.items.iter_mut() {
        let syn::ImplItem::Fn(fun) = impl_item else {
            continue;
        };
        if !has_with_clause(&fun.attrs)? {
            continue;
        }
        companion_items.push(syn::ImplItem::Fn(fun.clone()));
        // What is left implements the method of the trait itself.
        fun.attrs.push(mk_companion_marker(span));
    }
    if companion_items.is_empty() {
        return Ok(None);
    }
    let mut companion_impl = item_impl.clone();
    companion_impl.attrs = Vec::new();
    // Implementing the companion trait is never unsafe: it declares only the
    // verified counterparts, and the obligation of the trait itself is
    // discharged by the implementation of that trait.
    companion_impl.unsafety = None;
    companion_impl.trait_ = Some((None, companion, syn::token::For { span }));
    companion_impl.items = companion_items;
    Ok(Some(syn::Item::Impl(companion_impl)))
}

/// Derive the companion trait of a trait whose methods declare a `with` clause.
///
/// A method cannot declare its own verified counterpart: the counterpart has
/// extra parameters, so it is a different method, and for an external trait it
/// could not be added at all. The counterparts of the methods that are given a
/// `with` clause are therefore collected into a companion trait declared next
/// to the trait, and the method itself keeps `requires(false)`, so verified
/// code can only call it through its counterpart.
///
/// The companion is a subtrait of the trait it belongs to, `trait
/// _VERUS_VERIFIED_TRAIT_X: X`, which is the only direction available for an
/// external trait, and the one that lets a counterpart refer to `Self::Assoc`
/// and keep a default body. A bound `A: X` therefore does not reach the
/// counterparts by itself; the bound on the companion is added to the callers
/// that need it, see `hir_proof_with_rewrite`.
///
/// An implementation is split along the same line, so it implements the
/// companion only if it defines a method that has a `with` clause. A method
/// that has both a `with` clause and a default body therefore has to be defined
/// by every implementation, like a method without a default body.
fn companion_trait_of(
    item: &mut syn::Item,
    is_proxy: bool,
) -> Result<Option<syn::Item>, TokenStream> {
    let syn::Item::Trait(item_trait) = item else {
        return Ok(None);
    };
    let span = item_trait.ident.span();
    let mut methods: Vec<syn::TraitItem> = Vec::new();
    for trait_item in item_trait.items.iter_mut() {
        let syn::TraitItem::Fn(fun) = trait_item else {
            continue;
        };
        if !has_with_clause(&fun.attrs)? {
            continue;
        }
        if let Some(default) = &fun.default {
            // The counterpart of the method is declared by the companion trait,
            // which an implementation only implements when it overrides the
            // method. A default body would therefore be inherited by the
            // counterpart of an implementation that overrides the method
            // without a `with` clause, and a verified call would run the
            // default while the executable runs the override.
            return Err(quote_spanned!(default.span() =>
                compile_error!("`with` is not supported on a trait method with a default body: remove the default body and implement the method in every implementation of the trait");
            ));
        }
        methods.push(syn::TraitItem::Fn(fun.clone()));
        // What is left declares the method of the trait itself.
        fun.attrs.push(mk_companion_marker(span));
    }
    if methods.is_empty() {
        return Ok(None);
    }
    // The trait the companion belongs to: for a proxy that is the external
    // trait it specifies, not the proxy itself.
    let trait_path = if is_proxy {
        let Some(external) = external_trait_of_proxy(item_trait) else {
            return Err(quote_spanned!(span =>
                compile_error!("`with` on the proxy of an external trait requires an `ExternalTraitSpecificationFor` member naming the external trait");
            ));
        };
        external
    } else {
        self_trait_path(item_trait)
    };
    let companion = companion_trait_path(&trait_path);
    let mut supertraits = syn::punctuated::Punctuated::new();
    supertraits.push(mk_trait_bound(trait_path));
    Ok(Some(syn::Item::Trait(syn::ItemTrait {
        attrs: Vec::new(),
        vis: item_trait.vis.clone(),
        unsafety: None,
        auto_token: None,
        restriction: None,
        trait_token: item_trait.trait_token,
        ident: companion.segments.last().expect("non-empty path").ident.clone(),
        generics: item_trait.generics.clone(),
        colon_token: Some(syn::token::Colon { spans: [span] }),
        supertraits,
        brace_token: item_trait.brace_token,
        items: methods,
    })))
}

fn mk_trait_bound(path: syn::Path) -> syn::TypeParamBound {
    syn::TypeParamBound::Trait(syn::TraitBound {
        paren_token: None,
        modifier: syn::TraitBoundModifier::None,
        lifetimes: None,
        path,
    })
}

/// The trait itself, named with the arguments of its own generics: `X<A>` for
/// `trait X<A>`.
fn self_trait_path(item_trait: &syn::ItemTrait) -> syn::Path {
    let ident = &item_trait.ident;
    let (_, ty_generics, _) = item_trait.generics.split_for_impl();
    syn::parse_quote_spanned!(ident.span() => #ident #ty_generics)
}

/// The external trait that a proxy specifies, named by the bound of its
/// `ExternalTraitSpecificationFor` member.
fn external_trait_of_proxy(item_trait: &syn::ItemTrait) -> Option<syn::Path> {
    item_trait.items.iter().find_map(|trait_item| {
        let syn::TraitItem::Type(assoc) = trait_item else {
            return None;
        };
        if assoc.ident != "ExternalTraitSpecificationFor" {
            return None;
        }
        assoc.bounds.iter().find_map(|bound| match bound {
            syn::TypeParamBound::Trait(bound) => Some(bound.path.clone()),
            _ => None,
        })
    })
}

/// Does one of these attributes declare extra ghost/tracked inputs or outputs?
fn has_with_clause(attrs: &[syn::Attribute]) -> Result<bool, TokenStream> {
    for attr in attrs {
        if attr.path().get_ident().map_or(true, |ident| ident != VERUS_SPEC) {
            continue;
        }
        let syn::Meta::List(list) = &attr.meta else {
            continue;
        };
        let spec: verus_syn::SignatureSpecAttr = match verus_syn::parse2(list.tokens.clone()) {
            Ok(spec) => spec,
            Err(err) => return Err(err.to_compile_error()),
        };
        if spec.spec.with.is_some() {
            return Ok(true);
        }
    }
    Ok(false)
}

/// The name of the companion trait of a trait.
///
/// The companion is declared next to the trait it belongs to, so it is reached
/// through the same path, with the last segment renamed. The companion repeats
/// the generics of that trait, so the arguments written at the use site carry
/// over unchanged.
pub(crate) fn companion_trait_path(trait_path: &syn::Path) -> syn::Path {
    let mut companion = trait_path.clone();
    let segment = companion.segments.last_mut().expect("non-empty trait path");
    segment.ident = syn::Ident::new(
        &format!("{VERIFIED_TRAIT_PREFIX}_{}", segment.ident),
        segment.ident.span(),
    );
    companion
}

/// Adds a `#[verus_spec]` attribute to the given attributes if it's not already present.
/// #[verus_spec] may be applied earlier or later than the current attribute.
/// If it's applied earlier, we can infer it via verus::internal(xxx).
/// If it's applied later, we can find it directly.
fn add_verus_spec_if_needed(attrs: &mut Vec<syn::Attribute>, span: proc_macro2::Span) {
    if attrs.iter().any(|attr| attr.path().get_ident().map_or(false, |ident| ident == VERUS_SPEC)) {
        return;
    }
    attrs.push(crate::syntax::mk_rust_attr_syn(span, VERUS_SPEC, TokenStream::new()));
}

/// Prepares items under `#[verus_verify]` for subsequent `#[verus_spec]` expansion.
///
/// This function performs two tasks:
///
/// 1. **Inject `#[verus_spec]` where missing.** Items and impl items that carry
///    `#[verus_verify]` but no `#[verus_spec]` would otherwise be marked as
///    verifier-aware without receiving the necessary rewrites (loop desugaring,
///    const/static proxy generation, etc.), resulting in confusing error messages.
///    An empty `#[verus_spec]` is added so the rewriter has something to act on.
///
/// 2. **Mark impl methods with a sentinel attribute.** Each impl method that has
///    (or just received) a `#[verus_spec]` attribute is tagged with an internal
///    `#[allow(unused, verus_impl_method_marker)]` attribute. This signals to the
///    `#[verus_spec]` expansion that the method lives inside an impl block,
///    enabling it to apply impl-specific rewrites.
///
/// Recursion into nested items is intentionally skipped here; `#[verus_spec]`
/// handles that during its own expansion pass.
fn prepare_items_for_verus_spec(
    span: proc_macro2::Span,
    i: &mut syn::Item,
    is_verified_trait: bool,
) {
    match i {
        syn::Item::Trait(t) if is_verified_trait => {
            for item in &mut t.items {
                if let syn::TraitItem::Fn(syn::TraitItemFn { attrs, .. }) = item {
                    add_verus_spec_if_needed(attrs, span);
                    attrs.push(crate::syntax::mk_rust_attr_syn(
                        span,
                        "allow",
                        quote_spanned! { span => (unused, verus_verified_trait_marker)},
                    ));
                }
            }
        }
        syn::Item::Const(syn::ItemConst { attrs, .. })
        | syn::Item::Static(syn::ItemStatic { attrs, .. })
        | syn::Item::Fn(syn::ItemFn { attrs, .. }) => {
            add_verus_spec_if_needed(attrs, span);
        }
        syn::Item::Impl(i) => {
            let marker = if i.trait_.is_some() {
                quote_spanned! { span => (unused, verus_trait_impl_method_marker)}
            } else {
                quote_spanned! { span => (unused, verus_impl_method_marker)}
            };
            for item in &mut i.items {
                match item {
                    syn::ImplItem::Const(syn::ImplItemConst { attrs, .. }) => {
                        add_verus_spec_if_needed(attrs, span);
                    }
                    syn::ImplItem::Fn(syn::ImplItemFn { attrs, .. }) => {
                        add_verus_spec_if_needed(attrs, span);
                        attrs.push(crate::syntax::mk_rust_attr_syn(span, "allow", marker.clone()));
                        if is_verified_trait {
                            attrs.push(crate::syntax::mk_rust_attr_syn(
                                span,
                                "allow",
                                quote_spanned! { span => (unused, verus_verified_trait_marker)},
                            ));
                        }
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }
}

/// A method with a `with` clause is expanded into an unverified stub and a
/// verified counterpart. When the two do not live next to each other, each side
/// is marked with which of the two it is to expand into.
///
/// This marker says: the counterpart is declared elsewhere, in the companion
/// trait, so expand into the stub only.
fn mk_companion_marker(span: proc_macro2::Span) -> syn::Attribute {
    crate::syntax::mk_rust_attr_syn(
        span,
        "allow",
        quote_spanned! { span => (unused, verus_companion_marker)},
    )
}

fn is_companion_marker(attr: &syn::Attribute) -> bool {
    attr.path().get_ident().map_or(false, |ident| ident == "allow")
        && matches!(&attr.meta, syn::Meta::List(meta_list)
            if meta_list.tokens.to_string().contains("verus_companion_marker"))
}

/// The other side: this method is declared by a companion trait, or defined by
/// an implementation of one, so expand into the counterpart only. The stub is
/// the method of the trait the companion belongs to.
fn is_verified_trait_marker(attr: &syn::Attribute) -> bool {
    attr.path().get_ident().map_or(false, |ident| ident == "allow")
        && matches!(&attr.meta, syn::Meta::List(meta_list)
            if meta_list.tokens.to_string().contains("verus_verified_trait_marker"))
}

fn is_verus_proof_stmt(stmt: &syn::Stmt) -> bool {
    pub const VERUS_MACROS: [&str; 3] = ["proof", "proof_decl", "proof_with"];
    if let syn::Stmt::Macro(mac_stmt) = stmt {
        let syn::Macro { path, .. } = &mac_stmt.mac;
        if let Some(ident) = path.get_ident() {
            return VERUS_MACROS.contains(&ident.to_string().as_str());
        }
    }
    false
}

// We need to replace some macros/attributes.
// For example, panic, println, fmt macro is hard to support in verus.
// We can replace them to enable the support.
// TODO: when tracked/ghost is supported, we need to clear verus-related
// attributes for expression so that unverfied `cargo build` does not need to
// enable unstable feature for macro.
pub(crate) fn replace_block(
    erase: EraseGhost,
    fblock: &mut syn::Block,
    inside_external_code: bool,
) {
    let mut replacer = ExecReplacer { erase, inside_external_code };
    replacer.visit_block_mut(fblock);
}

pub(crate) fn replace_expr(erase: EraseGhost, expr: &mut syn::Expr) {
    let mut replacer = ExecReplacer { erase, inside_external_code: false };
    replacer.visit_expr_mut(expr);
}

pub(crate) fn rewrite_verus_spec(
    erase: EraseGhost,
    outer_attr_tokens: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    if erase.erase_all() {
        return input;
    }
    // Remove the last `,` if `input` has one.
    let mut tokens: Vec<_> = proc_macro2::TokenStream::from(input).into_iter().collect();
    if matches!(tokens.last(), Some(proc_macro2::TokenTree::Punct(p)) if p.as_char() == ',') {
        tokens.pop();
    }
    let input: proc_macro::TokenStream =
        tokens.into_iter().collect::<proc_macro2::TokenStream>().into();

    let f = match syn::parse::<VerusSpecTarget>(input) {
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
        VerusSpecTarget::FnOrLoop(f) => {
            rewrite_verus_spec_on_fun_or_loop(erase, outer_attr_tokens, f)
        }
        VerusSpecTarget::ItemConst(i) => {
            if let Err(error_tokens) = check_misuse_verus_spec(&i.attrs, true) {
                return error_tokens;
            }
            rewrite_verus_spec_on_item_const(erase, outer_attr_tokens, i)
        }
        VerusSpecTarget::ItemStatic(i) => {
            if let Err(error_tokens) = check_misuse_verus_spec(&i.attrs, true) {
                return error_tokens;
            }
            rewrite_verus_spec_on_item_static(erase, outer_attr_tokens, i)
        }
        VerusSpecTarget::IOTarget(i) => {
            rewrite_verus_spec_on_expr_local(erase, outer_attr_tokens, i)
        }
    }
}

fn closure_to_fn_sig(closure: &syn::ExprClosure) -> syn::Signature {
    let infer_type = |span| {
        Box::new(syn::Type::Infer(syn::TypeInfer { underscore_token: syn::Token![_](span) }))
    };
    syn::Signature {
        constness: closure.constness,
        asyncness: closure.asyncness,
        unsafety: None,
        abi: None,
        fn_token: syn::Token![fn](closure.span()),
        ident: syn::Ident::new("closure", closure.span()),
        generics: syn::Generics::default(),
        inputs: closure
            .inputs
            .iter()
            .map(|arg| {
                let (pat, ty) = match arg {
                    syn::Pat::Type(pat_ty) => (pat_ty.pat.clone(), pat_ty.ty.clone()),
                    syn::Pat::Ident(pat_ident) => {
                        let ty = infer_type(pat_ident.span());
                        (Box::new(syn::Pat::Ident(pat_ident.clone())), ty)
                    }
                    _ => {
                        panic!("unexpected pattern in closure argument: {:?}", arg);
                    }
                };
                syn::FnArg::Typed(syn::PatType {
                    attrs: vec![],
                    pat: pat,
                    colon_token: syn::Token![:](arg.span()),
                    ty: ty,
                })
            })
            .collect(),
        variadic: None,
        output: closure.output.clone(),
        paren_token: syn::token::Paren::default(),
    }
}

fn syn_to_verus_syn<V: verus_syn::parse::Parse>(input: impl ToTokens) -> V {
    let tokens = input.to_token_stream();
    verus_syn::parse2(tokens).unwrap()
}

pub(crate) fn rewrite_verus_spec_on_item_const(
    erase_ghost: EraseGhost,
    outer_attr_tokens: proc_macro::TokenStream,
    item_const: ItemConst,
) -> proc_macro::TokenStream {
    if erase_ghost.erase() {
        return item_const.to_token_stream().into();
    }
    let spec_attr =
        verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::SignatureSpecAttr);
    let mut verus_item_const = syn_to_verus_syn::<verus_syn::ItemConst>(item_const);
    let span = verus_item_const.span();
    if spec_attr.spec.ensures.is_some() {
        verus_item_const.ensures = spec_attr.spec.ensures;
        verus_item_const.mode = verus_syn::FnMode::Exec(verus_syn::ModeExec {
            exec_token: verus_syn::Token![exec](span),
        });
        verus_item_const.block = Some(Box::new(verus_syn::Block {
            brace_token: verus_syn::token::Brace::default(),
            stmts: vec![verus_syn::Stmt::Expr(
                verus_syn::Expr::Verbatim(verus_item_const.expr.to_token_stream()),
                None,
            )],
        }));
        verus_item_const.eq_token = None;
        verus_item_const.expr = None;
        verus_item_const.semi_token = None;
    }
    let mut items = vec![verus_syn::Item::Const(verus_item_const)];
    crate::syntax::rewrite_items_inner(&mut items, erase_ghost, true)
}

pub(crate) fn rewrite_verus_spec_on_item_static(
    erase_ghost: EraseGhost,
    outer_attr_tokens: proc_macro::TokenStream,
    item_static: syn::ItemStatic,
) -> proc_macro::TokenStream {
    if erase_ghost.erase() {
        return item_static.to_token_stream().into();
    }
    let spec_attr =
        verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::SignatureSpecAttr);
    let mut verus_item_static = syn_to_verus_syn::<verus_syn::ItemStatic>(item_static);
    let span = verus_item_static.span();
    // Must add exec mode to static explicitly
    verus_item_static.mode =
        verus_syn::FnMode::Exec(verus_syn::ModeExec { exec_token: verus_syn::Token![exec](span) });
    if spec_attr.spec.ensures.is_some() {
        verus_item_static.ensures = spec_attr.spec.ensures;
        verus_item_static.block = Some(Box::new(verus_syn::Block {
            brace_token: verus_syn::token::Brace::default(),
            stmts: vec![verus_syn::Stmt::Expr(
                verus_syn::Expr::Verbatim(verus_item_static.expr.to_token_stream()),
                None,
            )],
        }));
        verus_item_static.eq_token = None;
        verus_item_static.expr = None;
        verus_item_static.semi_token = None;
    }
    let mut items = vec![verus_syn::Item::Static(verus_item_static)];
    crate::syntax::rewrite_items_inner(&mut items, erase_ghost, true)
}

pub(crate) fn rewrite_verus_spec_on_fun_or_loop(
    erase: EraseGhost,
    outer_attr_tokens: proc_macro::TokenStream,
    f: AnyFnOrLoop,
) -> proc_macro::TokenStream {
    match f {
        AnyFnOrLoop::Fn(mut fun) => {
            let verus_applied = match check_misuse_verus_spec(&fun.attrs, true) {
                Ok(verus_applied) => verus_applied,
                Err(error_tokens) => return error_tokens,
            };

            // Note: trait default methods appear in this case,
            // since they look syntactically like non-trait functions
            let spec_attr =
                verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::SignatureSpecAttr);

            fun.attrs.push(mk_verus_attr_syn(fun.span(), quote! { verus_macro }));

            let impl_marker = |attr: &syn::Attribute| -> Option<bool> {
                if attr.path().get_ident().map_or(true, |ident| ident != "allow") {
                    return None;
                }
                let syn::Meta::List(meta_list) = &attr.meta else {
                    return None;
                };
                let tokens = meta_list.tokens.to_string();
                if tokens.contains("verus_trait_impl_method_marker") {
                    Some(true)
                } else if tokens.contains("verus_impl_method_marker") {
                    Some(false)
                } else {
                    None
                }
            };

            // Check if the function has the impl method marker
            let impl_kind = fun.attrs.iter().find_map(&impl_marker);
            let is_impl_fn = impl_kind.is_some();
            let is_trait_impl_fn = impl_kind == Some(true);

            // Remove the marker attribute (internal use only)
            fun.attrs.retain(|attr| impl_marker(attr).is_none());

            // A method with a `with` clause expands into an unverified stub and a
            // verified counterpart. When a trait implementation is split between
            // the trait and its companion, the two sides live in different impl
            // blocks, and each is marked with which of the two it expands into.
            let emit_stub = !fun.attrs.iter().any(is_verified_trait_marker);
            let emit_counterpart = !fun.attrs.iter().any(is_companion_marker);
            fun.attrs.retain(|attr| !is_verified_trait_marker(attr) && !is_companion_marker(attr));

            let mut new_stream = TokenStream::new();
            let mut rustdoc_attrs: Vec<syn::Attribute> = vec![];
            if crate::rustdoc::env_rustdoc() {
                let mut verus_fun: verus_syn::ItemFn = syn_to_verus_syn(fun.clone());
                verus_fun.sig.spec = spec_attr.spec.clone();

                // Set return variable name
                if let Some((verus_syn::Pat::Ident(pat_ident), _)) = &spec_attr.ret_pat {
                    if let verus_syn::ReturnType::Type(_, _, opt_name, _) =
                        &mut verus_fun.sig.output
                    {
                        *opt_name = Some(Box::new((
                            verus_syn::token::Paren::default(),
                            verus_syn::Pat::Ident(pat_ident.clone()),
                            verus_syn::Token![:](pat_ident.span()),
                        )));
                    }
                }

                crate::rustdoc::process_item_fn(&mut verus_fun);

                for attr in &verus_fun.attrs {
                    if attr.path().is_ident("doc")
                        && attr.to_token_stream().to_string().contains("verusdoc_special_attr")
                    {
                        if let Ok(doc_attrs) =
                            syn::Attribute::parse_outer.parse(attr.to_token_stream().into())
                        {
                            rustdoc_attrs.extend(doc_attrs);
                        }
                    }
                }
            }

            // Create a copy of unverified function.
            // To avoid misuse of the unverified function,
            // we add `requires false` and thus prevent verified function to use it.
            // Allow unverified code to use the function without changing in/output.
            if let Some(with) = &spec_attr.spec.with {
                let span = with.with.span();
                if emit_stub {
                    let mut extra_funs =
                        rewrite_unverified_func(&mut fun, span, erase, is_trait_impl_fn);

                    if crate::rustdoc::env_rustdoc() {
                        if let Some(unverified_fun) = extra_funs.last_mut() {
                            unverified_fun.attrs.extend(rustdoc_attrs.clone());
                        }
                        fun.attrs.push(crate::syntax::mk_rust_attr_syn(
                            span,
                            "doc",
                            quote! {hidden},
                        ));
                    }
                    extra_funs.iter().for_each(|f| f.to_tokens(&mut new_stream));
                } else {
                    // The stub is the method of the trait that the companion
                    // trait belongs to, so only the rename is left to do here.
                    let x = &fun.sig.ident;
                    fun.sig.ident = syn::Ident::new(&format!("{VERIFIED}_{x}"), x.span());
                    fun.attrs.push(mk_verus_attr_syn(span, quote! { verified_with }));
                    fun.attrs.push(crate::syntax::mk_rust_attr_syn(
                        span,
                        "allow",
                        quote! {non_snake_case},
                    ));
                    if erase.erase() {
                        // The body belongs to the stub, and does not even type
                        // check against the signature of the counterpart, which
                        // returns the extra ghost/tracked outputs as well.
                        fun.block.stmts.clear();
                        fun.block.stmts.push(syn::Stmt::Expr(
                            syn::Expr::Verbatim(quote_spanned! {span => unimplemented!()}),
                            Some(syn::token::Semi { spans: [span] }),
                        ));
                    }
                    if crate::rustdoc::env_rustdoc() {
                        fun.attrs.extend(rustdoc_attrs.clone());
                    }
                }
                if !emit_counterpart {
                    return proc_macro::TokenStream::from(new_stream);
                }
            } else if crate::rustdoc::env_rustdoc() {
                fun.attrs.extend(rustdoc_attrs);
            }

            // Inject doc attribute in rustdoc mode
            if crate::rustdoc::env_rustdoc() {
                let mut verus_fun: verus_syn::ItemFn = syn_to_verus_syn(fun.clone());
                verus_fun.sig.spec = spec_attr.spec.clone();

                // Set return variable name
                if let Some((verus_syn::Pat::Ident(pat_ident), _)) = &spec_attr.ret_pat {
                    if let verus_syn::ReturnType::Type(_, _, opt_name, _) =
                        &mut verus_fun.sig.output
                    {
                        *opt_name = Some(Box::new((
                            verus_syn::token::Paren::default(),
                            verus_syn::Pat::Ident(pat_ident.clone()),
                            verus_syn::Token![:](pat_ident.span()),
                        )));
                    }
                }

                crate::rustdoc::process_item_fn(&mut verus_fun);

                for attr in &verus_fun.attrs {
                    if attr.path().is_ident("doc")
                        && attr.to_token_stream().to_string().contains("verusdoc_special_attr")
                    {
                        if let Ok(doc_attrs) =
                            syn::Attribute::parse_outer.parse(attr.to_token_stream().into())
                        {
                            fun.attrs.extend(doc_attrs);
                        }
                    }
                }
            }

            // Update function signature based on verus_spec.
            let spec_stmts =
                syntax::sig_specs_attr(erase, spec_attr, &mut fun.sig, is_impl_fn, false);

            if erase.erase() {
                // In erase mode, just return the stub functions.
                // No need to add proof statements.
                fun.to_tokens(&mut new_stream);
                return proc_macro::TokenStream::from(new_stream);
            }
            // Create const proxy function if it is a const function.
            // Skip it if it is already inside verus!
            if fun.sig.constness.is_some() && !verus_applied {
                let proxy = rewrite_const_ret_proxy(&mut fun);
                fun.to_tokens(&mut new_stream);
                fun = proxy; // Add proof and spec on proxy func.
            }

            // Add the spec/proof (requires/ensures) to the function body.
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            let _ = fun.block_mut().unwrap().stmts.splice(0..0, new_stmts);

            // Parse and replace proof_xxx!() inside function and replace panic.
            let inside_external_code = has_external_code_syn(&fun.attrs);
            replace_block(erase, fun.block_mut().unwrap(), inside_external_code);
            fun.to_tokens(&mut new_stream);
            proc_macro::TokenStream::from(new_stream)
        }
        // A method of a companion trait declares the counterpart in this mode
        // as well. Any other trait method declares itself.
        AnyFnOrLoop::TraitMethod(mut method) if erase.erase() => {
            let spec_attr =
                verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::SignatureSpecAttr);
            let declares_counterpart = method.attrs.iter().any(is_verified_trait_marker);
            method
                .attrs
                .retain(|attr| !is_verified_trait_marker(attr) && !is_companion_marker(attr));
            if !declares_counterpart || spec_attr.spec.with.is_none() {
                return method.to_token_stream().into();
            }
            let span = method.sig.ident.span();
            let x = &method.sig.ident;
            method.sig.ident = syn::Ident::new(&format!("{VERIFIED}_{x}"), x.span());
            method.attrs.push(mk_verus_attr_syn(span, quote! { verified_with }));
            method.attrs.push(crate::syntax::mk_rust_attr_syn(
                span,
                "allow",
                quote! {non_snake_case},
            ));
            let _ = syntax::sig_specs_attr(erase, spec_attr, &mut method.sig, true, false);
            method.to_token_stream().into()
        }
        // erase non-function cases if in erase mode
        _ if erase.erase() => return f.to_token_stream().into(),
        AnyFnOrLoop::Closure(mut closure) => {
            replace_expr(erase, &mut closure.body);
            let mut spec_attr =
                verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::SignatureSpecAttr);
            if let Some(_) = &spec_attr.spec.with {
                return quote_spanned! {spec_attr.span() => compile_error!("`with` does not support closure")}.into();
            }
            if let Some((verus_syn::Pat::Type(pat_ty), ar)) = spec_attr.ret_pat {
                spec_attr.ret_pat = Some((*pat_ty.pat.clone(), ar));
                closure.output = syn::ReturnType::Type(
                    syn::Token![->](pat_ty.span()),
                    Box::new(syn::Type::Verbatim(pat_ty.ty.to_token_stream())),
                );
            }
            if matches!(closure.output, syn::ReturnType::Default) {
                return quote_spanned! {closure.span() =>
                    compile_error!("Closure must have a return type, or add `$ret: $type =>` in verus_spec");
                }.into();
            }
            let mut signature = closure_to_fn_sig(&closure);
            let spec_stmts = syntax::sig_specs_attr(erase, spec_attr, &mut signature, false, true);
            let body = &closure.body;
            let new_body = quote_spanned!(closure.body.span() =>
                #(#spec_stmts)*
                {#body}
            );
            *closure.body = Expr::Verbatim(new_body);
            closure.to_token_stream().into()
        }
        AnyFnOrLoop::TraitMethod(mut method) => {
            // Note: default trait methods appear in the AnyFnOrLoop::Fn case, not here
            if let Err(error_tokens) = check_misuse_verus_spec(&method.attrs, true) {
                return error_tokens;
            }
            let spec_attr =
                verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::SignatureSpecAttr);
            let mut new_stream = TokenStream::new();

            // In a companion trait, the role of the unverified stub is played by
            // the method of the trait the companion belongs to, which is declared
            // elsewhere and cannot be given a precondition here.
            let emit_stub = !method.attrs.iter().any(is_verified_trait_marker);
            // In that trait it is the other way round: the counterpart is not a
            // member of it, and is declared by the companion trait instead.
            let emit_counterpart = !method.attrs.iter().any(is_companion_marker);
            method
                .attrs
                .retain(|attr| !is_verified_trait_marker(attr) && !is_companion_marker(attr));

            if let Some(with) = &spec_attr.spec.with {
                // An `assume_specification` function names its target with the
                // trailing call of its body, so a bodyless one cannot be linked
                // to an external function.
                if method.attrs.iter().any(is_external_fn_specification_attr) {
                    return proc_macro::TokenStream::from(quote_spanned!(with.with.span() =>
                        compile_error!("`with` on an assume_specification requires a body that calls the specified function");
                    ));
                }
                let span = with.with.span();
                // The unverified stub keeps the declared signature and gets
                // `requires(false)`, so verified code cannot call it directly.
                // The verified counterpart is declared next to it and carries the
                // extra ghost/tracked parameters and the specification.
                if emit_stub {
                    let mut stub = method.clone();
                    stub.attrs.push(mk_verus_attr_syn(span, quote! { unverified_stub }));
                    stub.attrs.push(mk_verus_attr_syn(span, quote! { verus_macro }));
                    if !crate::rustdoc::env_rustdoc() {
                        stub.attrs.push(crate::syntax::mk_rust_attr_syn(
                            span,
                            "doc",
                            quote! {hidden},
                        ));
                    }
                    let mut stub_spec_fun_opt =
                        syntax_trait::split_trait_method_syn(&stub, erase.erase());
                    let stub_spec_fun = stub_spec_fun_opt.as_mut().unwrap_or(&mut stub);
                    if let Some(block) = stub_spec_fun.block_mut() {
                        block.stmts.insert(
                            0,
                            syn::Stmt::Expr(
                                syn::Expr::Verbatim(
                                    quote_spanned_builtin!(verus_builtin, span => #verus_builtin::requires([false])),
                                ),
                                Some(syn::token::Semi { spans: [span] }),
                            ),
                        );
                    }
                    stub_spec_fun_opt.to_tokens(&mut new_stream);
                    stub.to_tokens(&mut new_stream);
                }
                if !emit_counterpart {
                    return proc_macro::TokenStream::from(new_stream);
                }
                let x = &method.sig.ident;
                method.sig.ident = syn::Ident::new(&format!("{VERIFIED}_{x}"), x.span());
                method.attrs.push(mk_verus_attr_syn(span, quote! { verified_with }));
                method.attrs.push(crate::syntax::mk_rust_attr_syn(
                    span,
                    "allow",
                    quote! {non_snake_case},
                ));
            }

            let spec_stmts = syntax::sig_specs_attr(erase, spec_attr, &mut method.sig, true, false);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            let mut spec_fun_opt = syntax_trait::split_trait_method_syn(&method, erase.erase());
            let spec_fun = spec_fun_opt.as_mut().unwrap_or(&mut method);
            let _ = spec_fun.block_mut().unwrap().stmts.splice(0..0, new_stmts);
            method.attrs.push(mk_verus_attr_syn(method.span(), quote! { verus_macro }));
            spec_fun_opt.to_tokens(&mut new_stream);
            method.to_tokens(&mut new_stream);
            proc_macro::TokenStream::from(new_stream)
        }
        AnyFnOrLoop::ForLoop(forloop) => {
            let spec_attr = verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::LoopSpec);
            syntax::for_loop_spec_attr(erase, spec_attr, forloop).to_token_stream().into()
        }
        AnyFnOrLoop::Loop(mut l) => {
            let spec_attr = verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::LoopSpec);
            let spec_stmts = syntax::while_loop_spec_attr(erase, spec_attr);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            if erase.keep() {
                l.body.stmts.splice(0..0, new_stmts);
            }
            l.to_token_stream().into()
        }
        AnyFnOrLoop::While(mut l) => {
            let spec_attr = verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::LoopSpec);
            let spec_stmts = syntax::while_loop_spec_attr(erase, spec_attr);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            if erase.keep() {
                l.body.stmts.splice(0..0, new_stmts);
            }
            l.to_token_stream().into()
        }
    }
}

pub(crate) fn proof_rewrite(erase: EraseGhost, input: TokenStream) -> proc_macro::TokenStream {
    if erase.keep() {
        let block: TokenStream =
            syntax::proof_block(erase, quote_spanned!(input.span() => {#input}).into()).into();
        quote! {
            #[verifier::proof_block]
            {
                #block;
            }
        }
        .into()
    } else {
        proc_macro::TokenStream::new()
    }
}

/// The `verus_spec(with)` annotation can be applied to either a local statement or an expression.
///
/// - When applied to an expression (`expr`), the trailing semicolon (`;`) is ignored due to limitations of the procedure macro.
///   To include the semicolon, developers must use the following syntax:
///   ```rust
///   {#[verus_spec(with ..)] expr};
///   ```
///
/// - When used with an expression, developers must explicitly declare the returned ghost or tracked patterns.
///   This is because the additional declarations cannot be automatically added in a meaningful way.
///
/// Example:
/// ```rust
/// if #[verus_io(with Tracked(arg1), Ghost(arg2) -> Tracked(out) |= Tracked(extra))]
/// call(arg0) == something {
/// }
/// ```
/// This will be transformed to the following:
/// ```rust
/// {
///     let (tmp, tmp_out) = call(arg0, Tracked(arg1), Tracked(arg2));
///     proof!{out = tmp_out.get();}  // Ensuring `out` is properly assigned.
///     (tmp, Tracked(extra))  // Returning the transformed values.
/// }
/// ```
///
/// The recommended approach for handling returned ghost/tracked outputs is to use a local statement:
///
/// Example:
/// ```rust
/// #[verus_spec(with Tracked(arg1), Ghost(arg2) -> Tracked(out) |= Tracked(extra))]
/// let out0 = call(arg0);
/// ```
/// This will be transformed to:
/// ```rust
/// let tracked mut out;
/// let out0 = {
///     let (tmp, tmp_out) = call(arg0, Tracked(arg1), Tracked(arg2));
///     proof!{out = tmp_out.get();}  // Ensure proper assignment of the ghost value.
///     (tmp, Tracked(extra))  // Returning the transformed values.
/// };
/// ```
fn rewrite_verus_spec_on_expr_local(
    erase: EraseGhost,
    attr_input: proc_macro::TokenStream,
    io_target: VerusIOTarget,
) -> proc_macro::TokenStream {
    if erase.erase() {
        return io_target.to_token_stream().into();
    }
    let call_with_spec = verus_syn::parse_macro_input!(attr_input as verus_syn::WithSpecOnExpr);
    let tokens = match io_target {
        VerusIOTarget::Local(mut local) => {
            if let Err(error_tokens) = check_misuse_verus_spec(&local.attrs, true) {
                return error_tokens;
            }
            let syn::Local { init, .. } = &mut local;
            if let Some(syn::LocalInit { expr, .. }) = init {
                let x_declares = rewrite_with_expr(erase, expr, call_with_spec);
                quote! {
                    #(#x_declares)*
                    #local
                }
            } else {
                proc_macro2::TokenStream::from(quote_spanned!(local.span() =>
                    compile_error!("with attribute cannot be applied to a local without init");
                ))
            }
        }
        VerusIOTarget::Expr(mut e) => {
            rewrite_with_expr(erase, &mut e, call_with_spec);
            e.into_token_stream()
        }
    };
    tokens.into()
}

/// Wrap an expression with a `|=` follow clause, producing a flat tuple
/// `(expr, follow_0, .., follow_n)`, which is the shape of the return type the
/// extra outputs of a `with` clause give the function.
fn apply_follows(erase: &EraseGhost, expr: &mut Expr, follow_tokens: Vec<TokenStream>) {
    let follows: Vec<TokenStream> = follow_tokens
        .into_iter()
        .map(|tokens| syntax::rewrite_expr(erase.clone(), false, tokens.into()).into())
        .collect();
    *expr = Expr::Verbatim(quote_spanned!(expr.span() => (#expr #(,#follows)*)));
}

fn is_tracked_ghost_expr(expr: &verus_syn::Expr) -> bool {
    // check expr is of the form Tracked(...) or Ghost(...)
    if let verus_syn::Expr::Call(verus_syn::ExprCall { func, .. }) = expr {
        if let verus_syn::Expr::Path(path) = func.as_ref() {
            if let Some(ident) = path.path.get_ident() {
                return ident == "Tracked" || ident == "Ghost";
            }
        }
    }
    false
}

/// Apply ghost/tracked fields in `with` clause to a struct constructor expression.
/// Return Err if the ghost/tracked fields are not valid.
fn apply_erased_fields<'a>(
    erase: EraseGhost,
    expr: &mut Expr,
    erased_fields: impl Iterator<Item = &'a verus_syn::FieldValue>,
) -> Result<(), ()> {
    let syn::Expr::Struct(expr_struct) = expr else {
        // If there's no struct constructor, we cannot apply ghost/tracked fields.
        if let Some(field) = erased_fields.last() {
            *expr = syn::Expr::Verbatim(quote_spanned! {field.span() =>
                compile_error!("Ghost/tracked fields can only be applied to struct constructors.")
            });
            return Err(());
        }
        // No ghost/tracked fields, just return.
        return Ok(());
    };
    for field in erased_fields {
        let rewritten =
            syntax::rewrite_expr(erase.clone(), false, field.expr.to_token_stream().into());
        let verus_syn::Member::Named(field_name) = &field.member else {
            *expr = syn::Expr::Verbatim(quote_spanned! {field.member.span() =>
                compile_error!("A ghost/tracked field must be a named field.")
            });
            return Err(());
        };
        if !is_tracked_ghost_expr(&field.expr) {
            *expr = syn::Expr::Verbatim(quote_spanned! {field.expr.span() =>
                compile_error!("A ghost/tracked field must be a tracked/ghost expression. If you want to add ghost/tracked fields to a struct constructor, you should use $ident: Tracked/Ghost($ident).")
            });
            return Err(());
        }
        assert!(field.attrs.is_empty()); // guarded by verus_syn::WithSpecOnExpr parsing
        let extra_field = syn::FieldValue {
            attrs: vec![],
            member: syn::Member::Named(field_name.clone()),
            colon_token: field.colon_token.and_then(|c| Some(syn::Token![:](c.span()))),
            expr: syn::Expr::Verbatim(rewritten.into()),
        };
        expr_struct.fields.push(extra_field);
    }
    return Ok(());
}

// Expand `with extra_in => extra_out` on a method call expr.
// Return some pre-statements that needs to be declared before the expr.
fn rewrite_with_expr(
    erase: EraseGhost,
    expr: &mut Expr,
    call_with_spec: verus_syn::WithSpecOnExpr,
) -> Vec<verus_syn::Stmt> {
    let verus_syn::WithSpecOnExpr { inputs, outputs, follows, erased_fields, .. } = call_with_spec;

    if outputs.is_some() || inputs.len() > 0 {
        match expr {
            syn::Expr::Call(_) | syn::Expr::MethodCall(_) => {
                let elems = inputs
                    .iter()
                    .map(|arg| {
                        syn::Expr::Verbatim(
                            syntax::rewrite_expr(
                                erase.clone(),
                                false,
                                arg.into_token_stream().into(),
                            )
                            .into(),
                        )
                    })
                    .collect::<Punctuated<syn::Expr, syn::Token![,]>>();

                let inputs_expr = syn::Expr::Tuple(syn::ExprTuple {
                    attrs: vec![],
                    paren_token: syn::token::Paren::default(),
                    elems,
                });
                *expr = if outputs.is_some() {
                    syn::Expr::Verbatim(quote_spanned_builtin!(verus_builtin, expr.span() =>
                        #verus_builtin::proof_with(#inputs_expr, #expr)
                    ))
                } else {
                    syn::Expr::Verbatim(quote_spanned_builtin!(verus_builtin, expr.span() => {
                        #verus_builtin::proof_with_ret(#inputs_expr, #expr)
                    }))
                };
            }
            syn::Expr::Try(syn::ExprTry { expr, .. }) => {
                let call_with_spec = verus_syn::WithSpecOnExpr {
                    inputs,
                    outputs,
                    follows,
                    erased_fields,
                    ..call_with_spec
                };
                return rewrite_with_expr(erase, expr, call_with_spec);
            }
            _ => {
                *expr = Expr::Verbatim(quote_spanned!(expr.span() =>
                    compile_error!("with ghost inputs/outputs cannot be applied to a non-call expression. You may want to use proof_with!(|= var) to append a ghost var to the expr.")
                ));
                return vec![];
            }
        }
    }

    if apply_erased_fields(erase.clone(), expr, erased_fields.iter()).is_err() {
        return vec![];
    }
    let x_declares = if let Some((_, extra_pat)) = outputs {
        // The expected pat.
        let tmp_pat =
            verus_syn::Pat::Verbatim(quote_spanned! {expr.span() => __verus_tmp_expr_var__});
        let mut elems =
            verus_syn::punctuated::Punctuated::<verus_syn::Pat, verus_syn::Token![,]>::new();
        elems.push(tmp_pat.clone());
        // Several extra outputs are returned as one flat tuple, so a tuple
        // pattern `=> (a, b)` has to be flattened to match it.
        match extra_pat {
            verus_syn::Pat::Tuple(tuple) => elems.extend(tuple.elems),
            pat => elems.push(pat),
        }
        // The actual pat.
        let mut pat = verus_syn::Pat::Tuple(verus_syn::PatTuple {
            attrs: vec![],
            paren_token: verus_syn::token::Paren::default(),
            elems,
        });
        let (x_declares, x_assigns) = syntax::rewrite_exe_pat(&mut pat);
        *expr = syn::Expr::Verbatim(quote_spanned! {expr.span() => {
            let #pat = #expr;
            proof!{
                #(#x_assigns)*
            }
            #tmp_pat
        }
        });
        x_declares
    } else {
        vec![]
    };
    if let Some((_, follow)) = follows {
        // A tuple pattern `|= (a, b)` supplies several extra outputs, which the
        // function returns as the flat tuple `(ret, a, b)`.
        let follow_tokens = match follow {
            verus_syn::Pat::Tuple(tuple) => {
                tuple.elems.iter().map(|p| p.to_token_stream()).collect()
            }
            pat => vec![pat.to_token_stream()],
        };
        apply_follows(&erase, expr, follow_tokens);
    }
    x_declares
}

/// Rewrite the const function and return a proxy function.
fn rewrite_const_ret_proxy(const_fun: &mut syn::ItemFn) -> syn::ItemFn {
    // This function is used to rewrite a const function to link it to a proxy function
    // that can be used to verify code.
    // It seems that we do not need to erase anything.
    // But just do it to be safe and consistent with verus macro.
    let span = const_fun.sig.constness.unwrap().span();
    let mut proxy_fun = const_fun.clone();
    let inside_external_code = has_external_code_syn(&const_fun.attrs);
    replace_block(EraseGhost::Erase, const_fun.block_mut().unwrap(), inside_external_code);
    const_fun.attrs.push(mk_verifier_attr_syn(span, quote! { external }));
    const_fun.attrs.push(mk_verus_attr_syn(span, quote! { uses_unerased_proxy }));
    const_fun.attrs.push(mk_verus_attr_syn(span, quote! { encoded_const }));

    proxy_fun.sig.ident = syn::Ident::new(
        &format!("{VERUS_UNERASED_PROXY}{}", const_fun.sig.ident),
        const_fun.sig.ident.span(),
    );
    proxy_fun.attrs.push(mk_verus_attr_syn(span, quote! { unerased_proxy }));
    proxy_fun.attrs.push(crate::syntax::mk_rust_attr_syn(span, "allow", quote! { non_snake_case }));
    proxy_fun
}

/// Returns true for `#[verifier::assume_specification]` and
/// `#[verifier::external_fn_specification]`, in either the `verifier::x` or the
/// `verifier(x)` form.
fn is_external_fn_specification_attr(attr: &syn::Attribute) -> bool {
    let is_name = |n: &str| n == "assume_specification" || n == "external_fn_specification";
    let segments: Vec<String> = attr.path().segments.iter().map(|s| s.ident.to_string()).collect();
    match segments.as_slice() {
        [verifier, name] if verifier == "verifier" => is_name(name),
        [verifier] if verifier == "verifier" => match &attr.meta {
            syn::Meta::List(list) => list
                .parse_args::<syn::Path>()
                .ok()
                .and_then(|p| p.get_ident().map(|i| is_name(&i.to_string())))
                .unwrap_or(false),
            _ => false,
        },
        _ => false,
    }
}

/// What a `with` clause expands into, per erasure mode.
///
/// `#[verus_spec(with Tracked(t): Tracked<u8>)] fn f(x: u8) -> bool { body }`
///
/// | mode       | when                 | stub `f`                           | counterpart `_VERUS_VERIFIED_f`     |
/// |------------|----------------------|------------------------------------|-------------------------------------|
/// | `Keep`     | verification         | `external_body`, `requires(false)` | extra params, `body`, specification |
/// | `Erase`    | compilation by verus | `body`: this is what executes      | extra params, `unimplemented!()`    |
/// | `EraseAll` | standard rust tools  | `f` as written                     | not declared                        |
///
/// The counterpart is declared in `Erase` mode because a crate depending on this
/// one resolves the callee of a `proof_with!` call against the metadata compiled
/// in that mode, while its specification comes from the vir metadata exported in
/// `Keep` mode. The two are matched by path, so what `Erase` mode declares has
/// to have the name, the signature and the enclosing item that `Keep` mode gives
/// it -- for a method, that means the companion trait and an implementation of
/// it. The body is never run: `proof_with!` is erased along with the ghost code,
/// so every call goes to the stub.
///
/// If the function is const, it is rewritten to a proxy function and a verified
/// function.
///
/// For an `assume_specification`, the stub stays the real `assume_specification`:
/// it keeps the exact signature and the body whose trailing call names the
/// specified function, and only gains `requires(false)`. The counterpart carries
/// the extra ghost/tracked parameters and the user's specification, and is a
/// plain `external_body` function.
fn rewrite_unverified_func(
    fun: &mut syn::ItemFn,
    span: proc_macro2::Span,
    erase: EraseGhost,
    is_trait_impl_fn: bool,
) -> Vec<syn::ItemFn> {
    let is_assume_spec = fun.attrs.iter().any(is_external_fn_specification_attr);
    let mut ret = vec![];
    let mut unverified_fun = fun.clone();
    if fun.sig.constness.is_some() && !is_assume_spec {
        // Create a proxy function to include requires/ensures.
        let proxy = rewrite_const_ret_proxy(&mut unverified_fun);
        ret.push(unverified_fun);
        unverified_fun = proxy;
    }
    let unimplemented = syn::Stmt::Expr(
        syn::Expr::Verbatim(quote_spanned! {span => unimplemented!()}),
        Some(syn::token::Semi { spans: [span] }),
    );
    let precondition_false = syn::Stmt::Expr(
        syn::Expr::Verbatim(
            quote_spanned_builtin!(verus_builtin, span => #verus_builtin::requires([false])),
        ),
        Some(syn::token::Semi { spans: [span] }),
    );
    if !is_assume_spec {
        // `assume_specification` already implies an external body, and marking it
        // `external_body` explicitly is rejected.
        unverified_fun.attrs_mut().push(mk_verus_attr_syn(span, quote! { external_body }));
    }
    if !crate::rustdoc::env_rustdoc() {
        unverified_fun.attrs_mut().push(crate::syntax::mk_rust_attr_syn(
            span,
            "doc",
            quote! {hidden},
        ));
    }
    if let Some(block) = unverified_fun.block_mut() {
        // The body of the stub is dropped in `Keep` mode: it is not verified,
        // and the proof code in it names ghost variables the stub does not
        // take. It is kept in `Erase` mode, where it is what executes.
        if erase.keep() {
            if is_assume_spec {
                // Keep the body: its trailing call names the specified function.
                block.stmts.insert(0, precondition_false);
            } else {
                block.stmts.clear();
                // A trait implementation cannot declare its own `requires`: it
                // inherits `requires(false)` from the trait declaration.
                if !is_trait_impl_fn {
                    block.stmts.push(precondition_false);
                }
                block.stmts.push(unimplemented.clone());
            }
        }
    }
    // change name to verified_{fname}
    let x = &fun.sig.ident;
    fun.sig.ident = syn::Ident::new(&format!("{VERIFIED}_{x}"), x.span());
    fun.attrs.push(mk_verus_attr_syn(span, quote! { verified_with }));
    fun.attrs.push(crate::syntax::mk_rust_attr_syn(span, "allow", quote! {non_snake_case}));

    if is_assume_spec {
        // The verified counterpart has extra parameters, so it cannot itself be an
        // `assume_specification`; it is an ordinary function whose specification is
        // assumed for the external function it stands in for.
        fun.attrs.retain(|attr| !is_external_fn_specification_attr(attr));
        fun.attrs.push(mk_verus_attr_syn(span, quote! { external_body }));
        fun.block.stmts.clear();
        fun.block.stmts.push(unimplemented);
    } else if erase.erase() {
        // The other way round for the counterpart: only the stub is called.
        fun.block.stmts.clear();
        fun.block.stmts.push(unimplemented);
    }
    ret.push(unverified_fun);
    // Mark every unverified item, so that rust_verify can redirect
    // `proof_with(.., f(..))` calls to the verified counterpart, which is the
    // sibling named `_VERUS_VERIFIED_{name}`.
    // A const function also produces an unerased proxy, and a call site may resolve
    // to either of them, so both carry the marker.
    for unverified_fun in ret.iter_mut() {
        unverified_fun.attrs_mut().push(mk_verus_attr_syn(span, quote! { unverified_stub }));
    }
    ret
}
