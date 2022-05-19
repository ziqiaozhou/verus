use proc_macro::Span;
use proc_macro2::{Delimiter, Group, Spacing, TokenStream, TokenTree};
use quote::quote_spanned;
use std::collections::HashSet;
use syn::punctuated::Punctuated;
use syn::token::Paren;
use syn::visit_mut::{visit_expr_mut, VisitMut};
use syn::{parse_macro_input, parse_quote_spanned, Expr, ExprCall};

struct SpanId(Span);

impl PartialEq for SpanId {
    fn eq(&self, other: &SpanId) -> bool {
        self.0.eq(&other.0)
    }
}

impl Eq for SpanId {}

impl std::hash::Hash for SpanId {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.start().line.hash(state);
    }
}

#[derive(Default)]
struct ItemState {
    mode: Vec<TokenTree>,
    visibility: Vec<TokenTree>,
}

struct SpanState {
    implies: HashSet<SpanId>,
    equal: HashSet<SpanId>,
}

pub(crate) struct ExprState {
    spans: SpanState,
}

impl ExprState {
    pub(crate) fn new() -> ExprState {
        let spans = SpanState { implies: HashSet::new(), equal: HashSet::new() };
        ExprState { spans }
    }
}

enum Cluster {
    Fn,
    Spec,
    Proof,
    Exec,
    Imply,
    Equal,
    NotEqual,
    Lt,
    Gt,
    Arrow(TokenTree, TokenTree, Option<(TokenTree, TokenTree)>),
    Visibility(Vec<TokenTree>),
}

// Match the biggest possible token cluster on the top of the stack.
// Example: if the stack contains '-', '>', match as "->", not as "-" then ">".
fn peek_cluster(input_rev: &Vec<TokenTree>) -> Option<(proc_macro2::Span, usize, Cluster)> {
    let len = input_rev.len();
    if len >= 4 {
        let t0 = &input_rev[len - 1];
        let t1 = &input_rev[len - 2];
        let t2 = &input_rev[len - 3];
        let t3 = &input_rev[len - 4];
        let span = t0.span();
        match (t0, t1, t2, t3) {
            (
                TokenTree::Punct(p0),
                TokenTree::Punct(p1),
                TokenTree::Ident(_),
                TokenTree::Punct(p3),
            ) if p0.as_char() == '-'
                && p1.as_char() == '>'
                && p3.as_char() == ':'
                && p0.spacing() == Spacing::Joint
                && p1.spacing() == Spacing::Alone
                && p3.spacing() == Spacing::Alone =>
            {
                // -> x:
                let param = Some((t2.clone(), t3.clone()));
                return Some((span, 4, Cluster::Arrow(t0.clone(), t1.clone(), param)));
            }
            _ => {}
        }
    }
    if len >= 3 {
        let t0 = &input_rev[len - 1];
        let t1 = &input_rev[len - 2];
        let t2 = &input_rev[len - 3];
        let span = t0.span();
        match (t0, t1, t2) {
            (TokenTree::Punct(p0), TokenTree::Punct(p1), TokenTree::Punct(p2))
                if p0.as_char() == '='
                    && p1.as_char() == '='
                    && p2.as_char() == '>'
                    && p0.spacing() == Spacing::Joint
                    && p1.spacing() == Spacing::Joint
                    && p2.spacing() == Spacing::Alone =>
            {
                return Some((span, 3, Cluster::Imply));
            }
            (TokenTree::Punct(p0), TokenTree::Punct(p1), TokenTree::Punct(p2))
                if p0.as_char() == '='
                    && p1.as_char() == '='
                    && p2.as_char() == '='
                    && p0.spacing() == Spacing::Joint
                    && p1.spacing() == Spacing::Joint
                    && p2.spacing() == Spacing::Alone =>
            {
                return Some((span, 3, Cluster::Equal));
            }
            (TokenTree::Punct(p0), TokenTree::Punct(p1), TokenTree::Punct(p2))
                if p0.as_char() == '!'
                    && p1.as_char() == '='
                    && p2.as_char() == '='
                    && p0.spacing() == Spacing::Joint
                    && p1.spacing() == Spacing::Joint
                    && p2.spacing() == Spacing::Alone =>
            {
                return Some((span, 3, Cluster::NotEqual));
            }
            _ => {}
        }
    }
    if len >= 2 {
        let t0 = &input_rev[len - 1];
        let t1 = &input_rev[len - 2];
        let span = t0.span();
        match (t0, t1) {
            (TokenTree::Punct(p0), TokenTree::Punct(p1))
                if p0.as_char() == '-'
                    && p1.as_char() == '>'
                    && p0.spacing() == Spacing::Joint
                    && p1.spacing() == Spacing::Alone =>
            {
                return Some((span, 2, Cluster::Arrow(t0.clone(), t1.clone(), None)));
            }
            (TokenTree::Ident(x0), TokenTree::Group(g1))
                if x0 == "pub" && g1.delimiter() == Delimiter::Parenthesis =>
            {
                let vis = vec![t0.clone(), t1.clone()];
                return Some((span, 2, Cluster::Visibility(vis)));
            }
            _ => {}
        }
    }
    if len >= 1 {
        let t0 = &input_rev[len - 1];
        let span = t0.span();
        match t0 {
            TokenTree::Punct(p) if p.as_char() == '<' => return Some((span, 1, Cluster::Lt)),
            TokenTree::Punct(p) if p.as_char() == '>' => return Some((span, 1, Cluster::Gt)),
            TokenTree::Ident(x) if x == "pub" => {
                return Some((span, 1, Cluster::Visibility(vec![t0.clone()])));
            }
            TokenTree::Ident(x) if x == "fn" => return Some((span, 1, Cluster::Fn)),
            TokenTree::Ident(x) if x == "spec" => return Some((span, 1, Cluster::Spec)),
            TokenTree::Ident(x) if x == "proof" => return Some((span, 1, Cluster::Proof)),
            TokenTree::Ident(x) if x == "exec" => return Some((span, 1, Cluster::Exec)),
            _ => {}
        }
    }
    None
}

fn pop_cluster(input_rev: &mut Vec<TokenTree>, pop: usize) {
    for _ in 0..pop {
        input_rev.pop();
    }
}

fn pop_cluster_into(input_rev: &mut Vec<TokenTree>, output: &mut Vec<TokenTree>, pop: usize) {
    for _ in 0..pop {
        output.push(input_rev.pop().expect("pop_cluster_into"));
    }
}

pub(crate) fn rewrite_expr_tree(state: &mut ExprState, tree: TokenTree) -> Vec<TokenTree> {
    match tree {
        TokenTree::Group(group) => {
            let stream = rewrite_expr_stream(state, group.stream());
            let mut new_group = TokenTree::Group(Group::new(group.delimiter(), stream));
            new_group.set_span(group.span());
            vec![new_group]
        }
        _ => vec![tree],
    }
}

pub(crate) fn rewrite_expr_stream(state: &mut ExprState, input: TokenStream) -> TokenStream {
    let mut input_rev: Vec<TokenTree> = input.into_iter().collect();
    input_rev.reverse();
    let mut output: Vec<TokenTree> = Vec::new();
    while !input_rev.is_empty() {
        match peek_cluster(&input_rev) {
            Some((span, pop, Cluster::Imply)) => {
                pop_cluster(&mut input_rev, pop);
                output.extend(quote_spanned! { span => >>= }.into_iter());
                state.spans.implies.insert(SpanId(span.unwrap()));
            }
            Some((span, pop, Cluster::Equal)) => {
                pop_cluster(&mut input_rev, pop);
                output.extend(quote_spanned! { span => == }.into_iter());
                state.spans.equal.insert(SpanId(span.unwrap()));
            }
            Some((span, pop, Cluster::NotEqual)) => {
                pop_cluster(&mut input_rev, pop);
                output.extend(quote_spanned! { span => != }.into_iter());
                state.spans.equal.insert(SpanId(span.unwrap()));
            }
            _ => {
                output.extend(rewrite_expr_tree(state, input_rev.pop().unwrap()));
            }
        }
    }
    let mut new_stream = TokenStream::new();
    new_stream.extend(output.into_iter());
    new_stream
}

struct Visitor {
    state: ExprState,
}
impl VisitMut for Visitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        visit_expr_mut(self, expr);
        if let Expr::AssignOp(assign) = expr {
            if let syn::BinOp::ShrEq(_) = assign.op {
                use syn::spanned::Spanned;
                if self.state.spans.implies.contains(&SpanId(assign.op.span().unwrap())) {
                    let span = assign.span();
                    let attrs = std::mem::take(&mut assign.attrs);
                    let func = parse_quote_spanned!(span => ::builtin::imply);
                    let paren_token = Paren { span };
                    let mut args = Punctuated::new();
                    let dummy: Expr = parse_quote_spanned!(span => ());
                    args.push(std::mem::replace(&mut *assign.left, dummy.clone()));
                    args.push(std::mem::replace(&mut *assign.right, dummy));
                    *expr = Expr::Call(ExprCall { attrs, func, paren_token, args });
                }
            }
        }
        if let Expr::Binary(binary) = expr {
            let eq = match binary.op {
                syn::BinOp::Eq(_) => Some(true),
                syn::BinOp::Ne(_) => Some(false),
                _ => None,
            };
            if let Some(eq) = eq {
                use syn::spanned::Spanned;
                if self.state.spans.equal.contains(&SpanId(binary.op.span().unwrap())) {
                    let span = binary.span();
                    let attrs = std::mem::take(&mut binary.attrs);
                    let func = parse_quote_spanned!(span => ::builtin::equal);
                    let paren_token = Paren { span };
                    let mut args = Punctuated::new();
                    let dummy: Expr = parse_quote_spanned!(span => ());
                    args.push(std::mem::replace(&mut *binary.left, dummy.clone()));
                    args.push(std::mem::replace(&mut *binary.right, dummy));
                    let call = Expr::Call(ExprCall { attrs, func, paren_token, args });
                    if eq {
                        *expr = call;
                    } else {
                        *expr = parse_quote_spanned!(span => ! #call);
                    }
                }
            }
        }
    }
}

pub(crate) fn rewrite_expr(
    state: ExprState,
    stream: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let mut expr: Expr = parse_macro_input!(stream as Expr);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor { state };
    visitor.visit_expr_mut(&mut expr);
    expr.to_tokens(&mut new_stream);
    proc_macro::TokenStream::from(new_stream)
}

pub(crate) fn rewrite_fun_tree(tree: TokenTree) -> (Vec<TokenTree>, bool) {
    match tree {
        TokenTree::Group(group) if group.delimiter() == Delimiter::Brace => {
            let mut state = ExprState::new();
            let stream = TokenStream::from(TokenTree::Group(group));
            let stream = rewrite_expr_stream(&mut state, stream);
            let stream = proc_macro::TokenStream::from(stream);
            let stream = rewrite_expr(state, stream);
            let stream = proc_macro2::TokenStream::from(stream);
            (stream.into_iter().collect(), true)
        }
        _ => (vec![tree], false),
    }
}

fn skip_generics(input_rev: &mut Vec<TokenTree>, output: &mut Vec<TokenTree>) {
    let mut depth = 0;
    while input_rev.len() > 0 {
        match peek_cluster(input_rev) {
            Some((_, _, Cluster::Lt)) => {
                depth += 1;
                output.push(input_rev.pop().unwrap());
            }
            Some((_, _, Cluster::Gt)) => {
                depth -= 1;
                output.push(input_rev.pop().unwrap());
            }
            Some((_, pop, _)) => {
                // This covers the -> case, which we don't want to treat as - followed by Gt.
                pop_cluster_into(input_rev, output, pop);
            }
            None => {
                output.push(input_rev.pop().unwrap());
            }
        }
        if depth == 0 {
            break;
        }
    }
}

fn skip_return_type(input_rev: &mut Vec<TokenTree>, output: &mut Vec<TokenTree>) {
    while let Some(x) = input_rev.last() {
        match x {
            TokenTree::Group(group) if group.delimiter() == Delimiter::Brace => {
                // function body
                break;
            }
            TokenTree::Ident(x) if x == "where" => {
                break;
            }
            _ => {
                output.push(input_rev.pop().unwrap());
            }
        }
    }
}

fn rewrite_fun_stream(
    item_state: &mut ItemState,
    input_rev: &mut Vec<TokenTree>,
    fun_token: TokenTree,
) -> TokenStream {
    let mut _ret_name: Option<(TokenTree, TokenTree)> = None;
    let mut ret_type: Vec<TokenTree> = Vec::new();
    let mut output: Vec<TokenTree> = Vec::new();

    if let Some(fun_name) = input_rev.pop() {
        output.push(fun_name);
    }
    skip_generics(input_rev, &mut output);
    if let Some(params) = input_rev.pop() {
        output.push(params);
    }

    if let Some((_, pop, Cluster::Arrow(t0, t1, ret))) = peek_cluster(input_rev) {
        pop_cluster(input_rev, pop);
        output.push(t0);
        output.push(t1);
        _ret_name = ret;
        skip_return_type(input_rev, &mut ret_type);
        output.extend(ret_type.clone());
    }

    // handle where clause, function body
    while !input_rev.is_empty() {
        match peek_cluster(input_rev) {
            _ => {
                let (xtree, done) = rewrite_fun_tree(input_rev.pop().unwrap());
                output.extend(xtree);
                if done {
                    break;
                }
            }
        }
    }

    let mut new_stream = TokenStream::new();
    new_stream.extend(item_state.mode.drain(..));
    new_stream.extend(item_state.visibility.drain(..));
    new_stream.extend(vec![fun_token]);
    new_stream.extend(output.into_iter());
    new_stream
}

pub(crate) fn rewrite_items_tree(tree: TokenTree) -> Vec<TokenTree> {
    vec![tree]
}

pub(crate) fn rewrite_items_stream(input: TokenStream) -> TokenStream {
    let mut item_state: ItemState = Default::default();
    let mut input_rev: Vec<TokenTree> = input.into_iter().collect();
    input_rev.reverse();
    let mut output: Vec<TokenTree> = Vec::new();
    while !input_rev.is_empty() {
        match peek_cluster(&input_rev) {
            Some((_, pop, Cluster::Visibility(vis))) => {
                pop_cluster(&mut input_rev, pop);
                item_state.visibility = vis;
            }
            Some((_, _, Cluster::Fn)) => {
                let fun_token = input_rev.pop().unwrap();
                output.extend(rewrite_fun_stream(&mut item_state, &mut input_rev, fun_token));
            }
            Some((span, pop, Cluster::Spec)) => {
                pop_cluster(&mut input_rev, pop);
                item_state.mode.extend(quote_spanned! { span => #[spec] }.into_iter());
            }
            Some((span, pop, Cluster::Proof)) => {
                pop_cluster(&mut input_rev, pop);
                item_state.mode.extend(quote_spanned! { span => #[proof] }.into_iter());
            }
            Some((span, pop, Cluster::Exec)) => {
                pop_cluster(&mut input_rev, pop);
                item_state.mode.extend(quote_spanned! { span => #[exec] }.into_iter());
            }
            _ => {
                output.extend(rewrite_items_tree(input_rev.pop().unwrap()));
            }
        }
    }
    let mut new_stream = TokenStream::new();
    new_stream.extend(output.into_iter());
    new_stream
}
