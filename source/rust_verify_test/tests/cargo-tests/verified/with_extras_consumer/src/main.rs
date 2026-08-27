#![feature(proc_macro_hygiene)]
// A downstream crate that calls an upstream `with` function, implements an
// upstream `with` trait conformingly, and inherits an upstream default body.
use vstd::prelude::*;
use with_extras_lib::*;

#[verus_verify]
struct S;

// the impl's `with` clause matches the trait's
#[verus_verify]
impl Doubler for S {
    #[verus_spec(with Ghost(g): Ghost<u64>)]
    fn double(&self, a: u64) -> u64 {
        a + a
    }
}

// `quadruple` is not implemented here: it is inherited from the upstream
// default body, extras and all
#[verus_verify]
fn use_inherited_default_body() {
    let s = S;
    proof_with!{Ghost(1u64)}
    let r = s.quadruple(3);
    proof!{ assert(r == 12); }
}

#[verus_verify]
fn call_upstream_fn() {
    proof_with!{Ghost(1u64)}
    let r = upstream_fn(7);
    proof!{ assert(r == 7); }
}

#[verus_verify]
fn call_downstream_impl() {
    let s = S;
    proof_with!{Ghost(1u64)}
    let r = s.double(5);
    proof!{ assert(r == 10); }
}

fn main() {
    call_upstream_fn();
    call_downstream_impl();
    use_inherited_default_body();
}
