#![feature(proc_macro_hygiene)]
// A call site that disagrees with the upstream arity: `upstream_fn` declares one
// extra, this supplies two. A downstream crate has no body to scan, so its view
// of the arity comes from the shim.
use vstd::prelude::*;
use with_extras_lib::*;

#[verus_verify]
fn call_upstream_fn() -> u64 {
    proof_with!{Ghost(1u64), Ghost(2u64)}
    upstream_fn(7)
}

fn main() {
    call_upstream_fn();
}
