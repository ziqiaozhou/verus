#![feature(proc_macro_hygiene)]
// Calling an upstream shim directly, rather than through `proof_with`.
use vstd::prelude::*;
use with_extras_lib::*;

#[verus_verify]
fn call_the_shim() -> u64 {
    _VERUS_WITH_upstream_fn(7, Ghost::assume_new())
}

fn main() {
    call_the_shim();
}
