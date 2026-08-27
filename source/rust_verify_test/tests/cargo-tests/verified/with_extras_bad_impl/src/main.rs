#![feature(proc_macro_hygiene)]
// A downstream impl that does not conform to the upstream trait's `with`
// clause: the trait declares `Ghost<u64>`, this declares `Ghost<u32>`. Callers
// are checked against the trait's shim, so an impl that assumes more than the
// trait promised has to be rejected here.
use vstd::prelude::*;
use with_extras_lib::*;

#[verus_verify]
struct S;

#[verus_verify]
impl Doubler for S {
    #[verus_spec(with Ghost(g): Ghost<u32>)]
    fn double(&self, a: u64) -> u64 {
        a + a
    }
}

fn main() {}
