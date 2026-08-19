#![feature(proc_macro_hygiene)]

use proof_with_lib::{negate, Counter, Doubler, Twice};
use vstd::prelude::*;

// `proof_with!` on a function of another crate: the call is redirected to the
// verified counterpart imported from `proof_with_lib`.
#[verus_spec(
    with Tracked(t): Tracked<u8>
    requires t == 1u8,
)]
pub fn call_free_function() {
    proof_with!{Tracked(t)}
    let r = negate(true, 1);
    proof!{ assert(r == false); }
}

// The same for a method of an inherent implementation, including an extra
// tracked output.
#[verus_spec(
    with Tracked(t): Tracked<u8>
    requires t == 1u8,
)]
pub fn call_method(c: &Counter) {
    proof_with!{Tracked(t) => Tracked(next)}
    let r = c.bump();
    proof!{
        assert(r == 7u8);
        assert(next == 1u8);
    }
}

// Without `proof_with!`, the call goes to the unverified stub, which is exec
// code that any crate can compile and run.
pub fn call_stub() -> bool {
    negate(true, 1)
}

// A trait method of another crate: the call is redirected to the counterpart
// the companion trait of `proof_with_lib` declares.
#[verus_spec(
    with Ghost(g): Ghost<u64>
    requires g < 100,
)]
pub fn call_trait_method(t: &Twice) {
    proof_with!{Ghost(g)}
    let r = t.double(3);
    proof!{ assert(r == 6u64); }
}
