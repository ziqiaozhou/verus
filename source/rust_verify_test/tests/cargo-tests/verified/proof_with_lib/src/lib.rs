use vstd::prelude::*;

// A function with a `with` clause expands into an unverified stub, which keeps
// the exec signature the caller sees, and a verified counterpart, which takes
// the extra ghost/tracked parameters. The counterpart must reach the crate
// metadata so that a dependent crate can redirect a `proof_with!` call to it.
#[verus_spec(ret =>
    with Tracked(expected): Tracked<u8>
    requires x == expected,
    ensures ret == !b,
)]
pub fn negate(b: bool, x: u8) -> bool {
    !b
}

#[verus_verify]
pub struct Counter(pub u8);

#[verus_verify]
impl Counter {
    #[verus_spec(ret =>
        with Tracked(step): Tracked<u8> -> next: Tracked<u8>
        requires step == 1u8,
        ensures ret == 7u8, next@ == step,
    )]
    pub fn bump(&self) -> u8 {
        proof_with!{|= Tracked(step)}
        7
    }
}

// The counterpart of a trait method belongs to the companion trait declared
// next to the trait. Both have to reach the crate metadata, as does the
// implementation of the companion trait.
#[verus_verify]
pub trait Doubler {
    #[verus_spec(ret =>
        with Ghost(g): Ghost<u64>
        requires g < 100, a < 100,
        ensures ret == a + a,
    )]
    fn double(&self, a: u64) -> u64;
}

#[verus_verify]
pub struct Twice;

#[verus_verify]
impl Doubler for Twice {
    #[verus_spec(with Ghost(g): Ghost<u64>)]
    fn double(&self, a: u64) -> u64 {
        a + a
    }
}
