#![feature(proc_macro_hygiene)]
// The upstream half of the cross-crate `with` tests: a trait whose methods
// declare extra ghost arguments, and a free function that does the same. The
// downstream crates implement, inherit and call these.
use vstd::prelude::*;

#[verus_spec(ret =>
    with Ghost(g): Ghost<u64>
    requires g > 0,
    ensures ret == a,
)]
pub fn upstream_fn(a: u64) -> u64 {
    a
}

#[verus_verify]
pub trait Doubler {
    // no default body: a downstream impl must supply one, and its `with`
    // clause has to conform to this one
    #[verus_spec(ret =>
        with Ghost(g): Ghost<u64>
        requires g > 0, a < 100,
        ensures ret == 2 * a,
    )]
    fn double(&self, a: u64) -> u64;

    // a default body, which a downstream impl may inherit: the capability this
    // design exists to deliver
    #[verus_spec(ret =>
        with Ghost(g): Ghost<u64>
        requires g > 0, a < 50,
        ensures ret == 4 * a,
    )]
    fn quadruple(&self, a: u64) -> u64 {
        proof_with!{Ghost(g)}
        let d = self.double(a);
        proof_with!{Ghost(g)}
        self.double(d)
    }
}

// a borrowing extra, whose lifetime the downstream impl must not narrow
#[verus_verify]
pub trait Borrower {
    #[verus_spec(with Ghost(g): Ghost<&'a u64>)]
    fn borrow_it<'a>(&self, g: &'a u64);
}
