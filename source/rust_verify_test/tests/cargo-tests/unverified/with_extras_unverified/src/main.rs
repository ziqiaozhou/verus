// Building without Verus at all: the extras are erased entirely, so the
// upstream functions are called with their executable arguments only.
use with_extras_lib::*;

struct S;

impl Doubler for S {
    fn double(&self, a: u64) -> u64 {
        a + a
    }
}

fn main() {
    let s = S;
    println!("{} {} {}", upstream_fn(7), s.double(5), s.quadruple(3));
}
