// rust_verify/tests/example.rs expect-failures

extern crate builtin;
#[allow(unused_imports)]
use builtin::*;
mod pervasive;
#[allow(unused_imports)]
use pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::{*, seq::*, vec::*, map::*, set::*};

fn main() {}

// hmm, might not be finite
#[proof]
fn test_set() {
    let nonneg = Set::new(|i: int| i >= 0);
    let pos1 = nonneg.filter(|i: int| i > 0);
}