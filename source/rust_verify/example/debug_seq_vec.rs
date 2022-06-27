// rust_verify/tests/example.rs expect-failures

extern crate builtin;
#[allow(unused_imports)]
use builtin::*;
mod pervasive;
#[allow(unused_imports)]
use pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::{*, seq::*, vec::*};

fn main() {}


// Example 1: Simple Sequence
#[proof]
fn seq_first_elt_is_10(v: Seq<u32>) -> u32 {
    requires([
        // v.len() == 0,
        v.len() > 5,
        v.index(0) == 10,  // comment this to make this proof fail
    ]);
    ensures(|ret:u32| ret == 10u32);
    v.index(0)
}


// Example 2: Two sequence - not connected two `axiom_seq_update_same`
// This example itself is correct, however, Z3(4.8.5) finds it hard to find 
// `assert(result.0.index(3) == result.1.index(3))`
// In debugger, the generated counter example has different values at index(3)
#[spec]
fn bigger(v1: Seq<i32>, v2:Seq<i32>) -> bool {
    forall(|i:int| ((0 <= i) && (i < v1.len())) >>= (v1.index(i) <= v2.index(i)))
}

#[proof]
fn seq_push(v1: Seq<i32>, v2:Seq<i32>, num:i32) -> (Seq<i32>, Seq<i32>) {
    requires([
        v1.len() == 3 ,
        v1.len() == v2.len(),
        bigger(v1, v2),
    ]);
    ensures(|ret:(Seq<i32>, Seq<i32>)| [
        ret.0.len() == ret.1.len(),
        bigger(ret.0, ret.1),        
    ]);
    
    let result = (v1.push(num), v2.push(num));               //  TODO: not present in query const if not used in line 50
    assert(result.0.index(3) == result.1.index(3));       // Fails without this assertion
    result
}


// Maybe make an example about seq of enum/struct


// Example3: simple vector example
#[exec]
fn vec_first_elt_is_10(v: Vec<u32>) -> u32 {
    requires([
        v.len() > 5,
        v.view().index(0) == 10,  // comment this to make this proof fail
    ]);
    ensures(|ret:u32| ret == 10u32);
    *v.index(0)
}


// Example4: Vector update. 
// This example itself is correct, but Z3 doesn't automatically find that the last index is 11
// after `v.push(11)
#[spec]
fn sorted(v: Seq<u32>) -> bool {
    forall(|i:int, j:int| ((0 <= i) && (i <= j) && (j < v.len())) >>= (v.index(i) <= v.index(j)))
}

#[spec]
fn upper_bound(v: Seq<u32>, bound:u32) -> bool {
    forall(|i:int| ((0 <= i) && (i < v.len())) >>= (v.index(i) <= bound))
}

#[exec]
fn vec_sorted_after_push(v: &mut Vec<u32>, value: u32) {
    requires([
        old(v).len() < 20,
        old(v).len() > 5,
        sorted(old(v).view()),
        upper_bound(old(v).view(), 10),  // all elt is < 10
    ]);
    ensures([
        sorted(v.view()),
    ]);

    #[spec] let initial_len = v.view().len();
    v.push(11u32);
    // assert(v.index(4) < 10);
    // assert(v.index(initial_len) == 11);  // Fails without this line. 
    v.push(12u32);
}
