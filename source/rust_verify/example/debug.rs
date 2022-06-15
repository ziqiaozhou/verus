// rust_verify/tests/example.rs expect-failures

use builtin::*;
mod pervasive;
use pervasive::*;

fn main() {}

// plan: struct -> enum -> Seq -> List -> Set -> Map



// Example 1: mutation
#[proof]
fn test_mut(i: int, n: nat, u: u8) {
    requires(i >= 0); // comment this to make this proof fail
    let mut x:int = 5; 
    x = x + i;           // 1_mutation
    x = x + n;           // 2_mutation
    x = x + u;           // 3_mutation
    assert(x >= 5);
}



// Example 2: if-else
#[proof]
fn test_if_else(b:bool, z:int) {
    requires(b);     // comment this to make this proof fail
    let mut x:int = 3;
    let mut y:int = z;   // 0_entry
    if b {
        x = 2*x;        // 1_mutation
        y = x + 1;      // 2_mutation
    } else {
        x = y + 1;      // 3_mutation
        y = 7;          // 4_mutation
    } 
    // 5_join
    assert(x + y > 5); 
}



// Example 3: loop
#[exec]
fn test_loop_context() {
    let mut i: u64 = 10;
    let mut b: u64 = 20;     // 0_entry
    let mut inc = 2;

    while i < 100 {
        invariant([
            10 <= i,
            i <= 100,
            b == i * 2,
            inc == 2,   // comment this to make this proof fail
        ]);   
        // 1_while_begin
        
        i = i + 1;      // 2_mutation
        b = b + inc;    // 3_mutation        
    } // 4_while_end

    assert(i == 100);
    assert(b == 200);
}



// fn test_params(i: int, n: nat, u: u8) {
//     assert(n >= 5);
// }

// #[proof]
// fn test_mutation(i: int, n: nat, u: u8) {
//     let mut x:int = 5 as int;
//     x = x + i;
//     x = x + n;
//     x = x + u;
//     assert(x >= 5);
// }


// #[spec]
// fn add_one(i: int) -> int {
//     i + 1
// }

// #[proof]
// fn very_simple(z:int) {
//     let mut x = z;      // 1_mutation
//     assert (add_one(x) < 3);
// }

// #[proof]
// fn test_if_else(b:bool, z:int) {
//     let mut x : int;
//     let mut y : int = z; // 0_entry
//     let mut f : int;
//     x = 0;
//     x = x + y;      // 1_mutation
//     if b {
//         x = 2*x;    // 2_mutation
//         y = x + 1;  // 3_mutation
//     } else {
//         let mut dd : int;
//         if b {
//             let mut ddd : int;
//             assert(true);
//             x = 2*x;    // 4_mutation
//             y = x + 1;  // 5_mutation
//         } // 6_join
//         x = y + 1;  // 7_mutation
//         y = 7;      // 8_mutation
//         f = 34;    // 9_mutation
//     } // 10_join
//     assert(x + y > 5); 
// }




// Since the loop body has separate query, it need additional support
// query-specific snapshot?
// Since the while-loop body's query fails, the query has no information about lines before loop
// when `assert(b1 == 5) fails, currently I cannot query lines outside of loop body, also it might give a werid value (from user's perspective)
// but the weird value might be helpful to help user to realize insufficient context providing.

#[exec]
fn test_loop() {
    let mut i: u64 = 10;
    let mut b1: u8 = 20;
    let mut b2: u8 = 200;
    let mut b3: u8 = 30;  // 0_entry
    i = i + 1;           // 1_mutation         
    i = i - 1;           // 2_mutation
    // assert(false);

    // while i < 100 {
    //     invariant([
    //         10 <= i,
    //         i <= 100,
    //         b1 as u64 == i * 2,
    //     ]);
    //                   // 3_while_begin
    //     // assert(b1 == 5);
    //     i = i + 1;    // 4_mutation
    //     b1 = b1 + 2;  // 5_mutation
    //     b2 = b2 + 1;  // 6_mutation
    // } // 5_while_end

    assert(2 > 1);   // 7_while_end
}


fn inc(num: &mut i32) {
    requires(*old(num) < 1000);
    ensures(*old(num) + 1 == *num);
    *num = *num + 1;
}

fn test_mutable_ref() {
    let mut x = 100;
    inc(&mut x);
    assert(x == 102); // Fails
}