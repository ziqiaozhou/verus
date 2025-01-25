#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_let_else_returns verus_code! {
        enum X {
            A(usize),
            B(bool),
        }
        spec fn is_a(x: X) -> bool {
            match x {
                X::A(..) => {
                    true
                }
                _ => {
                    false
                }
            }
        }
        fn f(x: X) -> (ret: bool)
        ensures is_a(x) == ret
        {
            let X::A(a) = x else {
                return false
            };
            return true;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_let_else_ensures_failed_no_unwind_condition2 verus_code! {
        enum X {
            A(usize),
            B(bool),
        }
        #[verifier(external_body)]
        fn call_panic() -> ! {
            panic!();
        }
        spec fn is_a(x: X) -> bool {
            match x {
                X::A(..) => {
                    true
                }
                _ => {
                    false
                }
            }
        }
        fn f(x: X) -> (ret: bool)
        ensures is_a(x) == ret
        {
            let X::A(a) = x else {
                call_panic();
            };
            return true; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_let_else_dots verus_code! {
        struct A {
            x: usize,
            y: bool,
            z: i32,
        }
        enum X {
            U(usize),
            B(bool),
            A(A, usize, bool),
        }
        #[verifier(external_body)]
        fn call_panic() -> ! {
            panic!();
        }
        spec fn is_a(x: X) -> bool {
            match x {
                X::A(..) => {
                    true
                }
                _ => {
                    false
                }
            }
        }
        spec fn check_x_b(x: X, val1: usize, val2: bool) -> bool {
            match x {
                X::A(A{x, ..}, ..,b) => {
                    x == val1 && b == val2
                }
                _ => {
                    false
                }
            }
        }
        fn f(x: X) -> (ret: (usize, bool))
        ensures is_a(x) ==> check_x_b(x, ret.0, ret.1)
        no_unwind when is_a(x)
        {
            let X::A(A {x, ..}, .., b) = x else {
                call_panic();
            };
            (x, b)
        }
    } => Ok(())
}
