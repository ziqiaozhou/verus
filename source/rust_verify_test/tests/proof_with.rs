#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;


test_verify_one_file! {
     #[test] test_proof_with code!{
        use vstd::prelude::*;
        verus!{
        fn test(a: u64) 
        {
            let b: Tracked<u64> = declare_with();
            let c: Ghost<u32> = declare_with();
            requires(a == 0 && b.view() == 1 && c.view() == 2);
        }
       
        fn call_test() {
            proof_with(Tracked(0u64));
            proof_with(Ghost(2u32));
            test(0); // FAILS
        }
        }
     } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
     #[test] test_proof_with_invalid_type code!{
        use vstd::prelude::*;
        verus!{
        fn test(a: u64) 
        {
            let b: Tracked<u64> = declare_with();
            requires(a == 0 && b.view() == 1);
        }
       
        fn call_test() {
            proof_with(0u64);
            test(0);
        }
        }
     } => Err(e) => assert_vir_error_msg(e, "proof_with expects an argument of type Tracked<T> or Ghost<T>")
}

test_verify_one_file! {
     #[test] test_proof_with_wrong_mode_type code!{
        use vstd::prelude::*;
        verus!{
        fn test(a: u64)
        {
            let b: Tracked<u64> = declare_with();
            requires(a == 0 && b.view() == 1);
        }

        fn call_test() {
            proof_with(Ghost(0u64));
            test(0);
        }
        }
     } => Err(e) => assert_vir_error_msg(e, "proof_with argument 1 has wrong mode: expected Tracked, got Ghost")
}
