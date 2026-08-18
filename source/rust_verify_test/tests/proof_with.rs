#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Tests for `#[verus_spec(with ..)]`: extra ghost/tracked inputs and outputs.
//
// A call site written as `proof_with!{..} f(..)` is redirected to the verified
// counterpart of `f` on the lowered HIR, before type checking, so that rustc
// type checks, borrow checks and lifetime checks the extra arguments.

test_verify_one_file! {
    #[test] test_proof_with code!{
        use vstd::prelude::*;

        #[verus_spec(
            with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32>
            requires a == 0, b == 1, c == 2,
        )]
        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(1u64), Ghost(2u32)}
            test(0);
        }

        // The unverified counterpart keeps the original signature.
        #[verifier::external]
        fn unverified_call_test() {
            test(0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_with_impl code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct A {
            a: u64,
        }

        impl A {
            #[verus_spec(
                with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32>
                requires self.a == 0, b == 1, c == 2,
            )]
            fn test(&self) {
            }
        }

        #[verus_spec]
        fn call_test() {
            let a = A { a: 0 };
            proof_with!{Tracked(1u64), Ghost(2u32)}
            a.test();
        }

        #[verifier::external]
        fn unverified_call_test() {
            let a = A { a: 0 };
            a.test();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_with_failed_requires code!{
        use vstd::prelude::*;

        #[verus_spec(
            with Tracked(b): Tracked<u64>
            requires b == 1,
        )]
        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(2u64)}
            test(0); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_proof_with_missing code!{
        use vstd::prelude::*;

        #[verus_spec(
            with Tracked(b): Tracked<u64>
            requires b == 1,
        )]
        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_test() {
            test(0); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_proof_with_on_non_with_fn code!{
        use vstd::prelude::*;

        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(1u64)}
            test(0);
        }
    } => Err(e) => {
        assert!(e.warnings[0].message.contains("`test` does not accept extra ghost/tracked arguments"));
        assert_rust_error_msg(e, "this function takes 1 argument but 2 arguments were supplied");
    }
}

// ---- type, mode and lifetime checking is done by rustc ----

test_verify_one_file! {
    #[test] test_proof_with_invalid_type code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<u64>)]
        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(1u32)}
            test(0);
        }
    } => Err(e) => assert_rust_error_msg_all(e, "mismatched types")
}

test_verify_one_file! {
    #[test] test_proof_with_wrong_mode_type code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<u64>)]
        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Ghost(1u64)}
            test(0);
        }
    } => Err(e) => assert_rust_error_msg_all(e, "mismatched types")
}

test_verify_one_file! {
    #[test] test_proof_with_wrong_arity code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<u64>, Tracked(c): Tracked<u64>)]
        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(1u64)}
            test(0);
        }
    } => Err(e) => assert_rust_error_msg_all(e, "this function takes 3 arguments but 2 arguments were supplied")
}

test_verify_one_file! {
    #[test] test_proof_with_lifetime_mismatch code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(c): Tracked<&'a u64>)]
        fn test<'a>(a: &'a u64, b: u64) -> &'a u64 {
            a
        }

        #[verus_spec]
        fn test2<'a, 'b>(a: &'a u64, b: u64, c: Tracked<&'b u64>) -> &'a u64 {
            proof_with!{c}
            test(a, b)
        }
    } => Err(e) => assert_rust_error_msg_skip_spec_msgs(e, "lifetime may not live long enough")
}

test_verify_one_file! {
    #[test] test_proof_with_lifetime_compatible code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(c): Tracked<&'a u64>)]
        fn test<'a>(a: &'a u64, b: u64) -> &'a u64 {
            a
        }

        #[verus_spec]
        fn test2<'a, 'b: 'a>(a: &'a u64, b: u64, c: Tracked<&'b u64>) -> &'a u64 {
            proof_with!{c}
            test(a, b)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_with_ghost_lifetime_mismatch code!{
        use vstd::prelude::*;

        #[verus_spec(with Ghost(g): Ghost<&'a u64>)]
        fn test<'a>(a: &'a u64) -> &'a u64 {
            a
        }

        #[verus_spec]
        fn test2<'a, 'b>(a: &'a u64, c: Ghost<&'b u64>) -> &'a u64 {
            proof_with!{c}
            test(a)
        }
    } => Err(e) => assert_rust_error_msg_skip_spec_msgs(e, "lifetime may not live long enough")
}

test_verify_one_file! {
    #[test] test_proof_with_ownership code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct A;

        #[verus_spec(with Tracked(b): Tracked<&'a mut A>, Ghost(c): Ghost<u32>)]
        fn test<'a>(a: &'a mut A) {
        }

        #[verus_spec]
        fn call_test(mut a: A) {
            proof_with!{Tracked(&mut a), Ghost(2u32)}
            test(&mut a);
        }
    } => Err(e) => assert_rust_error_msg_skip_spec_msgs(e, "cannot borrow `a` as mutable more than once at a time")
}

// ---- generics ----

test_verify_one_file! {
    #[test] test_proof_with_generic_type code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<T>)]
        fn test<T>(a: T) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(1u64)}
            test(0u64);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_with_generic_type_wrong_type code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<T>)]
        fn test<T>(a: T) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(1u32)}
            test(0u64);
        }
    } => Err(e) => assert_rust_error_msg_all(e, "mismatched types")
}

// ---- extra ghost/tracked outputs ----

test_verify_one_file! {
    #[test] test_ret_with_basic code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with -> z: Ghost<u32>
            ensures ret == 1u64, z@ == 2u32,
        )]
        fn test() -> u64 {
            proof_with!{|= Ghost(2u32)}
            1
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{=> Ghost(z)}
            let r = test();
            proof!{
                assert(r == 1);
                assert(z == 2);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ret_with_ignored code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with -> z: Ghost<u32>
            ensures ret == 1u64, z@ == 2u32,
        )]
        fn test() -> u64 {
            proof_with!{|= Ghost(2u32)}
            1
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{=> _}
            let r = test();
            proof!{
                assert(r == 1);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ret_with_multiple code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with -> y: Ghost<u8>, z: Ghost<u32>
            ensures ret == 1u64, y@ == 3u8, z@ == 2u32,
        )]
        fn test() -> u64 {
            proof_with!{|= (Ghost(3u8), Ghost(2u32))}
            1
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{=> (Ghost(y), Ghost(z))}
            let r = test();
            proof!{
                assert(r == 1);
                assert(y == 3);
                assert(z == 2);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ret_with_ensures_fail code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with -> z: Ghost<u32>
            ensures z@ == 2u32, // FAILS
        )]
        fn test() -> u64 {
            proof_with!{|= Ghost(3u32)}
            1
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_with_inputs_and_outputs code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with Tracked(y): Tracked<&mut int>, Ghost(w): Ghost<u32> -> z: Ghost<u32>
            requires x < 100, *old(y) < 100,
            ensures *final(y) == x, ret == x, z@ == x,
        )]
        fn test(x: u32) -> u32 {
            proof!{
                *y = x as int;
            }
            proof_with!{|= Ghost(x)}
            x
        }

        #[verus_spec]
        fn call_test() {
            proof_decl!{
                let tracked mut y = 0int;
            }
            proof_with!{Tracked(&mut y), Ghost(0u32) => Ghost(z)}
            let r = test(1);
            proof!{
                assert(r == 1);
                assert(y == 1);
                assert(z == 1);
            }
        }
    } => Ok(())
}

// The extra ghost/tracked types come from the verified counterpart's signature,
// so no type annotation is needed at the call site.
test_verify_one_file! {
    #[test] test_with_inferred_types code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with Ghost(w): Ghost<u32> -> z: Ghost<u8>
            ensures ret == 1u64, z@ == 5u8,
        )]
        fn test() -> u64 {
            proof_with!{|= Ghost(5u8)}
            1
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Ghost(0u32) => Ghost(z)}
            let r = test();
            proof!{
                assert(r == 1);
                assert(z == 5);
            }
        }
    } => Ok(())
}

// ---- calls through a path or an alias resolve to the same verified function ----

test_verify_one_file! {
    #[test] test_proof_with_qualified_path code!{
        use vstd::prelude::*;

        mod m {
            use vstd::prelude::*;
            #[verus_spec(
                with Tracked(b): Tracked<u64>
                requires b == 1,
            )]
            pub fn test(a: u64) {
            }
        }

        #[verus_spec]
        fn call_qualified() {
            proof_with!{Tracked(1u64)}
            m::test(0);
        }

        use m::test as aliased;

        #[verus_spec]
        fn call_aliased() {
            proof_with!{Tracked(1u64)}
            aliased(0);
        }
    } => Ok(())
}

test_verify_one_file! {
    // The same call without `proof_with!` reaches the unverified stub, both
    // through the qualified path and through the alias.
    #[test] test_proof_with_qualified_path_missing code!{
        use vstd::prelude::*;

        mod m {
            use vstd::prelude::*;
            #[verus_spec(
                with Tracked(b): Tracked<u64>
                requires b == 1,
            )]
            pub fn test(a: u64) {
            }
        }

        use m::test as aliased;

        #[verus_spec]
        fn call_qualified() {
            m::test(0); // FAILS
        }

        #[verus_spec]
        fn call_aliased() {
            aliased(0); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    // A call through a `use crate::.. as ..` alias is redirected to the verified
    // counterpart, and an alias of an ordinary function next to it is untouched.
    #[test] test_proof_with_through_crate_alias code!{
        use vstd::prelude::*;

        fn original(x: i32) -> i32 {
            x * 2
        }

        use crate::original as alias;

        #[verus_spec(r =>
            with Ghost(g): Ghost<int>
            requires g == 1, a < 1000,
            ensures r == a + 1,
        )]
        fn with_extra(a: u64) -> u64 {
            a + 1
        }

        use crate::with_extra as with_alias;

        #[verus_spec]
        fn test() {
            proof_with!{Ghost(1int)}
            let r = with_alias(6);
            proof!{ assert(r == 7); }
        }

        fn unverified() -> i32 {
            // The stub keeps the name and the signature the user wrote.
            alias(2) + with_alias(1) as i32
        }
    } => Ok(())
}

test_verify_one_file! {
    // Without `proof_with!`, the call goes to the unverified stub, whose
    // `requires(false)` no caller can satisfy, through an alias just the same.
    #[test] test_proof_with_through_crate_alias_missing code!{
        use vstd::prelude::*;

        #[verus_spec(r =>
            with Ghost(g): Ghost<int>
            requires g == 1, a < 1000,
            ensures r == a + 1,
        )]
        fn with_extra(a: u64) -> u64 {
            a + 1
        }

        use crate::with_extra as with_alias;

        #[verus_spec]
        fn test() {
            let r = with_alias(6); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    // A user-defined function named `proof_with` is not the builtin marker and must
    // not trigger the call redirect.
    #[test] test_user_defined_proof_with_is_not_a_marker code!{
        use vstd::prelude::*;

        mod verus_builtin {
            use vstd::prelude::*;
            #[verus_verify]
            pub fn proof_with<A, B>(_a: A, b: B) -> B {
                b
            }
        }

        #[verifier::external_body]
        fn opaque(a: u64) -> u64 {
            a
        }

        #[verus_spec]
        fn call_user_proof_with() -> u64 {
            verus_builtin::proof_with(1u64, opaque(2))
        }
    } => Ok(())
}

// --- Functions in different modules ---

test_verify_one_file! {
    #[test] test_cross_module_proof_with code!{
        mod inner {
            use vstd::prelude::*;

            #[verus_spec(ret=>
                with
                    Ghost(extra): Ghost<u64>,
                requires
                    a < 100 && extra@ < 100,
                ensures
                    ret == a,
            )]
            pub fn copy_u64(a: u64) -> u64
            {
                a
            }
        }

        #[verus_spec]
        fn test_call_cross_module() {
            use vstd::prelude::*;
            use inner::copy_u64;
            proof_with!{Ghost(5u64)}
            let ret = copy_u64(10);
            proof!{assert(ret == 10);}
        }
    } => Ok(())
}
