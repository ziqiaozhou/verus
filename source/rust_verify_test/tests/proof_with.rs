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
        assert!(e.errors.iter().any(|x| x.message.contains("`test` does not accept extra ghost/tracked arguments")));
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

// --- `with` on an external function specification (`assume_specification`) ---
//
// The `assume_specification` keeps the exact signature of the external function
// and gains `requires(false)`, so a plain call fails. The verified counterpart
// carries the extra ghost/tracked parameters, and `proof_with!` redirects the
// call to it.

test_verify_one_file! {
    #[test] test_external_fn_with code!{
        use vstd::prelude::*;

        #[verifier::external]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with Tracked(extra): Tracked<u8>
            requires x == extra,
            ensures ret == !b,
        )]
        fn negate_bool_spec(b: bool, x: u8) -> bool {
            negate_bool(b, x)
        }

        #[verus_spec]
        fn call_external() {
            proof_with!{Tracked(1u8)}
            let ret = negate_bool(true, 1);
            proof!{
                assert(!ret);
            }
        }

        #[verifier::external]
        fn unverified_call_external() {
            negate_bool(true, 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_external_fn_with_extra_output code!{
        use vstd::prelude::*;

        #[verifier::external]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with Tracked(extra): Tracked<u8> -> z: Ghost<u8>
            requires x == extra,
            ensures ret == !b, z@ == extra,
        )]
        fn negate_bool_spec(b: bool, x: u8) -> bool {
            negate_bool(b, x)
        }

        #[verus_spec]
        fn call_external() {
            proof_with!{Tracked(1u8) => Ghost(z)}
            let ret = negate_bool(true, 1);
            proof!{
                assert(!ret);
                assert(z == 1u8);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Without `proof_with!`, the call goes to the `assume_specification`, whose
    // precondition is `false`.
    #[test] test_external_fn_missing_proof_with code!{
        use vstd::prelude::*;

        #[verifier::external]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with Tracked(extra): Tracked<u8>
            requires x == extra,
            ensures ret == !b,
        )]
        fn negate_bool_spec(b: bool, x: u8) -> bool {
            negate_bool(b, x)
        }

        #[verus_spec]
        fn call_external() {
            let ret = negate_bool(true, 1); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_external_fn_failed_requires code!{
        use vstd::prelude::*;

        #[verifier::external]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with Tracked(extra): Tracked<u8>
            requires x == extra,
            ensures ret == !b,
        )]
        fn negate_bool_spec(b: bool, x: u8) -> bool {
            negate_bool(b, x)
        }

        #[verus_spec]
        fn call_external() {
            proof_with!{Tracked(99u8)}
            let ret = negate_bool(true, 1); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    // rustc still checks the extra arguments of the redirected call.
    #[test] test_external_fn_wrong_extra_type code!{
        use vstd::prelude::*;

        #[verifier::external]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with Tracked(extra): Tracked<u8>
            ensures ret == !b,
        )]
        fn negate_bool_spec(b: bool, x: u8) -> bool {
            negate_bool(b, x)
        }

        #[verus_spec]
        fn call_external() {
            proof_with!{Tracked(1u32)}
            let ret = negate_bool(true, 1);
        }
    } => Err(e) => assert_rust_error_msg_all(e, "mismatched types")
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

// --- `with` on a trait method ---
//
// A method that declares extra ghost/tracked parameters cannot be its own
// verified counterpart, so the counterparts are collected into a companion
// trait, `_VERUS_VERIFIED_TRAIT_X`, declared next to `X` as a subtrait of it.
// The method of `X` keeps `requires(false)`, an implementation of `X` is split
// between the two traits, and a caller that needs the counterpart is given the
// bound on the companion trait. None of this is spelled out in the source.

test_verify_one_file! {
    #[test] test_trait_with code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64>
                requires a < 100, g@ < 100,
                ensures ret == a,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                a
            }
        }

        #[verus_spec]
        fn call_concrete(s: &S) {
            proof_with!{Ghost(1u64)}
            let r = s.f(3);
            proof!{ assert(r == 3); }
        }

        // The extra arguments are declared by the trait, so a generic caller can
        // pass them too.
        #[verus_spec]
        fn call_generic<T: X>(t: &T) {
            proof_with!{Ghost(1u64)}
            let r = t.f(3);
            proof!{ assert(r == 3); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Without `proof_with!` the call goes to the stub, which inherits
    // `requires(false)` from the trait declaration.
    #[test] test_trait_with_missing_proof_with code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64>
                ensures ret == a,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                a
            }
        }

        #[verus_spec]
        fn call_concrete(s: &S) {
            let r = s.f(3); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_trait_with_failed_requires code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64>
                requires g@ < 100,
                ensures ret == a,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                a
            }
        }

        #[verus_spec]
        fn call_concrete(s: &S) {
            proof_with!{Ghost(300u64)}
            let r = s.f(3); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    // A generic caller passes the extra arguments with the bound it was written
    // with: the counterpart is declared by a companion trait, which the trait
    // has as a supertrait.
    #[test] test_trait_with_generic_caller code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
                ensures ret == a, g2 == g,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64> -> g2: Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                proof_with!{|= Ghost(g)}
                a
            }
        }

        #[verus_spec(r => ensures r == 7)]
        fn call_generic<A: X>(x: &A) -> u64 {
            proof_with!{Ghost(3u64) => Ghost(g2)}
            let r = x.f(7);
            proof!{ assert(g2 == 3); }
            r
        }

        #[verus_verify]
        fn test() {
            let r = call_generic(&S);
            proof!{ assert(r == 7); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // The trait the counterpart belongs to may be reached through a supertrait:
    // `A: Y`, where `trait Y: X`, calls the methods of `X` too.
    #[test] test_trait_with_generic_caller_of_subtrait code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
                ensures ret == a, g2 == g,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        trait Y: X {}

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64> -> g2: Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                proof_with!{|= Ghost(g)}
                a
            }
        }

        #[verus_verify]
        impl Y for S {}

        #[verus_spec(r => ensures r == 7)]
        fn call_generic<A: Y>(x: &A) -> u64 {
            proof_with!{Ghost(3u64) => Ghost(g2)}
            let r = x.f(7);
            proof!{ assert(g2 == 3); }
            r
        }

        #[verus_verify]
        fn test() {
            let r = call_generic(&S);
            proof!{ assert(r == 7); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // A qualified call names the trait, which the rewrite has to replace with
    // the companion trait that declares the counterpart.
    #[test] test_trait_qualified_call code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
                ensures ret == a, g2 == g,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64> -> g2: Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                proof_with!{|= Ghost(g)}
                a
            }
        }

        #[verus_verify]
        fn test() {
            proof_with!{Ghost(3u64) => Ghost(g2)}
            let r = X::f(&S, 7);
            proof!{ assert(r == 7); assert(g2 == 3); }

            proof_with!{Ghost(4u64) => Ghost(g3)}
            let r = <S as X>::f(&S, 7);
            proof!{ assert(r == 7); assert(g3 == 4); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // The bound is added to the item that declares the type parameter, which is
    // the implementation here, not the method.
    #[test] test_trait_with_generic_impl code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
                ensures ret == a, g2 == g,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64> -> g2: Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                proof_with!{|= Ghost(g)}
                a
            }
        }

        #[verus_verify]
        struct Wrapper<A>(A);

        #[verus_verify]
        impl<A: X> Wrapper<A> {
            #[verus_spec(r => ensures r == 7)]
            fn call(&self) -> u64 {
                proof_with!{Ghost(3u64) => Ghost(g2)}
                let r = self.0.f(7);
                proof!{ assert(g2 == 3); }
                r
            }
        }

        #[verus_verify]
        fn test() {
            let w = Wrapper(S);
            let r = w.call();
            proof!{ assert(r == 7); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // A caller whose type parameter is bounded by a trait without a companion
    // is left alone, and one that is bounded by a trait with a companion may
    // still not call the counterpart.
    #[test] test_trait_with_generic_caller_of_other_trait code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64>
                ensures ret == a,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        trait Y {
            #[verus_spec(ret => ensures ret == a)]
            fn g(&self, a: u64) -> u64;
        }

        #[verus_spec(r => ensures r == 7)]
        fn call_other<A: Y, B: X>(x: &A, _y: &B) -> u64 {
            x.g(7)
        }
    } => Ok(())
}

test_verify_one_file! {
    // A generic function can implement a trait whose method declares a `with`
    // clause of its own.
    #[test] test_trait_with_generic_self code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
                ensures ret == a, g2 == g,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct Wrapper<A>(A);

        #[verus_verify]
        impl<A: X> X for Wrapper<A> {
            #[verus_spec(with Ghost(g): Ghost<u64> -> g2: Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                proof_with!{Ghost(g) => Ghost(inner)}
                let r = self.0.f(a);
                proof_with!{|= Ghost(inner)}
                r
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // The companion trait is declared next to the trait it belongs to, so an
    // implementation reaches it through the same path.
    #[test] test_trait_with_qualified_path code!{
        use vstd::prelude::*;

        mod m {
            use vstd::prelude::*;

            #[verus_verify]
            pub trait X {
                #[verus_spec(ret =>
                    with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
                    ensures ret == a, g2 == g,
                )]
                fn f(&self, a: u64) -> u64;
            }
        }

        use m::X;

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl m::X for S {
            #[verus_spec(with Ghost(g): Ghost<u64> -> g2: Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                proof_with!{|= Ghost(g)}
                a
            }
        }

        #[verus_verify]
        fn test(s: &S) {
            proof_with!{Ghost(3u64) => Ghost(g2)}
            let r = s.f(7);
            proof!{ assert(r == 7); assert(g2 == 3); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // The counterpart is declared by a subtrait of the trait, so its signature
    // can name an associated type of the trait.
    #[test] test_trait_with_associated_type code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            type Item;

            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
                ensures g2 == g,
            )]
            fn f(&self, a: Self::Item) -> Self::Item;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            type Item = u64;

            #[verus_spec(with Ghost(g): Ghost<u64> -> g2: Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                proof_with!{|= Ghost(g)}
                a
            }
        }

        #[verus_verify]
        fn test(s: &S) {
            proof_with!{Ghost(3u64) => Ghost(g2)}
            let _r = s.f(7);
            proof!{ assert(g2 == 3); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // An implementation that does not declare the `with` clause of the trait
    // implements no counterpart, so it cannot be called with extra arguments.
    #[test] test_trait_with_missing_in_impl code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64>
                ensures ret == a,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            fn f(&self, a: u64) -> u64 {
                a
            }
        }

        #[verus_verify]
        fn test(s: &S) {
            proof_with!{Ghost(3u64)}
            let r = s.f(3);
        }
    } => Err(e) => assert_rust_error_msg_all(e, "_VERUS_VERIFIED_f` found for reference `&S`")
}

test_verify_one_file! {
    // rustc checks the extra parameters of the implementation against the trait.
    #[test] test_trait_with_mismatched_in_impl code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64>
                ensures ret == a,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Tracked(g): Tracked<u64>)]
            fn f(&self, a: u64) -> u64 {
                a
            }
        }
    } => Err(e) => assert_rust_error_msg_all(e, "has an incompatible type for trait")
}

test_verify_one_file! {
    // A trait can declare a `with` clause on several of its methods, each with
    // its own extra parameters, next to methods that have none. Every method
    // with a `with` clause gets its own counterpart in the companion trait, and
    // the implementation is split accordingly.
    #[test] test_trait_with_multiple_methods code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait T {
            #[verus_spec(r =>
                with Ghost(g): Ghost<int> -> g2: Ghost<int>
                ensures r == a, g2@ == g + 1,
            )]
            fn f(&self, a: u64) -> u64;

            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                requires b == 1,
                ensures r == 2,
            )]
            fn g(&self) -> u64;

            #[verus_spec(r => ensures r == 5)]
            fn plain(&self) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl T for S {
            #[verus_spec(with Ghost(g): Ghost<int> -> g2: Ghost<int>)]
            fn f(&self, a: u64) -> u64 {
                proof_decl!{ let ghost gg: int = g + 1; }
                proof_with!{|= Ghost(gg)}
                a
            }

            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn g(&self) -> u64 {
                2
            }

            fn plain(&self) -> u64 {
                5
            }
        }

        #[verus_verify]
        fn test() {
            let s = S;
            proof_with!{Ghost(3int) => Ghost(g2)}
            let r = s.f(7);
            proof!{ assert(r == 7); assert(g2 == 4); }
            proof_with!{Tracked(1u64)}
            let q = s.g();
            proof!{ assert(q == 2); }
            let p = s.plain();
            proof!{ assert(p == 5); }
        }

        #[verus_verify]
        fn call_generic<A: T>(x: &A) -> u64 {
            proof_with!{Ghost(3int) => Ghost(g2)}
            let r = x.f(7);
            proof!{ assert(g2 == 4); }
            proof_with!{Tracked(1u64)}
            let q = x.g();
            proof!{ assert(q == 2); }
            r
        }
    } => Ok(())
}

test_verify_one_file! {
    // The counterpart of a trait method is declared by the companion trait,
    // which an implementation only implements when it overrides the method. A
    // default body would be inherited by the counterpart of an implementation
    // that overrides the method without a `with` clause, so a verified call
    // would run the default while the executable runs the override. `with` on a
    // method with a default body is rejected instead.
    #[test] test_trait_with_default_body code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait T {
            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                requires b == 1,
                ensures r == 2,
            )]
            fn g(&self) -> u64 {
                2
            }
        }
    } => Err(e) => assert_vir_error_msg(e, "`with` is not supported on a trait method with a default body")
}

test_verify_one_file! {
    // Since no method of a companion trait has a default body, an implementation
    // that overrides a method without repeating its `with` clause leaves the
    // counterpart unimplemented, which rustc rejects. The two halves of a method
    // can therefore never come apart.
    #[test] test_trait_with_missing_in_impl_of_several code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait T {
            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                requires b == 1,
                ensures r == 2,
            )]
            fn g(&self) -> u64;

            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                requires b == 1,
                ensures r == 9,
            )]
            fn f(&self) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl T for S {
            // The `with` clause is missing, so `_VERUS_VERIFIED_g` is not
            // implemented, even though the other method makes the implementation
            // of the companion trait exist.
            fn g(&self) -> u64 {
                3
            }

            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn f(&self) -> u64 {
                9
            }
        }
    } => Err(e) => assert_rust_error_msg_all(e, "not all trait items implemented, missing: `_VERUS_VERIFIED_g`")
}

// --- `with` on the methods of an external trait ---
//
// An external trait cannot declare the verified counterparts of its methods:
// they take extra parameters, so they are not members of it. Declaring a `with`
// clause on its proxy derives a companion trait, a subtrait of the external
// trait, that declares the counterparts. The method of the external trait keeps
// `requires(false)`, so verified code can only reach it through its
// counterpart, and an implementation of the external trait is split between the
// two traits.

// The external trait and the type that implements it, shared by the tests below.
const EXTERNAL_TRAIT_DECL: &str = code_str! {
    use vstd::prelude::*;

    #[verifier::external]
    trait T {
        fn f(&self, a: u64) -> u64;
    }

    #[verus_verify]
    struct S;
};

// The proxy that declares the `with` clause, and the implementation split by it.
const EXTERNAL_TRAIT: &str = code_str! {
    #[verus_verify]
    #[verifier::external_trait_specification]
    trait ExT {
        type ExternalTraitSpecificationFor: T;

        #[verus_spec(r =>
            with Ghost(g): Ghost<int> -> g2: Ghost<int>
            ensures r == a, g2@ == g + 1,
        )]
        fn f(&self, a: u64) -> u64;
    }

    #[verus_verify]
    impl T for S {
        #[verus_spec(with Ghost(g): Ghost<int> -> g2: Ghost<int>)]
        fn f(&self, a: u64) -> u64 {
            proof_decl!{ let ghost gg: int = g + 1; }
            proof_with!{|= Ghost(gg)}
            a
        }
    }
};

const CALL_EXTERNAL_TRAIT: &str = code_str! {
    #[verus_verify]
    fn test() {
        let s = S;
        proof_with!{Ghost(3int) => Ghost(g2)}
        let r = s.f(7);
        proof!{ assert(r == 7); assert(g2 == 4); }
    }
};

test_verify_one_file! {
    #[test] test_external_trait_with
        EXTERNAL_TRAIT_DECL.to_string() + EXTERNAL_TRAIT + CALL_EXTERNAL_TRAIT
    => Ok(())
}

test_verify_one_file! {
    // A qualified call to a method of an external trait, whose counterpart the
    // companion of the external trait declares.
    #[test] test_external_trait_qualified_call
        EXTERNAL_TRAIT_DECL.to_string() + EXTERNAL_TRAIT + code_str!{
        #[verus_verify]
        fn test() {
            proof_with!{Ghost(3int) => Ghost(g2)}
            let r = T::f(&S, 7);
            proof!{ assert(r == 7); assert(g2 == 4); }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // The companion trait is erased away when the code is compiled: the body
    // stays in the implementation of the external trait.
    #[test] test_external_trait_with_compile ["--compile"] =>
        EXTERNAL_TRAIT_DECL.to_string() + EXTERNAL_TRAIT + CALL_EXTERNAL_TRAIT
    => Ok(())
}

test_verify_one_file! {
    // A generic caller passes the extra arguments with the bound it was
    // written with: the bound on the companion trait is added to it.
    #[test] test_external_trait_with_generic_caller
        EXTERNAL_TRAIT_DECL.to_string() + EXTERNAL_TRAIT + code_str!{
        #[verus_spec(r => ensures r == 7)]
        fn call_generic<X: T>(x: &X) -> u64 {
            proof_with!{Ghost(3int) => Ghost(g2)}
            let r = x.f(7);
            proof!{ assert(g2 == 4); }
            r
        }

        #[verus_verify]
        fn test() {
            let s = S;
            let r = call_generic(&s);
            proof!{ assert(r == 7); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // The companion trait is found by the call even though only the external
    // trait is imported at the call site.
    #[test] test_external_trait_with_cross_module code!{
        mod m {
            use vstd::prelude::*;

            #[verifier::external]
            pub trait T {
                fn f(&self, a: u64) -> u64;
            }

            #[verus_verify]
            #[verifier::external_trait_specification]
            pub trait ExT {
                type ExternalTraitSpecificationFor: T;

                #[verus_spec(r =>
                    with Ghost(g): Ghost<int> -> g2: Ghost<int>
                    ensures r == a, g2@ == g + 1,
                )]
                fn f(&self, a: u64) -> u64;
            }

            #[verus_verify]
            pub struct S;

            #[verus_verify]
            impl T for S {
                #[verus_spec(with Ghost(g): Ghost<int> -> g2: Ghost<int>)]
                fn f(&self, a: u64) -> u64 {
                    proof_decl!{ let ghost gg: int = g + 1; }
                    proof_with!{|= Ghost(gg)}
                    a
                }
            }
        }

        use m::{S, T};
        use vstd::prelude::*;

        #[verus_verify]
        fn test() {
            let s = S;
            proof_with!{Ghost(3int) => Ghost(g2)}
            let r = s.f(7);
            proof!{ assert(r == 7); assert(g2 == 4); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // The name of the companion trait carries the generic arguments written at
    // the implementation.
    #[test] test_external_trait_with_generic_trait code!{
        use vstd::prelude::*;

        #[verifier::external]
        trait T<A> {
            fn f(&self, a: A) -> A;
        }

        #[verus_verify]
        #[verifier::external_trait_specification]
        trait ExT<A> {
            type ExternalTraitSpecificationFor: T<A>;

            #[verus_spec(r =>
                with Ghost(g): Ghost<int> -> g2: Ghost<int>
                ensures g2@ == g + 1,
            )]
            fn f(&self, a: A) -> A;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl T<u64> for S {
            #[verus_spec(r =>
                with Ghost(g): Ghost<int> -> g2: Ghost<int>
                ensures r == a,
            )]
            fn f(&self, a: u64) -> u64 {
                proof_decl!{ let ghost gg: int = g + 1; }
                proof_with!{|= Ghost(gg)}
                a
            }
        }

        #[verus_verify]
        fn test() {
            let s = S;
            proof_with!{Ghost(3int) => Ghost(g2)}
            let r = s.f(7);
            proof!{ assert(r == 7); assert(g2 == 4); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Only the methods with a `with` clause are split: the others stay in the
    // implementation of the external trait and keep their own specification.
    #[test] test_external_trait_with_some_methods code!{
        use vstd::prelude::*;

        #[verifier::external]
        trait T {
            fn f(&self, a: u64) -> u64;
            fn g(&self, a: u64) -> u64;
        }

        #[verus_verify]
        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;

            #[verus_spec(r =>
                with Ghost(g): Ghost<int> -> g2: Ghost<int>
                ensures r == a, g2@ == g + 1,
            )]
            fn f(&self, a: u64) -> u64;

            #[verus_spec(r => ensures r == a)]
            fn g(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl T for S {
            #[verus_spec(with Ghost(g): Ghost<int> -> g2: Ghost<int>)]
            fn f(&self, a: u64) -> u64 {
                proof_decl!{ let ghost gg: int = g + 1; }
                proof_with!{|= Ghost(gg)}
                a
            }

            fn g(&self, a: u64) -> u64 {
                a
            }
        }

        #[verus_verify]
        fn test() {
            let s = S;
            proof_with!{Ghost(3int) => Ghost(g2)}
            let r = s.f(7);
            let r2 = s.g(1);
            proof!{ assert(r == 7); assert(g2 == 4); assert(r2 == 1); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // The extra outputs alone are enough to need a counterpart.
    #[test] test_external_trait_with_output_only code!{
        use vstd::prelude::*;

        #[verifier::external]
        trait T {
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;

            #[verus_spec(r =>
                with -> g2: Ghost<int>
                ensures r == a, g2@ == a,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl T for S {
            #[verus_spec(with -> g2: Ghost<int>)]
            fn f(&self, a: u64) -> u64 {
                proof_decl!{ let ghost gg: int = a as int; }
                proof_with!{|= Ghost(gg)}
                a
            }
        }

        #[verus_verify]
        fn test() {
            let s = S;
            proof_with!{=> Ghost(g2)}
            let r = s.f(7);
            proof!{ assert(g2 == 7); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // The method of the external trait has `requires(false)`: what it does
    // without the extra arguments is not specified.
    #[test] test_external_trait_with_plain_call
        EXTERNAL_TRAIT_DECL.to_string() + EXTERNAL_TRAIT + code_str!{
        #[verus_verify]
        fn test() {
            let s = S;
            let r = s.f(7); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    // The counterpart is checked against the specification declared for it by
    // the companion trait, which the implementation does not repeat.
    #[test] test_external_trait_with_failed_ensures
        EXTERNAL_TRAIT_DECL.to_string() + code_str!{
        #[verus_verify]
        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;

            #[verus_spec(r =>
                with Ghost(g): Ghost<int> -> g2: Ghost<int>
                ensures r == a, g2@ == g + 1, // FAILS
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        impl T for S {
            #[verus_spec(with Ghost(g): Ghost<int> -> g2: Ghost<int>)]
            fn f(&self, a: u64) -> u64 {
                proof_decl!{ let ghost gg: int = g + 2; }
                proof_with!{|= Ghost(gg)}
                a
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    // The counterpart of a method of an external trait is a method of the
    // companion trait, like any other, so it takes `Tracked` inputs too.
    #[test] test_external_trait_with_tracked
        EXTERNAL_TRAIT_DECL.to_string() + code_str!{
        #[verus_verify]
        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;

            #[verus_spec(r =>
                with Tracked(g): Tracked<u64>
                ensures r == a,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        impl T for S {
            #[verus_spec(with Tracked(g): Tracked<u64>)]
            fn f(&self, a: u64) -> u64 {
                a
            }
        }

        #[verus_verify]
        fn test(g: Tracked<u64>) {
            let s = S;
            proof_with!{g}
            let r = s.f(7);
            proof!{ assert(r == 7); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // The companion trait is named after the external trait, so the proxy has
    // to say which trait it stands for.
    #[test] test_external_trait_with_without_specification_for code!{
        use vstd::prelude::*;

        #[verus_verify]
        #[verifier::external_trait_specification]
        trait ExT {
            #[verus_spec(r =>
                with Ghost(g): Ghost<int> -> g2: Ghost<int>
                ensures r == a, g2@ == g + 1,
            )]
            fn f(&self, a: u64) -> u64;
        }
    } => Err(e) => assert_vir_error_msg(e, "ExternalTraitSpecificationFor")
}

test_verify_one_file! {
    // Several methods of an external trait can carry a `with` clause, each with
    // its own extra parameters, next to a method that has none. The companion
    // trait declares a counterpart for each of them.
    #[test] test_external_trait_with_multiple_methods code!{
        use vstd::prelude::*;

        #[verifier::external]
        trait T {
            fn f(&self, a: u64) -> u64;
            fn g(&self) -> u64;
            fn plain(&self) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;

            #[verus_spec(r =>
                with Ghost(g): Ghost<int> -> g2: Ghost<int>
                ensures r == a, g2@ == g + 1,
            )]
            fn f(&self, a: u64) -> u64;

            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                requires b == 1,
                ensures r == 2,
            )]
            fn g(&self) -> u64;

            #[verus_spec(r => ensures r == 5)]
            fn plain(&self) -> u64;
        }

        #[verus_verify]
        impl T for S {
            #[verus_spec(with Ghost(g): Ghost<int> -> g2: Ghost<int>)]
            fn f(&self, a: u64) -> u64 {
                proof_decl!{ let ghost gg: int = g + 1; }
                proof_with!{|= Ghost(gg)}
                a
            }

            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn g(&self) -> u64 {
                2
            }

            fn plain(&self) -> u64 {
                5
            }
        }

        #[verus_verify]
        fn test() {
            let s = S;
            proof_with!{Ghost(3int) => Ghost(g2)}
            let r = s.f(7);
            proof!{ assert(r == 7); assert(g2 == 4); }
            proof_with!{Tracked(1u64)}
            let q = s.g();
            proof!{ assert(q == 2); }
            let p = s.plain();
            proof!{ assert(p == 5); }
        }

        #[verus_verify]
        fn call_generic<A: T>(x: &A) -> u64 {
            proof_with!{Ghost(3int) => Ghost(g2)}
            let r = x.f(7);
            proof!{ assert(g2 == 4); }
            proof_with!{Tracked(1u64)}
            let q = x.g();
            proof!{ assert(q == 2); }
            r
        }
    } => Ok(())
}

// TODO: update verus_spec macro to support trait methods
test_verify_one_file! {
    // `with` on an implementation of an external trait is not supported: the
    // verified counterpart cannot be added to a trait declared in another crate.
    // The counterparts of the methods of a trait are declared by a companion
    // trait, which is derived from a `with` clause on the trait itself or, for
    // an external trait, on its `external_trait_specification`. A trait that has
    // neither has no companion to implement.
    #[test] test_external_trait_impl code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl core::default::Default for S {
            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn default() -> S {
                S
            }
        }
    } => Err(e) => assert_rust_error_msg_all(e, "cannot find trait `_VERUS_VERIFIED_TRAIT_Default`")
}

test_verify_one_file! {
    // A method of an external trait that has a default body has to be overridden
    // by an implementation that is used through `proof_with!`: the counterpart
    // declared by the companion trait has no default body of its own.
    #[test] test_external_trait_with_default_body code!{
        use vstd::prelude::*;

        #[verifier::external]
        trait T {
            fn g(&self) -> u64 {
                2
            }
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;

            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                requires b == 1,
                ensures r == 2,
            )]
            fn g(&self) -> u64;
        }

        #[verus_verify]
        impl T for S {}

        #[verus_verify]
        fn test() {
            let s = S;
            proof_with!{Tracked(1u64)}
            let q = s.g();
        }
    } => Err(e) => assert_rust_error_msg_all(e, "no method named `_VERUS_VERIFIED_g` found for struct `S`")
}

test_verify_one_file_with_options! {
    // The verified counterpart is named after the function the user wrote, so
    // `--verify-function` selects it and messages do not mention the twin.
    #[test] test_verify_function_selects_counterpart
        ["--verify-function test", "--verify-root"] => code!{
        use vstd::prelude::*;

        #[verus_spec(r =>
            with Tracked(b): Tracked<u64>
            requires b == 1,
            ensures r == 3u64,
        )]
        fn test(a: u64) -> u64 {
            a
        }
    } => Err(err) => assert_eq!(err.errors.len(), 1)
}

test_verify_one_file_with_options! {
    // The counterpart of a method takes the name of the method the user wrote in
    // the friendly name too, which is what `--verify-function` matches on.
    #[test] test_verify_function_selects_method_counterpart
        ["--verify-function S::f", "--verify-root"] => code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl S {
            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                requires b == 1,
                ensures r == 3u64,
            )]
            fn f(&self, a: u64) -> u64 {
                a
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "postcondition not satisfied")
}

test_verify_one_file_with_options! {
    // A trait method is selected by the name the user wrote too, and only the
    // one method named is verified even when the trait has several methods with
    // a `with` clause.
    #[test] test_verify_function_selects_trait_method_counterpart
        ["--verify-function S::g", "--verify-root"] => code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait T {
            #[verus_spec(r =>
                with Ghost(g): Ghost<int>
                ensures r == a,
            )]
            fn f(&self, a: u64) -> u64;

            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                requires b == 1,
                ensures r == 2,
            )]
            fn g(&self) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl T for S {
            #[verus_spec(with Ghost(g): Ghost<int>)]
            fn f(&self, a: u64) -> u64 {
                a
            }

            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn g(&self) -> u64 {
                3
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "postcondition not satisfied")
}

test_verify_one_file_with_options! {
    // The implementation of an external trait is named after the method the user
    // wrote as well, so `--verify-function` picks one of its counterparts.
    #[test] test_verify_function_selects_external_trait_method_counterpart
        ["--verify-function S::g", "--verify-root"] => code!{
        use vstd::prelude::*;

        #[verifier::external]
        trait T {
            fn f(&self, a: u64) -> u64;
            fn g(&self) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;

            #[verus_spec(r =>
                with Ghost(g): Ghost<int>
                ensures r == a,
            )]
            fn f(&self, a: u64) -> u64;

            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                requires b == 1,
                ensures r == 2,
            )]
            fn g(&self) -> u64;
        }

        #[verus_verify]
        impl T for S {
            #[verus_spec(with Ghost(g): Ghost<int>)]
            fn f(&self, a: u64) -> u64 {
                a
            }

            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn g(&self) -> u64 {
                3
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "postcondition not satisfied")
}

// --- The verified counterpart is not callable by hand ---
//
// It is only reachable through the function it belongs to, with `proof_with!`.
// Calling it directly would hand the caller the extra ghost/tracked outputs
// without any obligation to supply the inputs.

test_verify_one_file! {
    #[test] test_counterpart_direct_call_rejected code!{
        use vstd::prelude::*;

        #[verus_spec(r =>
            with Tracked(t): Tracked<u64>
            ensures r == 1,
        )]
        fn f() -> u64 {
            1
        }

        #[verus_spec]
        fn bad() {
            let _x = _VERUS_VERIFIED_f(Tracked::assume_new());
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot be called directly")
}

test_verify_one_file! {
    // The name is only reserved for a counterpart that the macro generated: a
    // function the user happens to give that name to is an ordinary function.
    #[test] test_counterpart_name_without_with_is_ordinary code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            ensures ret == 7,
        )]
        fn _VERUS_VERIFIED_f() -> u64 {
            7
        }

        #[verus_spec]
        fn caller() {
            let x = _VERUS_VERIFIED_f();
            proof!{ assert(x == 7); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // The injected companion-trait bound keeps the generic arguments from the
    // trait bound through which the method is called.
    #[test] test_trait_with_generic_trait_bound code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait Tr<T> {
            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn m(&self, t: T);
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl Tr<u64> for S {
            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn m(&self, _t: u64) {}
        }

        #[verus_spec]
        fn caller<A: Tr<u64>>(a: &A) {
            proof_with!{Ghost(1u64)}
            a.m(1u64);
        }

        #[verus_verify]
        fn test() {
            caller(&S);
        }
    } => Ok(())
}

test_verify_one_file! {
    // The verified counterpart of a method of an external trait is reached even
    // when the implementation lives in a different module than the
    // `external_trait_specification` proxy: the companion trait is generated next
    // to the proxy, so the implementation names it through the same path it uses
    // to name the trait.
    #[test] test_external_trait_with_impl_cross_module code!{
        use vstd::prelude::*;

        mod spec {
            use vstd::prelude::*;

            #[verifier::external]
            pub trait T {
                fn f(&self, a: u64) -> u64;
            }

            #[verus_verify]
            #[verifier::external_trait_specification]
            pub trait ExT {
                type ExternalTraitSpecificationFor: T;

                #[verus_spec(r =>
                    with Ghost(g): Ghost<int> -> g2: Ghost<int>
                    ensures r == a, g2@ == g + 1,
                )]
                fn f(&self, a: u64) -> u64;
            }
        }

        mod imp {
            use vstd::prelude::*;

            #[verus_verify]
            pub struct S;

            #[verus_verify]
            impl super::spec::T for S {
                #[verus_spec(with Ghost(g): Ghost<int> -> g2: Ghost<int>)]
                fn f(&self, a: u64) -> u64 {
                    proof_decl!{ let ghost gg: int = g + 1; }
                    proof_with!{|= Ghost(gg)}
                    a
                }
            }
        }

        use imp::S;
        use spec::T;

        #[verus_verify]
        fn test() {
            let s = S;
            proof_with!{Ghost(3int) => Ghost(g2)}
            let r = s.f(7);
            proof!{ assert(r == 7); assert(g2 == 4); }

            proof_with!{Ghost(3int) => Ghost(g3)}
            let r2 = spec::T::f(&s, 7);
            proof!{ assert(r2 == 7); assert(g3 == 4); }
        }
    } => Ok(())
}
