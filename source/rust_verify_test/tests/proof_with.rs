#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

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

        #[verus_verify]
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
    #[test] test_proof_with_trait code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct A {
            a: u64,
        }

        #[verus_verify]
        trait AOp {
            #[verus_spec(
                with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32>
                requires b == 1, c == 2,
            )]
            fn test(&self) {
            }
        }

        #[verus_verify]
        impl AOp for A {
            #[verus_spec(
                with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32>
            )]
            fn test(&self) {
                proof!{
                    assert(b == 1);
                    assert(c == 0); // FAILS
                }
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
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_proof_with_external code!{
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
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool {
            negate_bool(b, x)
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(1u8)}
            negate_bool(true, 1);
        }

        #[verifier::external]
        fn unverified_call_test() {
            negate_bool(true, 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_with_external_failed code!{
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
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool {
            negate_bool(b, x)
        }

        #[verus_spec]
        fn call_test() {
            negate_bool(true, 1);
        }
    } => Err(e) => assert_vir_error_msg(e, "this function requires 1 extra tracked/ghost argument(s) via proof_with()")
}

test_verify_one_file! {
    #[test] test_proof_with_failed_requires code!{
        use vstd::prelude::*;

        #[verus_spec(
            with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32>
            requires a == 0, b == 1, c == 2,
        )]
        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(0u64), Ghost(2u32)}
            test(0); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_proof_with_invalid_type code!{
        use vstd::prelude::*;

        #[verus_spec(
            with Tracked(b): Tracked<u64>
            requires a == 0, b == 1,
        )]
        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{0u64}
            test(0);
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
}

test_verify_one_file! {
    #[test] test_proof_with_wrong_mode_type code!{
        use vstd::prelude::*;

        #[verus_spec(
            with Tracked(b): Tracked<u64>
            requires a == 0, b == 1,
        )]
        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Ghost(0u64)}
            test(0);
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
}

// ---- Lifetime soundness tests ----
// These tests verify that lifetime constraints on tracked/ghost params are properly checked.

test_verify_one_file! {
    #[test] test_proof_with_lifetime_mismatch code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(c): Tracked<&'a u64>)]
        fn test<'a>(a: &'a u64, b: u64) -> u64 {
            1
        }

        // Accepted: the shim's `'a` is instantiated to a region contained in both
        // 'a and 'b, and `test` only uses `c` for that region. The previous
        // hand-rolled region check rejected this shape and was over-strict; see
        // test_proof_with_lifetime_bound_mismatch for the shape rustc does reject.
        #[verus_spec]
        fn test2<'a, 'b>(a: &'a u64, b: u64, c: Tracked<&'b u64>) -> u64 {
            proof_with!{c}
            test(a, b)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_with_lifetime_compatible code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(c): Tracked<&'a u64>)]
        fn test<'a>(a: &'a u64, b: u64) -> u64 {
            1
        }

        #[verus_spec]
        fn test2<'a, 'b: 'a>(a: &'a u64, b: u64, c: Tracked<&'b u64>) -> u64 {
            proof_with!{c}
            test(a, b)
        }
    } => Ok(())
}

// A lifetime the caller did not write is resolved inside the callee instead of
// being taken from the call site, so an extra declared with one could outlive
// what the caller actually granted. Each spelling of an omitted lifetime is
// rejected where it is written.
test_verify_one_file! {
    #[test] test_declare_with_elided_reference_lifetime code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(c): Tracked<&u64>)]
        fn test<'a>(a: &'a u64) -> u64 {
            1
        }
    } => Err(err) => assert_vir_error_msg(err, "must name its lifetimes explicitly")
}

test_verify_one_file! {
    #[test] test_declare_with_anonymous_lifetime code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(c): Tracked<&'_ u64>)]
        fn test<'a>(a: &'a u64) -> u64 {
            1
        }
    } => Err(err) => assert_vir_error_msg(err, "must name its lifetimes explicitly")
}

test_verify_one_file! {
    #[test] test_declare_with_elided_path_lifetime code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct Perm<'x> { p: &'x u64 }

        #[verus_spec(with Tracked(c): Tracked<Perm>)]
        fn test<'a>(a: &'a u64) -> u64 {
            1
        }
    } => Err(err) => assert_vir_error_msg(err, "must name its lifetimes explicitly")
}

// A lifetime that is written, including `'static`, is accepted.
test_verify_one_file! {
    #[test] test_declare_with_static_lifetime code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(c): Tracked<&'static u64>)]
        fn test<'a>(a: &'a u64) -> u64 {
            1
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_with_lifetime_bound_mismatch code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(c): Tracked<&'b u64>)]
        fn test<'a, 'b: 'a>(a: &'a u64, b: u64) -> &'a u64 {
            a
        }

        #[verus_spec]
        fn test2<'a, 'b>(a: &'a u64, b: u64, c: Tracked<&'b u64>) -> &'a u64 {
            proof_with!{c}
            test(a, b)
        }
    } => Err(err) => assert_rust_error_msg(err, "lifetime may not live long enough")
}

// Same as test_proof_with_lifetime_mismatch but for Ghost: accepted for the same
// reason, since the shim's region is only required to be one both sides satisfy.
test_verify_one_file! {
    #[test] test_declare_with_ghost_lifetime_mismatch code!{
        use vstd::prelude::*;

        #[verus_spec(with Ghost(g): Ghost<&'a u64>)]
        fn test<'a>(a: &'a u64) -> u64 {
            1
        }

        #[verus_spec]
        fn test2<'a, 'b>(a: &'a u64, c: Ghost<&'b u64>) -> u64 {
            proof_with!{c}
            test(a)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_with_generic_type code!{
        use vstd::prelude::*;

        #[verus_spec(
            with Tracked(b): Tracked<T>, Ghost(c): Ghost<u32>
            requires a === b, c == 2,
        )]
        fn test<T>(a: T) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(0u64), Ghost(2u32)}
            test(0u64);
        }

        #[verifier::external]
        fn unverified_call_test() {
            test(0u64);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_with_generic_type2 code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {}

        #[verus_spec(with Tracked(c): Tracked<T2>, Ghost(d): Ghost<u32>)]
        fn test<T1: X, T2>(a: T1, b: T2) {
        }

        #[verus_spec]
        fn call_test<T1: X, T2>(a: T1, b: T2, c: Tracked<T2>, d: Ghost<u32>) {
            proof_with!{c, d}
            test(a, b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_with_generic_type_wrong_type code!{
        use vstd::prelude::*;

        #[verus_spec(
            with Tracked(b): Tracked<T>, Ghost(c): Ghost<u32>
            requires a === b, c == 2,
        )]
        fn test<T>(a: T) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(0u8), Ghost(2u32)}
            test(0u64);
        }

        #[verifier::external]
        fn unverified_call_test() {
            test(0u64);
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
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
        fn call_test(mut a: A, mut b: A) {
            proof_with!{Tracked(&mut a), Ghost(2u32)}
            test(&mut a);
        }
    } => Err(e) => assert_rust_error_msg_skip_spec_msgs(e, "cannot borrow `a` as mutable more than once at a time")
}

// ---- escape hatch: bare `declare_with()` spellings ----
//
// These exercise the written-lifetime rule at the `declare_with()` call itself
// rather than through a `with` clause, so they stay in bare form by design: the
// shapes they test (no type annotation at all, and a turbofish instead of a let
// annotation) have no `#[verus_spec(with ...)]` spelling.

// Without a written type the extra's regions would come from inference, which is
// the same hazard as an elided lifetime. rustc reports this one first.
test_verify_one_file! {
    #[test] test_declare_with_unwritten_type verus_code!{
        use vstd::prelude::*;
        fn test<'a>(a: &'a u64) -> u64
        {
            let c = declare_with();
            1
        }
    } => Err(err) => assert_rust_error_msg(err, "type annotations needed")
}

// A `with` clause writes the type as a turbofish rather than a let annotation,
// so the same rule has to reach through it.
test_verify_one_file! {
    #[test] test_declare_with_turbofish_lifetime verus_code!{
        use vstd::prelude::*;
        fn test<'a>(a: &'a u64) -> u64
        {
            let c = declare_with::<Tracked<&'a u64>>();
            1
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_declare_with_turbofish_elided_lifetime verus_code!{
        use vstd::prelude::*;
        fn test<'a>(a: &'a u64) -> u64
        {
            let c = declare_with::<Tracked<&u64>>();
            1
        }
    } => Err(err) => assert_vir_error_msg(err, "must name its lifetimes explicitly")
}

// A bare `declare_with()` in the body is *not* what makes the macro emit a
// shim — only a `with` clause is. A function written this way therefore has no
// shim unless the user supplies one, which is the escape hatch: the extras are
// still checked by rustc, against a parameter list the user wrote.
test_verify_one_file! {
    #[test] test_escape_hatch_hand_written_shim code!{
        use vstd::prelude::*;

        #[verus_verify]
        fn callee<'a>(a: u64, b: &'a u64) -> u64 {
            let c: Ghost<&'a u64> = declare_with();
            1
        }

        // exactly what the macro would have generated from
        // `#[verus_spec(with Ghost(c): Ghost<&'a u64>)]`
        #[doc(hidden)]
        #[allow(non_snake_case, unused)]
        #[verus::internal(with_shim)]
        #[verifier::external_body]
        fn _VERUS_WITH_callee<'a>(a: u64, b: &'a u64, __verus_with_in_0: Ghost<&'a u64>) -> u64 {
            unimplemented!()
        }

        #[verus_verify]
        fn caller() {
            proof_with!{Ghost(&0u64)}
            let r = callee(5, &7);
        }
    } => Ok(())
}

// Without that hand-written shim there is nothing for the call site to be
// redirected to, so the call is rejected rather than silently losing its extra.
test_verify_one_file! {
    #[test] test_escape_hatch_missing_shim code!{
        use vstd::prelude::*;

        #[verus_verify]
        fn callee<'a>(a: u64, b: &'a u64) -> u64 {
            let c: Ghost<&'a u64> = declare_with();
            1
        }

        #[verus_verify]
        fn caller() {
            proof_with!{Ghost(&0u64)}
            let r = callee(5, &7);
        }
    } => Err(e) => assert_vir_error_msg(e, "`callee` is not declared with extra ghost/tracked arguments")
}

// The shim name is reserved by convention only. A function that merely happens
// to be called `_VERUS_WITH_f`, without the marker attribute the macro stamps,
// is an ordinary function: it may be called directly, and the rewrite does not
// mistake it for a shim.
test_verify_one_file! {
    #[test] test_reserved_shim_name_without_marker_is_ordinary code!{
        use vstd::prelude::*;

        #[verus_verify]
        fn callee(a: u64) -> u64 { 1 }

        #[verus_verify]
        #[allow(non_snake_case)]
        fn _VERUS_WITH_callee(a: u64, g: Ghost<u64>) -> u64 { 1 }

        // an ordinary call, with no `proof_with` involved
        #[verus_verify]
        fn call_directly() {
            let r = _VERUS_WITH_callee(5, Ghost::assume_new());
        }

        #[verus_verify]
        fn call_with_extras() {
            proof_with!{Ghost(3u64)}
            let r = callee(5);
        }
    } => Err(e) => assert_vir_error_msg(e, "`callee` is not declared with extra ghost/tracked arguments")
}

// The name is reserved only when the macro is actually generating the shim,
// which happens exactly when `callee` carries a `with` clause. A hand-written
// shim then collides, and rustc blames the `with` clause that generated it.
test_verify_one_file! {
    #[test] test_hand_written_shim_collides_with_generated_shim code!{
        use vstd::prelude::*;

        #[verus_spec(with Ghost(c): Ghost<u64>)]
        fn callee(a: u64) -> u64 { 1 }

        #[doc(hidden)]
        #[allow(non_snake_case, unused)]
        #[verus::internal(with_shim)]
        #[verifier::external_body]
        fn _VERUS_WITH_callee(a: u64, __verus_with_in_0: Ghost<u64>) -> u64 {
            unimplemented!()
        }
    } => Err(err) => assert_rust_error_msg(err, "the name `_VERUS_WITH_callee` is defined multiple times")
}

// ---- declare_ret_with / proof_with_ret tests ----

test_verify_one_file! {
    #[test] test_declare_ret_with_basic code!{
        use vstd::prelude::*;

        #[verus_spec(with -> out1: Tracked<u8>)]
        fn callee(a: u64) -> u64 {
            proof!{ out1 = Tracked(42u8); }
            1
        }

        #[verus_spec]
        fn call_test() {
            proof_decl!{ let tracked extra: u8; }
            proof_with!{=> Tracked(extra): Tracked<u8>}
            let ret = callee(5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_declare_ret_with_no_assigned code!{
        use vstd::prelude::*;

        #[verus_spec(with -> out1: Tracked<u8>)]
        fn callee(a: u64) -> u64 {
            1
        }

        #[verus_spec]
        fn call_test() {
            proof_decl!{ let tracked extra: u8; }
            proof_with!{=> Tracked(extra): Tracked<u8>}
            let ret = callee(5);
        }
    } => Err(e) => assert_any_vir_error_msg(e, "declare_ret_with() variable must be assigned to")
}

test_verify_one_file! {
    #[test] test_declare_ret_with_multiple code!{
        use vstd::prelude::*;

        #[verus_spec(with -> out1: Tracked<u8>, out2: Ghost<u32>)]
        fn callee(a: u64) -> u64 {
            proof!{
                out1 = Tracked(42u8);
                out2 = Ghost(7u32);
            }
            1
        }

        #[verus_spec]
        fn call_test() {
            proof_decl!{
                let tracked e1: u8;
                let ghost e2: u32;
            }
            proof_with!{=> (Tracked(e1), Ghost(e2)): (Tracked<u8>, Ghost<u32>)}
            let ret = callee(5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_declare_ret_with_with_inputs code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(inp): Tracked<u64> -> out1: Tracked<u8>)]
        fn callee(a: u64) -> u64 {
            proof!{ out1 = Tracked(0u8); }
            1
        }

        #[verus_spec]
        fn call_test() {
            proof_decl!{ let tracked extra: u8; }
            proof_with!{Tracked(42u64) => Tracked(extra): Tracked<u8>}
            let ret = callee(5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_declare_ret_with_ensures code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with -> out1: Tracked<u8>
            ensures ret == 1, out1@ == 42,
        )]
        fn callee(a: u64) -> u64 {
            proof!{ out1 = Tracked(42u8); }
            1
        }

        #[verus_spec]
        fn call_test() {
            proof_decl!{ let tracked z2: u8; }
            proof_with!{=> Tracked(z2): Tracked<u8>}
            let _ret = callee(5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_declare_ret_with_ensures_fail code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with -> out1: Tracked<u8>
            ensures ret == 1, out1@ == 42,
        )]
        fn callee(a: u64) -> u64 {
            proof!{ out1 = Tracked(10u8); } // FAILS
            1
        }
    } => Err(e) => assert!(e.errors.len() > 0)
}

// Ensures propagation when both an input and an output extra are declared: the
// caller must be able to assert postconditions about the extra return values as
// well as the exec return value.
test_verify_one_file! {
    #[test] test_declare_ret_with_caller_assert code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with -> out1: Tracked<u8>
            ensures ret == 1, out1@ == 42,
        )]
        fn callee(a: u64) -> u64 {
            proof!{ out1 = Tracked(42u8); }
            1
        }

        #[verus_spec]
        fn call_test() {
            proof_decl!{ let tracked z2: u8; }
            proof_with!{=> Tracked(z2): Tracked<u8>}
            let _ret = callee(5);
            proof!{
                assert(z2 == 42);
                assert(_ret == 1);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_declare_with_and_ret_with_ensures code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with Ghost(w): Ghost<u32> -> z: Ghost<u32>
            requires w < 100,
            ensures ret == x, z@ == x,
        )]
        fn callee(x: u32) -> u32 {
            proof!{ z = Ghost(x); }
            x
        }

        #[verus_spec]
        fn caller_test() {
            proof_decl!{ let ghost zz: u32; }
            proof_with!{Ghost(0u32) => Ghost(zz): Ghost<u32>}
            let _ret = callee(1);
            proof!{
                assert(zz == 1);   // from z@ == x postcondition
                assert(_ret == 1); // from ret == x postcondition
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_with_tracked_mut_ensures code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with Tracked(y): Tracked<u64>
            requires (x as u64) < 100, y < 100,
            ensures ret == x,
        )]
        fn set_val(x: u32) -> u32 {
            x
        }

        #[verus_spec]
        fn caller_test() {
            proof_with!{Tracked(1u64)}
            let ret = set_val(1);
            proof!{ assert(ret == 1); }

            proof_with!{Tracked(42u64)}
            let ret2 = set_val(42);
            proof!{ assert(ret2 == 42); }
        }
    } => Ok(())
}

// rustc detects when an extra borrows the same place as an exec argument
test_verify_one_file! {
    #[test] test_proof_with_double_borrow_error code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct A { val: u64 }

        #[verus_spec(with Tracked(extra): Tracked<&'a mut A>)]
        fn borrows<'a>(a: &'a mut A) -> u64 {
            1
        }

        #[verus_spec]
        fn bad_caller() {
            let mut a = A { val: 0 };
            // Both the exec arg and the extra borrow the same place - rustc must reject
            proof_with!{Tracked(&mut a)}
            borrows(&mut a);
        }
    } => Err(err) => assert_rust_error_msg_skip_spec_msgs(err, "cannot borrow `a` as mutable more than once")
}

// rustc detects when an extra's lifetime is too short
test_verify_one_file! {
    #[test] test_proof_with_lifetime_too_short_error code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct A { val: u64 }

        #[verus_spec(with Tracked(extra): Tracked<&'a mut A>)]
        fn returns_with_lifetime<'a>(a: &'a mut A) -> &'a mut A {
            a
        }

        #[verus_spec]
        fn bad_caller<'outer>(outer: &'outer mut A) -> &'outer mut A {
            let mut inner = A { val: 0 };
            // The return type forces 'a == 'outer, but `inner` doesn't live long enough
            proof_with!{Tracked(&mut inner)}
            returns_with_lifetime(outer)
        }
    } => Err(err) => assert_rust_error_msg_skip_spec_msgs(err, "cannot return value referencing local variable")
}

// ---- escape hatch: bare `declare_ret_with()` spellings ----
//
// Like the `declare_with()` section above, these test the shape of the
// `declare_ret_with()` call itself --- not used as a let initializer, and
// without `mut` --- which a `with` clause always generates correctly, so they
// have no attribute-surface equivalent. Do not "finish the migration" by
// deleting them.

test_verify_one_file! {
     #[test] test_declare_ret_with_outside_let verus_code!{
        use vstd::prelude::*;
        fn callee(a: u64) -> u64
        {
            declare_ret_with::<Tracked<u8>>();
            1
        }
     } => Err(e) => assert_vir_error_msg(e, "declare_ret_with() must be used as a let initializer")
}

test_verify_one_file! {
     #[test] test_declare_ret_with_requires_mut verus_code!{
        use vstd::prelude::*;
        fn callee(a: u64) -> u64
        {
            let out1: Tracked<u8> = declare_ret_with();
            1
        }
     } => Err(e) => assert_vir_error_msg(e, "declare_ret_with() variable must be declared as `let mut`")
}

// ---- Regression tests: every call site the rewrite must reach ----
//
// The rewrite has to find the generated `proof_with` call wherever the user
// wrote the annotation, including in nested expression positions.

test_verify_one_file! {
    #[test] test_proof_with_method_swapped_modes code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct A;

        #[verus_verify]
        impl A {
            #[verus_spec(with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32>)]
            fn test(&self) {
            }
        }

        #[verus_spec]
        fn call_test() {
            let a = A;
            proof_with!{Ghost(2u32), Tracked(1u64)}
            a.test();
        }
    } => Err(e) => assert_rust_error_msg(e, "arguments to this method are incorrect")
}

test_verify_one_file! {
    #[test] test_proof_with_method_wrong_type code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct A;

        #[verus_verify]
        impl A {
            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn test(&self) {
            }
        }

        #[verus_spec]
        fn call_test() {
            let a = A;
            proof_with!{Tracked(1u8)}
            a.test();
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
}

test_verify_one_file! {
    #[test] test_proof_with_too_many_extras code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<u64>)]
        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(1u64), Ghost(2u32)}
            test(0);
        }
    } => Err(e) => assert_rust_error_msg(e, "this function takes 2 arguments but 3 arguments were supplied")
}

test_verify_one_file! {
    #[test] test_proof_with_too_few_extras code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32>)]
        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(1u64)}
            test(0);
        }
    } => Err(e) => assert_rust_error_msg(e, "this function takes 3 arguments but 2 arguments were supplied")
}

test_verify_one_file! {
    #[test] test_proof_with_in_assignment code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<u64>)]
        fn test(a: u64) -> u64 {
            a
        }

        #[verus_spec]
        fn call_test() {
            let mut x = 0u64;
            x = { proof_with!{Ghost(1u64)} test(0) };
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
}

test_verify_one_file! {
    #[test] test_proof_with_in_binary_operand code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<u64>)]
        fn test(a: u64) -> u64 {
            a
        }

        #[verus_spec]
        fn call_test() {
            let x = { proof_with!{Ghost(1u64)} test(0) } + 1;
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
}

test_verify_one_file! {
    #[test] test_proof_with_in_struct_literal code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct S { a: u64 }

        #[verus_spec(with Tracked(b): Tracked<u64>)]
        fn test(a: u64) -> u64 {
            a
        }

        #[verus_spec]
        fn call_test() {
            let s = S { a: { proof_with!{Ghost(1u64)} test(0) } };
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
}

test_verify_one_file! {
    #[test] test_proof_with_in_closure code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<u64>)]
        fn test(a: u64) -> u64 {
            a
        }

        #[verus_spec]
        fn call_test() {
            let f = || { proof_with!{Ghost(1u64)} test(0) };
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
}

test_verify_one_file! {
    #[test] test_proof_with_inside_impl_method code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<u64>)]
        fn test(a: u64) -> u64 {
            a
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl S {
            #[verus_spec]
            fn caller(&self) -> u64 {
                proof_with!{Ghost(1u64)}
                test(0)
            }
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
}

test_verify_one_file! {
    #[test] test_proof_with_inside_trait_method code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<u64>)]
        fn test(a: u64) -> u64 {
            a
        }

        #[verus_verify]
        trait T {
            #[verus_spec]
            fn caller(&self) -> u64 {
                proof_with!{Ghost(1u64)}
                test(0)
            }
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
}

test_verify_one_file! {
    #[test] test_proof_with_ret_bad_input code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(inp): Tracked<u64> -> out1: Tracked<u8>
            ensures out1@ == 0u8,
        )]
        fn callee(a: u64) -> u64 {
            proof!{ out1 = Tracked(0u8); }
            1
        }

        #[verus_spec]
        fn call_test() {
            proof_decl!{ let tracked o: u8; }
            proof_with!{Ghost(42u64) => Tracked(o): Tracked<u8>}
            let ret = callee(5);
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
}

test_verify_one_file! {
    #[test] test_proof_with_no_such_with code!{
        use vstd::prelude::*;

        #[verus_spec]
        fn test(a: u64) -> u64 { a }

        #[verus_spec]
        fn call_test() {
            proof_with!{Ghost(1u64)}
            let x = test(0);
        }
    } => Err(e) => assert_vir_error_msg(e, "is not declared with extra ghost/tracked arguments")
}

// A shim carries the original's signature plus the extras and no contract, so a
// direct call would produce the original's result with none of its requirements.
test_verify_one_file! {
    #[test] test_direct_call_to_with_shim code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<u64>
            requires a == 1,
        )]
        fn test(a: u64) -> u64 {
            a
        }

        #[verus_spec]
        fn call_test() -> u64 {
            _VERUS_WITH_test(0, Tracked::assume_new())
        }
    } => Err(e) => assert_vir_error_msg(e, "is a shim generated by Verus")
}

test_verify_one_file! {
    #[test] test_direct_call_to_with_shim_method code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct A;

        #[verus_verify]
        impl A {
            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn test(&self) -> u64 {
                1
            }
        }

        #[verus_spec]
        fn call_test() -> u64 {
            let a = A;
            a._VERUS_WITH_test(Tracked::assume_new())
        }
    } => Err(e) => assert_vir_error_msg(e, "is a shim generated by Verus")
}

// A call site is checked against the trait method's shim but dispatches to the
// impl, so the impl's `with` clause must agree with the trait's. On the
// attribute surface the rustc conformance check catches an arity mismatch first,
// so this bare form is the only coverage of the VIR-level arity check that
// guards the `vir/src/modes.rs` assertion. Keep both.
test_verify_one_file! {
    #[test] test_trait_impl_with_arity_mismatch_vir verus_code!{
        use vstd::prelude::*;
        trait AOp {
            fn test(&self) {
                let b: Tracked<u64> = declare_with();
            }
        }
        struct A;
        impl AOp for A {
            fn test(&self) {
                let b: Tracked<u64> = declare_with();
                let c: Ghost<u32> = declare_with();
            }
        }
    } => Err(e) => assert_vir_error_msg(e, "but the trait method declares 1")
}

test_verify_one_file! {
    #[test] test_trait_impl_with_arity_mismatch code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait AOp {
            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn test(&self) {
            }
        }

        #[verus_verify]
        struct A;

        #[verus_verify]
        impl AOp for A {
            #[verus_spec(with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32>)]
            fn test(&self) {
            }
        }
    } => Err(e) => assert_help_error_msg(e, "expected a tuple with 2 elements, found one with 1 element")
}

// ---- trait/impl `with` conformance is checked by rustc ----
//
// The impl's `with` clause is checked against the trait's by a closure planted
// in the impl body, which calls a companion shim with the impl's own lifetimes
// named explicitly. The closure takes the extras as parameters rather than
// capturing them, so nothing in the real body is moved or borrowed.

test_verify_one_file! {
    #[test] test_trait_impl_with_type_mismatch code!{
        use vstd::prelude::*;
        #[verus_verify]
        trait AOp {
            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn test(&self);
        }
        #[verus_verify]
        struct A;
        #[verus_verify]
        impl AOp for A {
            #[verus_spec(with Ghost(b): Ghost<u32>)]
            fn test(&self) {
            }
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
}

// Regions are part of the agreement: the caller is checked against the trait's
// shim, so an impl may not name a lifetime the trait did not grant.
test_verify_one_file! {
    #[test] test_trait_impl_with_lifetime_match code!{
        use vstd::prelude::*;
        #[verus_verify]
        trait AOp {
            #[verus_spec(with Tracked(b): Tracked<&'a u64>)]
            fn test<'a, 'b>(&self, x: &'a u64, y: &'b u64);
        }
        #[verus_verify]
        struct A;
        #[verus_verify]
        impl AOp for A {
            #[verus_spec(with Tracked(b): Tracked<&'a u64>)]
            fn test<'a, 'b>(&self, x: &'a u64, y: &'b u64) {
            }
        }
    } => Ok(())
}

// This test is what stops a future refactor from dropping the explicit
// lifetimes and silently making the whole conformance check vacuous.
test_verify_one_file! {
    #[test] test_trait_impl_with_lifetime_mismatch code!{
        use vstd::prelude::*;
        #[verus_verify]
        trait AOp {
            #[verus_spec(with Tracked(b): Tracked<&'a u64>)]
            fn test<'a, 'b>(&self, x: &'a u64, y: &'b u64);
        }
        #[verus_verify]
        struct A;
        #[verus_verify]
        impl AOp for A {
            #[verus_spec(with Tracked(b): Tracked<&'b u64>)]
            fn test<'a, 'b>(&self, x: &'a u64, y: &'b u64) {
            }
        }
    } => Err(e) => assert_rust_error_msg(e, "lifetime may not live long enough")
}

test_verify_one_file! {
    #[test] test_trait_impl_with_lifetime_static code!{
        use vstd::prelude::*;
        #[verus_verify]
        trait AOp {
            #[verus_spec(with Tracked(b): Tracked<&'a u64>)]
            fn test<'a, 'b>(&self, x: &'a u64, y: &'b u64);
        }
        #[verus_verify]
        struct A;
        #[verus_verify]
        impl AOp for A {
            #[verus_spec(with Tracked(b): Tracked<&'static u64>)]
            fn test<'a, 'b>(&self, x: &'a u64, y: &'b u64) {
            }
        }
    } => Err(e) => assert_rust_error_msg(e, "lifetime may not live long enough")
}

test_verify_one_file! {
    #[test] test_trait_impl_with_lifetime_from_impl code!{
        use vstd::prelude::*;
        #[verus_verify]
        trait AOp<'a> {
            #[verus_spec(with Tracked(b): Tracked<&'a u64>)]
            fn test(&self, x: &'a u64);
        }
        #[verus_verify]
        struct A<'x>(&'x u64);
        #[verus_verify]
        impl<'x> AOp<'x> for A<'x> {
            #[verus_spec(with Tracked(b): Tracked<&'x u64>)]
            fn test(&self, x: &'x u64) {
            }
        }
    } => Ok(())
}

// ---- `with` on a proxy for a foreign trait (known gap) ----
//
// Both the call-site shim and the conformance companion are defaulted methods
// of the trait that declares the clause. That is what makes them reachable:
// naming the trait is a precondition for calling the method and for writing an
// impl. An `external_trait_specification` proxy breaks it --- callers and
// impls name the foreign trait and never the proxy --- so the shim could never
// be found. This is a regression against the `proof-with-builtin` branch, which
// supported it; the shim design buys trait default bodies in exchange.
//
// TODO(external-trait with): these flip to Ok(()) when support lands.

test_verify_one_file! {
    #[test] test_external_trait_with_rejected code!{
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
                with Ghost(g): Ghost<u64>
                ensures r == a,
            )]
            fn f(&self, a: u64) -> u64;
        }
    } => Err(e) => assert_vir_error_msg(e, "`with` is not supported on an `external_trait_specification` trait")
}

// A defaulted proxy method is syntactically an `ItemFn` and reaches a different
// arm of the macro, so it needs its own test.
test_verify_one_file! {
    #[test] test_external_trait_with_default_body_rejected code!{
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
                with Ghost(g): Ghost<u64>
                ensures r == a,
            )]
            fn f(&self, a: u64) -> u64 {
                a
            }
        }
    } => Err(e) => assert_vir_error_msg(e, "`with` is not supported on an `external_trait_specification` trait")
}

// A proxy without a `with` clause is unaffected.
test_verify_one_file! {
    #[test] test_external_trait_without_with_still_works code!{
        use vstd::prelude::*;
        #[verifier::external]
        trait T {
            fn f(&self, a: u64) -> u64;
        }
        #[verus_verify]
        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;

            #[verus_spec(r => ensures r == a)]
            fn f(&self, a: u64) -> u64;
        }
    } => Ok(())
}

// ---- variance of the `with` extras across a trait/impl boundary ----
//
// At a virtual call the caller supplies the extra input at the *trait's* type
// and receives the extra output at the trait's type, so soundness is ordinary
// function subtyping: inputs are contravariant (`I_trait <: I_impl`, the impl
// must accept anything a caller can send) and outputs are covariant
// (`O_impl <: O_trait`, the impl may promise more but never less).
//
// The companion puts each side in its correct position: the declared outputs
// are its parameters and the declared inputs are its return type. All four
// corners are tested below. `LongOut` in particular must stay `Ok(())` --- it
// is the only test that documents outputs being covariant rather than
// invariant, so without it a future change could re-invert the check and
// leave every other test green.

test_verify_one_file! {
    #[test] test_trait_impl_with_direction_good code!{
        use vstd::prelude::*;
        #[verus_verify]
        trait AOp {
            #[verus_spec(with Tracked(b): Tracked<&'a u64> -> g: Ghost<&'a u64>)]
            fn test<'a, 'b>(&self, x: &'a u64, y: &'b u64);
        }
        #[verus_verify]
        struct A;
        #[verus_verify]
        impl AOp for A {
            #[verus_spec(with Tracked(b): Tracked<&'a u64> -> g: Ghost<&'a u64>)]
            fn test<'a, 'b>(&self, x: &'a u64, y: &'b u64) {
                proof!{ g = Ghost(x); }
            }
        }
    } => Ok(())
}

// The impl assumes a longer-lived input than the trait granted, so a caller
// holding only a `&'a` extra could not call it. Unsound; must be rejected.
test_verify_one_file! {
    #[test] test_trait_impl_with_direction_long_in code!{
        use vstd::prelude::*;
        #[verus_verify]
        trait AOp {
            #[verus_spec(with Tracked(b): Tracked<&'a u64> -> g: Ghost<&'a u64>)]
            fn test<'a, 'b>(&self, x: &'a u64, y: &'b u64);
        }
        #[verus_verify]
        struct A;
        #[verus_verify]
        impl AOp for A {
            #[verus_spec(with Tracked(b): Tracked<&'static u64> -> g: Ghost<&'a u64>)]
            fn test<'a, 'b>(&self, x: &'a u64, y: &'b u64) {
                proof!{ g = Ghost(x); }
            }
        }
    } => Err(e) => assert_rust_error_msg(e, "lifetime may not live long enough")
}

// The impl promises a longer-lived output than the trait did. That is exactly
// as safe as returning `&'static` where `&'a` was promised, so it is accepted.
test_verify_one_file! {
    #[test] test_trait_impl_with_direction_long_out code!{
        use vstd::prelude::*;
        #[verus_verify]
        trait AOp {
            #[verus_spec(with Tracked(b): Tracked<&'a u64> -> g: Ghost<&'a u64>)]
            fn test<'a, 'b>(&self, x: &'a u64, y: &'b u64);
        }
        #[verus_verify]
        struct A;
        #[verus_verify]
        impl AOp for A {
            #[verus_spec(with Tracked(b): Tracked<&'a u64> -> g: Ghost<&'static u64>)]
            fn test<'a, 'b>(&self, x: &'a u64, y: &'b u64) {
                proof!{ g = Ghost(&0u64); }
            }
        }
    } => Ok(())
}

// The impl promises a shorter-lived output than the trait did, so a caller
// would receive an extra that does not live as long as promised.
test_verify_one_file! {
    #[test] test_trait_impl_with_direction_short_out code!{
        use vstd::prelude::*;
        #[verus_verify]
        trait AOp {
            #[verus_spec(with Tracked(b): Tracked<&'a u64> -> g: Ghost<&'a u64>)]
            fn test<'a, 'b>(&self, x: &'a u64, y: &'b u64);
        }
        #[verus_verify]
        struct A;
        #[verus_verify]
        impl AOp for A {
            #[verus_spec(with Tracked(b): Tracked<&'a u64> -> g: Ghost<&'b u64>)]
            fn test<'a, 'b>(&self, x: &'a u64, y: &'b u64) {
                proof!{ g = Ghost(y); }
            }
        }
    } => Err(e) => assert_rust_error_msg(e, "lifetime may not live long enough")
}

// The check must not move or borrow anything the real body still needs.
// `Tracked<T>`/`Ghost<T>` are `PhantomData<T>`, so neither is `Copy`: a
// checking closure that captured the extras would move them at construction.
test_verify_one_file! {
    #[test] test_trait_impl_with_body_consumes_tracked_input code!{
        use vstd::prelude::*;
        #[verus_verify]
        struct T { v: u64 }
        #[verus_verify]
        trait AOp {
            #[verus_spec(with Tracked(b): Tracked<T>)]
            fn test(&self);
        }
        #[verus_verify]
        struct A;
        #[verus_verify]
        impl AOp for A {
            #[verus_spec(with Tracked(b): Tracked<T>)]
            fn test(&self) {
                proof!{
                    let tracked z = b;
                }
            }
        }
    } => Ok(())
}

// The exec parameters are just as non-`Copy` as the extras.
test_verify_one_file! {
    #[test] test_trait_impl_with_by_value_self_and_noncopy_arg code!{
        use vstd::prelude::*;
        #[verus_verify]
        struct T { v: u64 }
        #[verus_verify]
        trait BOp: Sized {
            #[verus_spec(with Tracked(b): Tracked<T>)]
            fn consume(self, s: Vec<u8>) -> Vec<u8>;
        }
        #[verus_verify]
        struct B { v: u64 }
        #[verus_verify]
        impl BOp for B {
            #[verus_spec(with Tracked(b): Tracked<T>)]
            fn consume(self, s: Vec<u8>) -> Vec<u8> {
                proof!{
                    let tracked z = b;
                }
                let mut s = s;
                s.push((self.v % 256) as u8);
                s
            }
        }
    } => Ok(())
}

// A trait method that declares no extras has no shim, so the impl's `with`
// clause is unusable at any call site; say so rather than only reporting the
// arity difference.
test_verify_one_file! {
    #[test] test_trait_impl_with_not_on_trait verus_code!{
        use vstd::prelude::*;
        trait AOp {
            fn test(&self);
        }
        struct A;
        impl AOp for A {
            fn test(&self) {
                let b: Tracked<u64> = declare_with();
            }
        }
    } => Err(e) => assert_vir_error_msg(e, "must be declared on the trait method")
}

// ---- `#[verus_spec(with ...)]` in external, cross-module and trait contexts ----
//
// Merged from the former verus_spec_proof_with.rs. These cover the surfaces the
// clause has to reach beyond a plain free function: `external_fn_specification`,
// a callee in another module, and trait methods with and without a default body.

test_verify_one_file! {
    #[test] test_external_fn_with_declare_with code!{
        #[verifier::external]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with
                Tracked(extra): Tracked<u8>
                -> z: Tracked<u8>
            requires
                x == extra,
            ensures
                ret == !b,
                z@ == extra,
        )]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool {
            proof!{z = Tracked::assume_new();}
            negate_bool(b, x)
        }

        #[verus_spec]
        fn test_call_external_proof_with() {
            proof_decl!{
                let tracked z;
            }
            proof_with!{Tracked(1u8) => Tracked(z): Tracked<u8>}
            let ret = negate_bool(true, 1);
            proof!{
                assert(!ret);
                assert(z == 1u8);
            }

            proof_with!{Tracked(1u8)}
            let ret = negate_bool(true, 1);
            proof!{
                assert(!ret);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Calling an external function with declare_with but missing proof_with should fail
    #[test] test_external_fn_missing_proof_with code!{
        #[verifier::external]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with
                Tracked(extra): Tracked<u8>
            requires
                x == extra,
            ensures
                ret == !b,
        )]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool {
            negate_bool(b, x)
        }

        #[verus_spec]
        fn test_call_external_no_proof_with() {
            let ret = negate_bool(true, 1); // should fail
        }
    } => Err(e) => assert_vir_error_msg(e, "proof_with()")
}

test_verify_one_file! {
    // Calling an external function with wrong requires should fail verification
    #[test] test_external_fn_failed_requires code!{
        #[verifier::external]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with
                Tracked(extra): Tracked<u8>
            requires
                x == extra,
            ensures
                ret == !b,
        )]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool {
            negate_bool(b, x)
        }

        #[verus_spec]
        fn test_call_wrong_requires() {
            proof_with!{Tracked(99u8)}
            let ret = negate_bool(true, 1); // FAILS: x=1 != extra@=99
        }
    } => Err(e) => assert_one_fails(e)
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

test_verify_one_file! {
    #[test] test_trait_method code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret=>
                with
                    Ghost(extra): Ghost<u64>,
                requires
                    a < 100 && extra@ < 100,
                ensures
                    ret == a,
            )]
            fn copy_u64(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(ret=>
                with
                    Ghost(extra): Ghost<u64>,
            )]
            fn copy_u64(&self, a: u64) -> u64 {
                a
            }
        }

        #[verus_spec]
        fn test_call_trait_method(s: &S) {
            proof_with!{Ghost(5u64)}
            let ret = s.copy_u64(10);
            proof!{assert(ret == 10);}
        }
    } => Ok(())
}

// The shim is a defaulted method of the trait, so a default body on the original
// method stays legal and an impl that inherits it needs no `with` clause.
test_verify_one_file! {
    #[test] test_trait_method_with_default_body code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret=>
                with
                    Ghost(extra): Ghost<u64>,
                requires
                    a < 100 && extra@ < 100,
                ensures
                    ret == a,
            )]
            fn copy_u64(&self, a: u64) -> u64 {
                a
            }
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {}

        #[verus_spec]
        fn test_call_default(s: &S) {
            proof_with!{Ghost(5u64)}
            let ret = s.copy_u64(10);
            proof!{assert(ret == 10);}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_trait_method_missing_proof_with code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret=>
                with
                    Ghost(extra): Ghost<u64>,
                ensures
                    ret == a,
            )]
            fn copy_u64(&self, a: u64) -> u64 {
                a
            }
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {}

        #[verus_spec]
        fn test_call_missing(s: &S) {
            let ret = s.copy_u64(10);
        }
    } => Err(e) => assert_vir_error_msg(e, "proof_with()")
}

test_verify_one_file! {
    #[test] test_trait_method_impl_with_mismatch code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret=>
                with
                    Ghost(extra): Ghost<u64>,
            )]
            fn copy_u64(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(ret=>
                with
                    Tracked(extra): Tracked<u64>,
            )]
            fn copy_u64(&self, a: u64) -> u64 {
                a
            }
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
}

// ---- ported from `proof-with-builtin`: grouped positive cases ----
//
// Independent positive cases are grouped into a single `=> Ok(())` test, one
// case per module so that names do not clash and a failure points at the case;
// failing cases are kept separate so each keeps its own asserted diagnostic.

// Wrap the source of one case in a named module, keeping the cases of a grouped
// test independent.
fn in_mod(name: &str, body: &str) -> String {
    format!("mod {name} {{\n{body}\n}}\n")
}

// A function `f` that requires its `Tracked` input to equal its argument.
const FN_WITH_TRACKED_EQ: &str = code_str! {
    use vstd::prelude::*;

    #[verus_spec(ret =>
        with Tracked(t): Tracked<u8>
        requires t == a,
        ensures ret == a,
    )]
    pub fn f(a: u8) -> u8 {
        a
    }
};

test_verify_one_file! {
    #[test] test_attribute_form_group
        code_str!{
            use vstd::prelude::*;

            // free function with extra Tracked and Ghost inputs
            #[verus_spec(
                with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32>
                requires a == 0, b == 1, c == 2,
            )]
            fn free_fn(a: u64) {}

            #[verus_spec]
            fn call_free() {
                proof_with!{Tracked(1u64), Ghost(2u32)}
                free_fn(0);
            }

            // inherent method with extra inputs
            #[verus_verify]
            struct A {
                a: u64,
            }

            #[verus_verify]
            impl A {
                #[verus_spec(
                    with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32>
                    requires self.a == 0, b == 1, c == 2,
                )]
                fn m(&self) {}
            }

            #[verus_spec]
            fn call_method() {
                let a = A { a: 0 };
                proof_with!{Tracked(1u64), Ghost(2u32)}
                a.m();
            }

            // the extra Tracked reference may outlive the return with a `'b: 'a` bound
            #[verus_spec(with Tracked(c): Tracked<&'a u64>)]
            fn lt<'a>(a: &'a u64, b: u64) -> &'a u64 {
                a
            }

            #[verus_spec]
            fn lt_caller<'a, 'b: 'a>(a: &'a u64, b: u64, c: Tracked<&'b u64>) -> &'a u64 {
                proof_with!{c}
                lt(a, b)
            }

            // the extra input's type may be a generic parameter
            #[verus_spec(with Tracked(b): Tracked<T>)]
            fn gen<T>(a: T) {}

            #[verus_spec]
            fn call_gen() {
                proof_with!{Tracked(1u64)}
                gen(0u64);
            }
        }.to_string()
        // a call inside a closure body, a separate body in the same owner, is
        // rewritten too
        + &in_mod("closure_call", &(FN_WITH_TRACKED_EQ.to_string() + code_str!{
            #[verus_verify]
            fn call_in_closure() {
                let c = || -> u8 {
                    proof_with!{Tracked(3u8)}
                    let y = f(3);
                    y
                };
                let _v = c();
            }
        }))
    => Ok(())
}

test_verify_one_file! {
    // A wrong extra argument fails the precondition it was supposed to
    // establish.
    #[test] test_proof_with_failed_or_missing code!{
        use vstd::prelude::*;

        #[verus_spec(
            with Tracked(b): Tracked<u64>
            requires b == 1,
        )]
        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_wrong() {
            proof_with!{Tracked(2u64)}
            test(0); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

// ---- ported: type, mode and lifetime checking is done by rustc ----

test_verify_one_file! {
    // rustc checks the extra arguments of a rewritten call; a wrong extra type
    // is a `mismatched types` error in every form.
    #[test] test_mismatched_extra_type_rejected
        code_str!{
            use vstd::prelude::*;

            // a wrong type for a `Tracked` input
            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn f1(a: u64) {}

            #[verus_spec]
            fn c1() {
                proof_with!{Tracked(1u32)}
                f1(0);
            }

            // a `Ghost` value where a `Tracked` input is declared
            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn f2(a: u64) {}

            #[verus_spec]
            fn c2() {
                proof_with!{Ghost(1u64)}
                f2(0);
            }

            // a wrong type for a generic `Tracked` input
            #[verus_spec(with Tracked(b): Tracked<T>)]
            fn f3<T>(a: T) {}

            #[verus_spec]
            fn c3() {
                proof_with!{Tracked(1u32)}
                f3(0u64);
            }
        }.to_string()
    => Err(e) => {
        // one error per case, so no case can stop being rejected unnoticed
        assert_eq!(e.errors.len(), 3);
        assert_rust_error_msg_all(e, "mismatched types");
    }
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
    // The extra `Tracked`/`Ghost` input keeps its lifetime obligations: a
    // shorter-lived reference passed where a longer-lived one is declared is a
    // `lifetime may not live long enough` error.
    #[test] test_proof_with_lifetime_mismatch_both_modes
        // through a `Tracked` input
        in_mod("tracked", code_str!{
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
        })
        // through a `Ghost` input
        + &in_mod("ghost", code_str!{
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
        })
    => Err(e) => assert_rust_error_msgs(
        e,
        &["lifetime may not live long enough", "lifetime may not live long enough"],
    )
}

// ---- ported: extra ghost/tracked outputs ----

test_verify_one_file! {
    #[test] test_extra_outputs_group
        code_str!{
            use vstd::prelude::*;

            // one extra Ghost output, bound at the call site
            #[verus_spec(ret =>
                with -> z: Ghost<u32>
                ensures ret == 1u64, z@ == 2u32,
            )]
            fn one_output() -> u64 {
                proof!{ z = Ghost(2u32); }
                1
            }

            #[verus_spec]
            fn call_bind() {
                proof_decl!{ let ghost z: u32; }
                proof_with!{=> Ghost(z): Ghost<u32>}
                let r = one_output();
                proof!{ assert(r == 1); assert(z == 2); }
            }

            // several extra outputs, bound as a tuple
            #[verus_spec(ret =>
                with -> y: Ghost<u8>, z: Ghost<u32>
                ensures ret == 1u64, y@ == 3u8, z@ == 2u32,
            )]
            fn many_outputs() -> u64 {
                proof!{ y = Ghost(3u8); z = Ghost(2u32); }
                1
            }

            #[verus_spec]
            fn call_many() {
                proof_decl!{ let ghost y: u8; let ghost z: u32; }
                proof_with!{=> (Ghost(y), Ghost(z)): (Ghost<u8>, Ghost<u32>)}
                let r = many_outputs();
                proof!{ assert(r == 1); assert(y == 3); assert(z == 2); }
            }

            // extra inputs (including a `Tracked` mutable reference) and an
            // output together
            #[verus_spec(ret =>
                with Tracked(y): Tracked<&'a mut int>, Ghost(w): Ghost<u32> -> z: Ghost<u32>
                requires x < 100, *old(y) < 100,
                ensures *final(y) == x, ret == x, z@ == x,
            )]
            fn inout<'a>(x: u32) -> u32 {
                proof!{
                    *y = x as int;
                    z = Ghost(x);
                }
                x
            }

            #[verus_spec]
            fn call_inout() {
                proof_decl!{
                    let tracked mut y = 0int;
                    let ghost z: u32;
                }
                proof_with!{Tracked(&mut y), Ghost(0u32) => Ghost(z): Ghost<u32>}
                let r = inout(1);
                proof!{ assert(r == 1); assert(y == 1); assert(z == 1); }
            }
        }.to_string()
    => Ok(())
}

test_verify_one_file! {
    #[test] test_ret_with_ensures_fail code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with -> z: Ghost<u32>
            ensures z@ == 2u32, // FAILS
        )]
        fn test() -> u64 {
            proof!{ z = Ghost(3u32); }
            1
        }
    } => Err(e) => assert_one_fails(e)
}

// ---- ported: calls through a path or an alias reach the same shim ----

// A function with an extra `Tracked` input, in a submodule, and an alias to it.
const MOD_FN_WITH_TRACKED: &str = code_str! {
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
};

test_verify_one_file! {
    #[test] test_paths_and_aliases_group
        // a qualified path and a module-item alias both reach the shim
        in_mod("qualified_paths", &(MOD_FN_WITH_TRACKED.to_string() + code_str!{
            #[verus_spec]
            fn call_qualified() {
                proof_with!{Tracked(1u64)}
                m::test(0);
            }

            #[verus_spec]
            fn call_aliased() {
                proof_with!{Tracked(1u64)}
                aliased(0);
            }
        }))
        // a function defined in another module is reached from the call site
        + &in_mod("cross_module", code_str!{
            use vstd::prelude::*;

            mod inner {
                use vstd::prelude::*;

                #[verus_spec(ret =>
                    with Ghost(extra): Ghost<u64>
                    requires a < 100 && extra@ < 100,
                    ensures ret == a,
                )]
                pub fn copy_u64(a: u64) -> u64 {
                    a
                }
            }

            #[verus_spec]
            fn test_call_cross_module() {
                use inner::copy_u64;
                proof_with!{Ghost(5u64)}
                let ret = copy_u64(10);
                proof!{ assert(ret == 10); }
            }
        })
    => Ok(())
}

// ---- ported: omitting `proof_with!` on a function that declares one ----
//
// The extras a callee is entitled to assume were never supplied, so the call is
// rejected outright rather than verified.

test_verify_one_file! {
    #[test] test_proof_with_missing code!{
        use vstd::prelude::*;

        #[verus_spec(
            with Tracked(b): Tracked<u64>
            requires b == 1,
        )]
        fn test(a: u64) {
        }

        #[verus_verify]
        struct A;

        #[verus_verify]
        impl A {
            #[verus_spec(
                with Tracked(b): Tracked<u64>
                requires b == 1,
            )]
            fn m(&self) {}
        }

        #[verus_spec]
        fn call_free() {
            test(0);
        }

        #[verus_spec]
        fn call_method() {
            let a = A;
            a.m();
        }
    } => Err(e) => {
        assert_eq!(e.errors.len(), 2);
        assert_any_vir_error_msg(e, "this function requires 1 extra tracked/ghost argument(s) via proof_with()");
    }
}

test_verify_one_file! {
    // A qualified path and an alias are recognized as the same function, so
    // neither hides the missing extras.
    #[test] test_proof_with_qualified_path_missing
        MOD_FN_WITH_TRACKED.to_string() + code_str!{
        #[verus_spec]
        fn call_qualified() {
            m::test(0);
        }

        #[verus_spec]
        fn call_aliased() {
            aliased(0);
        }
    } => Err(e) => {
        assert_eq!(e.errors.len(), 2);
        assert_any_vir_error_msg(e, "this function requires 1 extra tracked/ghost argument(s) via proof_with()");
    }
}

test_verify_one_file! {
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
            let r = with_alias(6);
        }
    } => Err(e) => assert_vir_error_msg(e, "this function requires 1 extra tracked/ghost argument(s) via proof_with()")
}

test_verify_one_file! {
    // A user-defined function named `proof_with` is not the builtin marker and
    // must not trigger the call rewrite.
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

// ---- ported: a wrong extra type on a call to an `assume_specification` ----

test_verify_one_file! {
    #[test] test_external_fn_mismatched_extra_type code!{
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
            proof_with!{Tracked(1u32)}
            let ret = negate_bool(true, 1);
        }
    } => Err(e) => assert_rust_error_msg_all(e, "mismatched types")
}

// ---- ported: `with` on a trait method ----
//
// The shim of a trait method is an extra defaulted method of the same trait, so
// a caller reaches it through whatever bound already gives it the method.

// A trait whose method `f` declares a `Ghost` input, and the type that the tests
// below implement it for.
const TRAIT_WITH_GHOST_INPUT: &str = code_str! {
    use vstd::prelude::*;

    #[verus_verify]
    trait X {
        #[verus_spec(ret =>
            with Ghost(g): Ghost<u64>
            requires g < 100,
            ensures ret == a,
        )]
        fn f(&self, a: u64) -> u64;
    }

    #[verus_verify]
    struct S;
};

// A trait whose method `f` declares a `Ghost` input and a `Ghost` output, with
// the identity implementation for `S`.
const TRAIT_WITH_GHOST_OUTPUT: &str = code_str! {
    use vstd::prelude::*;

    #[verus_verify]
    trait X {
        #[verus_spec(ret =>
            with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
            ensures ret == a, g2@ == g,
        )]
        fn f(&self, a: u64) -> u64;
    }

    #[verus_verify]
    struct S;

    #[verus_verify]
    impl X for S {
        #[verus_spec(with Ghost(g): Ghost<u64> -> g2: Ghost<u64>)]
        fn f(&self, a: u64) -> u64 {
            proof!{ g2 = Ghost(g); }
            a
        }
    }
};

// A bodyless trait method with `with` extras: declaring, implementing and
// overriding one. Every case here used to reach an internal compiler panic,
// because a bodyless method's extra *outputs* were dropped on the way into VIR
// while its extra inputs were carried through.
test_verify_one_file! {
    #[test] test_trait_decl_with_ghost_output_verifies TRAIT_WITH_GHOST_OUTPUT.to_string() => Ok(())
}

test_verify_one_file! {
    #[test] test_trait_decl_with_tracked_output_verifies code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Tracked(t): Tracked<u64> -> t2: Tracked<u64>
                ensures ret == a, t2@ == t,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Tracked(t): Tracked<u64> -> t2: Tracked<u64>)]
            fn f(&self, a: u64) -> u64 {
                proof!{ t2 = Tracked(t); }
                a
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_trait_decl_with_several_extras_verifies code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64>, Tracked(t): Tracked<u64>
                    -> g2: Ghost<u64>, t2: Tracked<u64>
                ensures ret == a, g2@ == g, t2@ == t,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64>, Tracked(t): Tracked<u64>
                -> g2: Ghost<u64>, t2: Tracked<u64>)]
            fn f(&self, a: u64) -> u64 {
                proof!{ g2 = Ghost(g); t2 = Tracked(t); }
                a
            }
        }
    } => Ok(())
}

// An extra input named in `requires` rather than `ensures`: the other half of
// the declaration, which never went through the dropped field.
test_verify_one_file! {
    #[test] test_trait_decl_with_extra_input_in_requires code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64>
                requires g > 0,
                ensures ret == a,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn f(&self, a: u64) -> u64 { a }
        }
    } => Ok(())
}

// An extra output assigned in the body but named in no clause: mention and
// assignment are separate code paths, so exercise them independently.
test_verify_one_file! {
    #[test] test_trait_decl_with_output_not_in_any_clause code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
                ensures ret == a,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64> -> g2: Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                proof!{ g2 = Ghost(g); }
                a
            }
        }
    } => Ok(())
}

// ... and named in a clause but never assigned, which is rejected.
test_verify_one_file! {
    #[test] test_trait_impl_with_output_never_assigned code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
                ensures ret == a, g2@ == g,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64> -> g2: Ghost<u64>)]
            fn f(&self, a: u64) -> u64 { a }
        }
    } => Err(e) => assert_vir_error_msg(
        e, "declare_ret_with() variable must be assigned to in the function body")
}

// A default body may declare extras too, and an impl may inherit it.
test_verify_one_file! {
    #[test] test_trait_default_body_with_ghost_output code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
                ensures ret == a, g2@ == g,
            )]
            fn f(&self, a: u64) -> u64 {
                proof!{ g2 = Ghost(g); }
                a
            }
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {}
    } => Ok(())
}

// A trait method's extra *inputs* are usable at a call site; only extra outputs
// are still missing there (see the ignored group test below).
test_verify_one_file! {
    #[test] test_call_trait_method_with_extra_input code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret => with Ghost(g): Ghost<u64> ensures ret == a)]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn f(&self, a: u64) -> u64 { a }
        }

        #[verus_spec]
        fn caller(s: &S) {
            proof_with!{Ghost(3u64)}
            let r = s.f(7);
            proof!{ assert(r == 7); }
        }
    } => Ok(())
}

// A caller may ignore the extra outputs with `=> _`. The extras are then
// existentially quantified rather than projected out of the call's
// destination, which must still leave the callee's ensures about the ordinary
// return value usable.
test_verify_one_file! {
    #[test] test_call_ignoring_extra_outputs TRAIT_WITH_GHOST_OUTPUT.to_string() + code_str!{
        #[verus_spec(ret =>
            with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
            ensures ret == a, g2@ == g,
        )]
        fn freef(a: u64) -> u64 {
            proof!{ g2 = Ghost(g); }
            a
        }

        #[verus_spec]
        fn caller(s: &S) {
            proof_with!{Ghost(3u64) => _}
            let r = s.f(7);
            proof!{ assert(r == 7); }

            proof_with!{Ghost(3u64) => _}
            let r2 = freef(9);
            proof!{ assert(r2 == 9); }
        }

        // ... and may discard the result entirely
        #[verus_spec]
        fn discard(s: &S) {
            proof_with!{Ghost(3u64) => _}
            s.f(7);

            proof_with!{Ghost(3u64) => _}
            freef(9);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_local_trait_group
        // One trait `X` with a `Ghost` input and output serves every case whose
        // shape is not itself the point; each case below is just a caller.
        TRAIT_WITH_GHOST_OUTPUT.to_string() + code_str!{
            // a generic caller passes the extra arguments with its bound
            #[verus_spec]
            fn call_generic<A: X>(x: &A) {
                proof_decl!{ let ghost g2: u64; }
                proof_with!{Ghost(3u64) => Ghost(g2): Ghost<u64>}
                let r = x.f(7);
                proof!{ assert(r == 7); assert(g2 == 3); }
            }

            // a qualified call names the trait
            #[verus_spec]
            fn qualified_call() {
                proof_decl!{ let ghost g2: u64; }
                proof_with!{Ghost(3u64) => Ghost(g2): Ghost<u64>}
                let r = X::f(&S, 7);
                proof!{ assert(r == 7); assert(g2 == 3); }
            }

            // the shim may be reached through a supertrait `Y: X`
            #[verus_verify]
            trait Y: X {}

            #[verus_verify]
            impl Y for S {}

            #[verus_spec]
            fn call_via_subtrait<A: Y>(x: &A) {
                proof_decl!{ let ghost g2: u64; }
                proof_with!{Ghost(3u64) => Ghost(g2): Ghost<u64>}
                let r = x.f(7);
                proof!{ assert(g2 == 3); }
            }

            // the bound is on the impl that declares the type parameter, not on
            // the method
            #[verus_verify]
            struct Wrapper<A>(A);

            #[verus_verify]
            impl<A: X> Wrapper<A> {
                #[verus_spec]
                fn call(&self) {
                    proof_decl!{ let ghost g2: u64; }
                    proof_with!{Ghost(3u64) => Ghost(g2): Ghost<u64>}
                    let r = self.0.f(7);
                    proof!{ assert(g2 == 3); }
                }
            }

            // a bound on one type parameter must not affect a call made through
            // another
            #[verus_verify]
            trait Z {
                #[verus_spec(ret => ensures ret == a)]
                fn g(&self, a: u64) -> u64;
            }

            #[verus_spec(r => ensures r == 7)]
            fn call_other<A: Z, B: X>(z: &A, _x: &B) -> u64 {
                z.g(7)
            }

            // a type can implement `X` by forwarding the extra output of its
            // own field's method
            #[verus_verify]
            struct Fwd<A>(A);

            #[verus_verify]
            impl<A: X> X for Fwd<A> {
                #[verus_spec(with Ghost(g): Ghost<u64> -> g2: Ghost<u64>)]
                fn f(&self, a: u64) -> u64 {
                    proof_decl!{ let ghost inner: u64; }
                    proof_with!{Ghost(g) => Ghost(inner): Ghost<u64>}
                    let r = self.0.f(a);
                    proof!{ g2 = Ghost(inner); }
                    r
                }
            }

            // the shim carries the generic arguments of the bound the method is
            // called through
            #[verus_verify]
            trait Tr<A> {
                #[verus_spec(with Ghost(g): Ghost<u64>)]
                fn m(&self, a: A);
            }

            #[verus_verify]
            impl Tr<u64> for S {
                #[verus_spec(with Ghost(g): Ghost<u64>)]
                fn m(&self, _a: u64) {}
            }

            #[verus_spec]
            fn call_generic_args<A: Tr<u64>>(x: &A) {
                proof_with!{Ghost(1u64)}
                x.m(1u64);
            }

            // the generic callers have to be satisfied by a concrete argument,
            // which only a real call checks
            #[verus_verify]
            fn call_the_generic_callers() {
                call_generic(&S);
                call_generic(&Fwd(S));
                call_via_subtrait(&S);
                call_generic_args(&S);
                let w = Wrapper(S);
                w.call();
            }
        }
        // the shim is declared next to the trait in another module, so an impl
        // reaches it through the same path
        + &in_mod("qualified_path", code_str!{
            use vstd::prelude::*;

            mod m {
                use vstd::prelude::*;

                #[verus_verify]
                pub trait X {
                    #[verus_spec(ret =>
                        with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
                        ensures ret == a, g2@ == g,
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
                    proof!{ g2 = Ghost(g); }
                    a
                }
            }

            #[verus_verify]
            fn call_through_path(s: &S) {
                proof_decl!{ let ghost g2: u64; }
                proof_with!{Ghost(3u64) => Ghost(g2): Ghost<u64>}
                let r = s.f(7);
                proof!{ assert(r == 7); assert(g2 == 3); }
            }
        })
        // several methods can each declare their own extra parameters, next to
        // a method that declares none
        + &in_mod("mixed_methods", code_str!{
            use vstd::prelude::*;

            #[verus_verify]
            trait X {
                #[verus_spec(r =>
                    with Ghost(g): Ghost<int> -> g2: Ghost<int>
                    ensures r == a, g2@ == g + 1,
                )]
                fn ghost_method(&self, a: u64) -> u64;

                #[verus_spec(r =>
                    with Tracked(b): Tracked<u64>
                    requires b == 1,
                    ensures r == 2,
                )]
                fn tracked_method(&self) -> u64;

                #[verus_spec(r => ensures r == 5)]
                fn plain(&self) -> u64;
            }

            #[verus_verify]
            struct S;

            #[verus_verify]
            impl X for S {
                #[verus_spec(with Ghost(g): Ghost<int> -> g2: Ghost<int>)]
                fn ghost_method(&self, a: u64) -> u64 {
                    proof!{ g2 = Ghost(g + 1); }
                    a
                }

                #[verus_spec(with Tracked(b): Tracked<u64>)]
                fn tracked_method(&self) -> u64 {
                    2
                }

                fn plain(&self) -> u64 {
                    5
                }
            }

            // one bound gives a generic caller every shim at once
            #[verus_verify]
            fn call_all<A: X>(x: &A) {
                proof_decl!{ let ghost g2: int; }
                proof_with!{Ghost(3int) => Ghost(g2): Ghost<int>}
                let r = x.ghost_method(7);
                proof_with!{Tracked(1u64)}
                let q = x.tracked_method();
                let p = x.plain();
                proof!{ assert(r == 7); assert(g2 == 4); assert(q == 2); assert(p == 5); }
            }

            #[verus_verify]
            fn test() {
                call_all(&S);
                proof_with!{Tracked(1u64)}
                let r = S.tracked_method();
                proof!{ assert(r == 2); }
            }
        })
        // the shim's signature can name an associated type of the trait
        + &in_mod("associated_type", code_str!{
            use vstd::prelude::*;

            #[verus_verify]
            trait X {
                type Item;

                #[verus_spec(ret =>
                    with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
                    ensures g2@ == g,
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
                    proof!{ g2 = Ghost(g); }
                    a
                }
            }

            #[verus_verify]
            fn call_assoc(s: &S) {
                proof_decl!{ let ghost g2: u64; }
                proof_with!{Ghost(3u64) => Ghost(g2): Ghost<u64>}
                let _r = s.f(7);
                proof!{ assert(g2 == 3); }
            }
        })
    => Ok(())
}

test_verify_one_file! {
    // A call with an argument that violates the declared `requires` fails that
    // precondition; one that omits `proof_with!` is rejected outright.
    #[test] test_trait_with_missing_or_failed_requires
        TRAIT_WITH_GHOST_INPUT.to_string() + code_str!{
        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                a
            }
        }

        #[verus_spec]
        fn call_failed_requires(s: &S) {
            proof_with!{Ghost(300u64)}
            let r = s.f(3); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_trait_with_missing_proof_with
        TRAIT_WITH_GHOST_INPUT.to_string() + code_str!{
        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                a
            }
        }

        #[verus_spec]
        fn call_missing(s: &S) {
            let r = s.f(3);
        }
    } => Err(e) => assert_vir_error_msg(e, "this function requires 1 extra tracked/ghost argument(s) via proof_with()")
}

test_verify_one_file! {
    // rustc checks the extra parameters of the implementation against the trait.
    #[test] test_trait_with_mismatched_in_impl
        TRAIT_WITH_GHOST_INPUT.to_string() + code_str!{
        #[verus_verify]
        impl X for S {
            #[verus_spec(with Tracked(g): Tracked<u64>)]
            fn f(&self, a: u64) -> u64 {
                a
            }
        }
    } => Err(e) => assert_rust_error_msg_any(e, "mismatched types")
}

// Extras are discovered by scanning a callee's body, and bodies are lowered in
// item order, so a caller defined first must not see a callee with no extras.

test_verify_one_file! {
    #[test] test_call_before_callee_definition code!{
        use vstd::prelude::*;

        #[verus_spec(r =>
            ensures r == 7,
        )]
        fn caller() -> u64 {
            proof_with!{Ghost(1u64)}
            callee(7)
        }

        #[verus_spec(ret =>
            with Ghost(g): Ghost<u64>
            requires g > 0,
            ensures ret == a,
        )]
        fn callee(a: u64) -> u64 {
            a
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_missing_proof_with_before_callee_definition code!{
        use vstd::prelude::*;

        #[verus_spec]
        fn caller() -> u64 {
            callee(7)
        }

        #[verus_spec(ret =>
            with Ghost(g): Ghost<u64>
            requires g > 0,
            ensures ret == a,
        )]
        fn callee(a: u64) -> u64 {
            a
        }
    } => Err(e) => assert_vir_error_msg(e, "this function requires 1 extra tracked/ghost argument(s) via proof_with()")
}

test_verify_one_file! {
    #[test] test_impl_method_call_before_definition code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct S;

        #[verus_spec(r =>
            ensures r == 3,
        )]
        fn caller(s: &S) -> u64 {
            proof_with!{Ghost(1u64)}
            s.m(3)
        }

        #[verus_verify]
        impl S {
            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64>
                requires g > 0,
                ensures ret == a,
            )]
            fn m(&self, a: u64) -> u64 {
                a
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // A `with` clause naming a lifetime gives the proxy a late-bound lifetime the
    // external function does not have. That is a signature mismatch, and must be
    // reported as one rather than tripping an assertion while equalizing substs.
    #[test] test_assume_specification_extra_lifetime code!{
        use vstd::prelude::*;

        #[verifier::external]
        fn ext(x: &u64) -> u64 {
            *x
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with Tracked(t): Tracked<&'b u64>
            ensures ret == *x,
        )]
        fn ext_spec<'a, 'b>(x: &'a u64) -> u64 {
            ext(x)
        }
    } => Err(e) => assert_vir_error_msg(e, "assume_specification requires function type signature to match")
}

test_verify_one_file! {
    // The same rule as for extra inputs, on the extra-output path: an elided
    // lifetime here used to reach `lower_ty` unguarded and crash rustc.
    #[test] test_declare_ret_with_elided_lifetime code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct A { val: u64 }

        #[verus_spec]
        fn callee<'a>(x: &'a mut A) -> u64 {
            let mut out: Tracked<&mut A> = declare_ret_with();
            proof!{ out = Tracked::assume_new(); }
            1
        }
    } => Err(e) => assert_vir_error_msg(e, "the type of a `with` parameter must name its lifetimes explicitly")
}

test_verify_one_file! {
    // A callee that genuinely returns a 2-tuple has the same destination shape as
    // a `proof_with_ret` call site, so inferring the marker from the shape sent
    // this call down the projection path and lost the callee's postcondition.
    #[test] test_tuple_returning_callee_with_extra_out code!{
        use vstd::prelude::*;

        #[verus_spec(ret => with -> out1: Tracked<u8>,
            ensures ret.0 == 7u64, ret.1 == 8u64,
        )]
        fn callee(a: u64) -> (u64, u64) {
            proof!{ out1 = Tracked(42u8); }
            (7, 8)
        }

        #[verus_spec]
        fn call_test() {
            let pair = callee(5);
            proof!{ assert(pair.0 == 7u64); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // An impl method that declares no extras never registers, so a check driven
    // from the registry's keys could not see it. Extra inputs used to be caught
    // downstream by the mode checker; extra outputs were caught nowhere.
    #[test] test_impl_omits_with_clause_inputs code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait T {
            #[verus_spec(with tracked extra: Tracked<u8>)]
            fn f(&self, a: u64) -> u64;
        }

        struct S;

        #[verus_verify]
        impl T for S {
            #[verus_spec]
            fn f(&self, a: u64) -> u64 { 1 }
        }
    } => Err(e) => assert_any_vir_error_msg(e, "this method declares 0 extra ghost/tracked argument(s) but the trait method declares 1")
}

test_verify_one_file! {
    #[test] test_impl_omits_with_clause_outputs code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait T {
            #[verus_spec(with -> out1: Tracked<u8>)]
            fn f(&self, a: u64) -> u64;
        }

        struct S;

        #[verus_verify]
        impl T for S {
            #[verus_spec]
            fn f(&self, a: u64) -> u64 { 1 }
        }
    } => Err(e) => assert_any_vir_error_msg(e, "this method declares 0 extra ghost/tracked return value(s) but the trait method declares 1")
}

test_verify_one_file! {
    // A `proof_with` call nested inside another's argument sets the same pending
    // slot; the outer call's extras must survive lowering its arguments.
    #[test] test_nested_proof_with_in_argument code!{
        use vstd::prelude::*;

        #[verus_spec(with Ghost(g): Ghost<u64>)]
        fn inner(a: u64) -> u64 { a }

        #[verus_spec(with Ghost(g): Ghost<u64>)]
        fn outer(a: u64) -> u64 { a }

        #[verus_spec]
        fn call_test() {
            proof_decl!{ let ghost g1: u64 = 1; let ghost g2: u64 = 2; }
            proof_with!{Ghost(g1)}
            let r = outer({
                proof_with!{Ghost(g2)}
                let t = inner(5);
                t
            });
        }
    } => Ok(())
}
