#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// --------------------------------------------------------------------------
// Extra ghost/tracked inputs on a free function or an inherent method.
// --------------------------------------------------------------------------
test_verify_one_file! {
    #[test] test_attribute_form_group code!{
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

            // a call inside a closure body, a separate body in the same owner,
            // is rewritten too
            mod closure_call {
                use vstd::prelude::*;

                #[verus_spec(ret =>
                    with Tracked(t): Tracked<u8>
                    requires t == a,
                    ensures ret == a,
                )]
                fn f(a: u8) -> u8 {
                    a
                }

                #[verus_verify]
                fn call_in_closure() {
                    let c = || -> u8 {
                        proof_with!{Tracked(3u8)}
                        let y = f(3);
                        y
                    };
                    let _v = c();
                }
            }
    } => Ok(())
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
test_verify_one_file! {
    // rustc checks the extra arguments of a rewritten call; a wrong extra type
    // is a `mismatched types` error in every form.
    // The extras are ordinary Rust parameters, so a value of the wrong mode or
    // type is a type error at the call.
    #[test] test_mismatched_extra_type_rejected code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<u64>)]
        fn f(a: u64) {}

        #[verus_spec]
        fn c() {
            proof_with!{Ghost(1u64)}
            f(0);
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
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
// --------------------------------------------------------------------------
// Lifetimes and borrows on the extras.
// The extras become real Rust parameters, so rustc checks them like any
// other argument. What rustc cannot check is a lifetime the caller never
// wrote, which is rejected in the clause instead.
// --------------------------------------------------------------------------
test_verify_one_file! {
    #[test] test_with_lifetime_group code!{
            use vstd::prelude::*;

            // the shim's `'a` is instantiated to a region contained in both `'a`
            // and `'b`, and the callee only uses the extra for that region
            #[verus_spec(with Tracked(c): Tracked<&'a u64>)]
            fn borrows<'a>(a: &'a u64) -> u64 {
                1
            }

            #[verus_spec]
            fn call_borrows<'a, 'b>(a: &'a u64, c: Tracked<&'b u64>) -> u64 {
                proof_with!{c}
                borrows(a)
            }

            // `'static` is a written lifetime, so it is accepted
            #[verus_spec(with Tracked(c): Tracked<&'static u64>)]
            fn statics<'a>(a: &'a u64) -> u64 {
                1
            }

            mod ghost_extra {
                use vstd::prelude::*;

                #[verus_spec(with Ghost(g): Ghost<&'a u64>)]
                fn ghosts<'a>(a: &'a u64) -> u64 {
                    1
                }

                #[verus_spec]
                fn call_ghosts<'a, 'b>(a: &'a u64, c: Ghost<&'b u64>) -> u64 {
                    proof_with!{c}
                    ghosts(a)
                }
            }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_with_turbofish_lifetime verus_code!{
        use vstd::prelude::*;
        fn test<'a>(a: &'a u64) -> u64
        {
            let c = declare_with::<Tracked<&'a u64>>();
            1
        }
    } => Ok(())
}
// A lifetime the caller did not write is resolved inside the callee instead of
// being taken from the call site, so an extra declared with one could outlive
// what the caller actually granted. Every spelling of an omitted lifetime is
// rejected where it is written.

test_verify_one_file! {
    #[test] test_with_extra_must_name_lifetimes code!{
        mod elided_reference {
            use vstd::prelude::*;

            #[verus_spec(with Tracked(c): Tracked<&u64>)]
            fn test<'a>(a: &'a u64) -> u64 {
                1
            }
        }

        mod anonymous {
            use vstd::prelude::*;

            #[verus_spec(with Tracked(c): Tracked<&'_ u64>)]
            fn test<'a>(a: &'a u64) -> u64 {
                1
            }
        }

        mod elided_in_path {
            use vstd::prelude::*;

            #[verus_verify]
            struct Perm<'x> { p: &'x u64 }

            #[verus_spec(with Tracked(c): Tracked<Perm>)]
            fn test<'a>(a: &'a u64) -> u64 {
                1
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "must name its lifetimes explicitly")
}

// A `with` clause writes the type as a turbofish rather than a let annotation,
// so the same rule has to reach through it.
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
test_verify_one_file! {
    // The extra `Tracked`/`Ghost` input keeps its lifetime obligations: a
    // shorter-lived reference passed where a longer-lived one is declared is a
    // `lifetime may not live long enough` error.
    #[test] test_proof_with_lifetime_mismatch_both_modes code!{
        // through a `Tracked` input
        mod tracked {
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
        }

        // through a `Ghost` input
        mod ghost {
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
        }
    } => Err(e) => assert_rust_error_msgs(
        e,
        &["lifetime may not live long enough", "lifetime may not live long enough"],
    )
}
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
// --------------------------------------------------------------------------
// The Rust signature of an annotated function is unchanged.
// --------------------------------------------------------------------------
test_verify_one_file! {
    #[test] test_with_fn_pointer_rejected_in_verified_code code!{
        use vstd::prelude::*;

        #[verus_spec(with Ghost(g): Ghost<u32>)]
        fn extra_in(a: u64) -> u64 {
            a
        }

        #[verus_spec]
        fn verified_fp() {
            let f: fn(u64) -> u64 = extra_in;
            let r = f(1);
        }
    } => Err(e) => assert_vir_error_msg(e, "casting a pointer")
}
// --------------------------------------------------------------------------
// Extra outputs, folded into the return value.
// --------------------------------------------------------------------------
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
// --------------------------------------------------------------------------
// Control flow in a callee that has extra outputs.
// Folding the extras into the return value could silently change what
// happens at an early exit, so every path out is exercised.
// --------------------------------------------------------------------------
test_verify_one_file! {
    #[test] test_extra_out_control_flow_group code!{
        mod return_after_assign {
            use vstd::prelude::*;

            #[verus_spec(with -> z: Ghost<u32>, ensures z@ == 1)]
            fn f(x: u64) -> u64 {
                proof!{ z = Ghost(1u32); }
                if x > 0 {
                    return 5;
                }
                x
            }

            #[verus_spec]
            fn caller() {
                proof_decl!{ let ghost zz: u32; }
                proof_with!{ => Ghost(zz): Ghost<u32>}
                let r = f(7);
                proof!{ assert(zz == 1); }
            }
        }

        // two outputs, each assigned on every path out
        mod two_outputs_multiple_returns {
            use vstd::prelude::*;

            #[verus_spec(with -> y: Ghost<u32>, z: Tracked<u64>,
                         ensures y@ == 1, z@ == 2)]
            fn f(x: u64) -> u64 {
                if x > 0 {
                    proof!{ y = Ghost(1u32); z = Tracked(2u64); }
                    return 5;
                }
                proof!{ y = Ghost(1u32); z = Tracked(2u64); }
                x
            }

            #[verus_spec]
            fn caller() {
                proof_decl!{ let ghost yy: u32; let tracked zz: u64; }
                proof_with!{ => (Ghost(yy), Tracked(zz)): (Ghost<u32>, Tracked<u64>)}
                let r = f(7);
                proof!{ assert(yy == 1); assert(zz == 2); }
            }
        }

        // a unit-returning callee, whose extras are the whole return value
        mod unit_callee {
            use vstd::prelude::*;

            #[verus_spec(with -> z: Ghost<u32>, ensures z@ == 1)]
            fn f(x: u64) {
                proof!{ z = Ghost(1u32); }
                if x > 0 {
                    return;
                }
            }

            #[verus_spec]
            fn caller() {
                proof_decl!{ let ghost zz: u32; }
                proof_with!{ => Ghost(zz): Ghost<u32>}
                f(7);
                proof!{ assert(zz == 1); }
            }
        }

        // the caller may discard the extra outputs
        mod discarded_at_call {
            use vstd::prelude::*;

            #[verus_spec(ret => with -> z: Ghost<u32>, ensures z@ == 1, ret == 5)]
            fn f(x: u64) -> u64 {
                proof!{ z = Ghost(1u32); }
                if x > 0 {
                    return 5;
                }
                5
            }

            #[verus_spec]
            fn caller() {
                proof_with!{ => _}
                let r = f(7);
                proof!{ assert(r == 5); }
            }
        }

        // a callee with extra inputs only returns early without folding anything
        mod extra_in_only {
            use vstd::prelude::*;

            #[verus_spec(ret => with Tracked(t): Tracked<u64>, requires t == 3, ensures ret == t)]
            fn f(x: u64) -> u64 {
                if x > 0 {
                    return 3;
                }
                proof!{ assert(t == 3); }
                3
            }

            #[verus_spec]
            fn caller() {
                proof_with!{Tracked(3u64)}
                let r = f(7);
                proof!{ assert(r == 3); }
            }
        }
    } => Ok(())
}
test_verify_one_file! {
    #[test] test_extra_out_early_return_before_assign code!{
        use vstd::prelude::*;

        #[verus_spec(with -> z: Ghost<u32>, ensures z@ == 1)]
        fn f(x: u64) -> u64 {
            if x > 0 {
                return 5; // FAILS
            }
            proof!{ z = Ghost(1u32); }
            x
        }
    } => Err(err) => assert_one_fails(err)
}
test_verify_one_file! {
    #[test] test_extra_out_assigned_in_one_branch_only code!{
        use vstd::prelude::*;

        #[verus_spec(with -> z: Ghost<u32>, ensures z@ == 1)] // FAILS
        fn f(x: u64) -> u64 {
            if x > 0 {
                proof!{ z = Ghost(1u32); }
            }
            x
        }
    } => Err(err) => assert_one_fails(err)
}
test_verify_one_file! {
    #[test] #[ignore] test_extra_out_unassigned_on_return_path_is_unsound code!{
        use vstd::prelude::*;

        verus!{
            struct Pos { v: u64 }

            impl Pos {
                #[verifier::type_invariant]
                spec fn inv(&self) -> bool { self.v > 0 }
            }

            proof fn mk() -> (tracked r: Pos) ensures r.v == 1 { Pos { v: 1 } }
        }

        #[verus_spec(with -> z: Tracked<Pos>)]
        fn f(x: u64) -> u64 {
            if x > 0 {
                return 5; // FAILS
            }
            proof!{ z = Tracked(mk()); }
            x
        }

        #[verus_spec]
        fn caller() {
            proof_decl!{ let tracked zz: Pos; }
            proof_with!{ => Tracked(zz): Tracked<Pos>}
            let r = f(7);
            proof!{ use_type_invariant(&zz); assert(zz.v > 0); }
        }
    } => Err(err) => assert_one_fails(err)
}
// --------------------------------------------------------------------------
// The marker is only a marker.
// Where `proof_with!` may be written, and how it is parsed, is covered by
// the syntax tests in syntax_attr.rs; these are the checks that belong to
// the feature itself.
// --------------------------------------------------------------------------
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
// --------------------------------------------------------------------------
// Shims: the hand-written escape hatch, and the reserved shim name.
// --------------------------------------------------------------------------
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
// --------------------------------------------------------------------------
// Trait methods.
// --------------------------------------------------------------------------
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

            // the generic callers have to be satisfied by a concrete argument,
            // which only a real call checks
            #[verus_verify]
            fn call_the_generic_callers() {
                call_generic(&S);
                call_generic(&Fwd(S));
            }

            // several methods can each declare their own extra parameters, next
            // to a method that declares none
            mod mixed_methods {
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

            }
        }
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
// --------------------------------------------------------------------------
// The shim trait is in scope only at the call being rewritten.
// --------------------------------------------------------------------------
test_verify_one_file! {
    #[test] test_trait_shim_scope_is_per_call code!{
        use vstd::prelude::*;

        #[verus_verify]
        pub trait X {
            #[verus_spec(ret => with Ghost(g): Ghost<u64> ensures ret == a)]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        pub trait Y {
            #[verus_spec(ret => ensures ret == 8)]
            fn f(&self, a: u64) -> u64;

            #[verus_spec(ret => with Ghost(g): Ghost<u64> ensures ret == 9)]
            fn h(&self, a: u64) -> u64;
        }

        #[verus_verify]
        pub struct S;

        #[verus_verify]
        pub struct T;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn f(&self, a: u64) -> u64 { a }
        }

        #[verus_verify]
        impl Y for T {
            #[verus_spec(ret => ensures ret == 8)]
            fn f(&self, a: u64) -> u64 { 8 }

            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn h(&self, a: u64) -> u64 { 9 }
        }

        #[verus_spec]
        fn caller(s: &S, t: &T) {
            proof_with!{Ghost(3u64)}
            let r = s.f(7);
            let plain = t.f(7);
            proof_with!{Ghost(3u64)}
            let r2 = t.h(7);
            proof!{
                assert(r == 7);
                assert(plain == 8);
                assert(r2 == 9);
            }
        }
    } => Ok(())
}
test_verify_one_file! {
    #[test] test_trait_shim_not_in_scope_for_neighbouring_call code!{
        use vstd::prelude::*;

        mod defs {
            use vstd::prelude::*;

            #[verus_verify]
            pub trait X {
                #[verus_spec(ret => with Ghost(g): Ghost<u64> ensures ret == a)]
                fn f(&self, a: u64) -> u64;
            }

            #[verus_verify]
            pub struct S;

            #[verus_verify]
            impl X for S {
                #[verus_spec(with Ghost(g): Ghost<u64>)]
                fn f(&self, a: u64) -> u64 { a }
            }
        }

        use defs::{S, X};

        #[verus_spec]
        fn caller(s: &S) {
            proof_with!{Ghost(3u64)}
            let r = s.f(7);
            let bad = s._VERUS_WITH_f(8, Ghost::assume_new());
        }
    } => Err(e) => assert!(
        e.errors.iter().any(|d| d.message.contains("no method named `_VERUS_WITH_f`"))
    )
}
test_verify_one_file! {
    #[test] test_trait_shim_through_generic_bound code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret => with Ghost(g): Ghost<u64> ensures ret == a)]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_spec]
        fn caller<T: X>(t: &T) {
            proof_with!{Ghost(3u64)}
            let r = t.f(7);
            proof!{ assert(r == 7); }
        }

        #[verus_spec]
        fn caller_wrong_type<T: X>(t: &T) {
            proof_with!{Ghost(3u32)}
            let r = t.f(7);
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
}
test_verify_one_file! {
    #[test] test_trait_declaring_reserved_shim_name_is_ambiguous code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret => with Ghost(g): Ghost<u64> ensures ret == a)]
            fn f(&self, a: u64) -> u64;

            #[verus_spec]
            #[allow(non_snake_case)]
            fn _VERUS_WITH_f(&self, a: u64, g: Ghost<u64>) -> u64 { 1 }
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
    } => Err(e) => assert_rust_error_msg(e, "multiple applicable items in scope")
}
// --------------------------------------------------------------------------
// External functions: a `with` clause on an `assume_specification`.
// --------------------------------------------------------------------------
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
test_verify_one_file! {
    #[test] test_external_fn_spec_extra_out_still_needs_assume code!{
        use vstd::prelude::*;

        #[verifier::external]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with Tracked(extra): Tracked<u8> -> z: Tracked<u8>
            requires x == extra,
            ensures ret == !b, z@ == extra,
        )]
        fn negate_bool_spec(b: bool, x: u8) -> bool {
            negate_bool(b, x)
        }
    } => Err(e) => assert_vir_error_msg(
        e, "declare_ret_with() variable must be assigned to in the function body")
}
// --------------------------------------------------------------------------
// External traits: a `with` clause on an `external_trait_specification`.
// --------------------------------------------------------------------------
test_verify_one_file! {
    #[test] test_external_trait_with_call code!{
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
                requires g == 1,
                ensures r == a,
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_spec]
        fn caller<S: T>(s: &S) {
            proof_with!{Ghost(1u64)}
            let r = s.f(2);
            proof!{ assert(r == 2); }
        }
    } => Ok(())
}
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
// --------------------------------------------------------------------------
// Paths, modules, and definition order.
// --------------------------------------------------------------------------
test_verify_one_file! {
    #[test] test_paths_and_aliases_group code!{
        // a qualified path and a module-item alias both reach the shim
        mod qualified_paths {
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
                proof_with!{Tracked(1u64)}
                m::test(0);
            }

            #[verus_spec]
            fn call_aliased() {
                proof_with!{Tracked(1u64)}
                aliased(0);
            }
        }

        // a function defined in another module is reached from the call site
        mod cross_module {
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
        }
    } => Ok(())
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
// --------------------------------------------------------------------------
// A `with` clause written inside the `verus!` macro.
// --------------------------------------------------------------------------
const ASSUME_SPEC_NEGATE_BOOL: &str = verus_code_str! {
    use vstd::prelude::*;

    #[verifier::external]
    fn negate_bool(b: bool, _x: u8) -> bool {
        !b
    }

    assume_specification[negate_bool](b: bool, x: u8) -> (ret: bool)
        with Tracked(extra): Tracked<u8>
        requires x == extra,
        ensures ret == !b,
    ;
};
test_verify_one_file! {
    #[test] test_verus_syntax_group
        verus_code_str!{
            use vstd::prelude::*;

            // a free function with `with` inputs, in `verus!` syntax
            fn free_fn(a: u64) -> (r: u64)
                with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32>
                requires a == 0, b == 1, c == 2,
                ensures r == a,
            {
                a
            }

            fn call_free() {
                proof_with!{Tracked(1u64), Ghost(2u32)}
                let r = free_fn(0);
                assert(r == 0);
            }

            // an extra output, assigned by name in the callee
            fn out_fn(a: u64) -> (r: u64)
                with Ghost(c): Ghost<u32> -> d: Ghost<u32>
                requires c == 2,
                ensures r == a, d@ == c,
            {
                proof!{ d = Ghost(c); }
                a
            }

            fn call_out() {
                proof_decl!{ let ghost d: u32; }
                proof_with!{Ghost(2u32) => Ghost(d): Ghost<u32>}
                let r = out_fn(7);
                assert(r == 7 && d == 2);
            }

            // `with` on an `assume_specification` with an extra output
            #[verifier::external]
            fn ext_id(x: u64) -> u64 {
                x
            }

            assume_specification[ext_id](x: u64) -> (ret: u64)
                with Ghost(c): Ghost<u32> -> d: Ghost<u32>
                requires c == 2,
                ensures ret == x, d@ == c,
            ;

            fn call_ext_id() {
                proof_decl!{ let ghost d: u32; }
                proof_with!{Ghost(2u32) => Ghost(d): Ghost<u32>}
                let r = ext_id(7);
                assert(r == 7 && d == 2);
            }

            // `with` on an inherent method
            struct S;

            impl S {
                fn inherent(&self, a: u64) -> (r: u64)
                    with Ghost(g): Ghost<int>
                    requires g == 1,
                    ensures r == a,
                {
                    a
                }
            }

            fn call_inherent(s: S) {
                proof_with!{Ghost(1int)}
                let r = s.inherent(4);
                assert(r == 4);
            }
        }.to_string()
        // `with` on an `assume_specification` with an extra `Tracked` input
        + ASSUME_SPEC_NEGATE_BOOL
        + verus_code_str!{
            fn call_negate() {
                proof_with!{Tracked(3u8)}
                let r = negate_bool(true, 3);
                assert(r == false);
            }
        }
    => Ok(())
}
test_verify_one_file! {
    // The extra argument is needed, and a wrong one fails the callee's precondition.
    #[test] test_with_inside_verus_macro_fails verus_code!{
        use vstd::prelude::*;

        fn test(a: u64)
            with Tracked(b): Tracked<u64>
            requires b == 1,
        {
        }

        fn call_wrong() {
            proof_with!{Tracked(2u64)}
            test(0); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}
test_verify_one_file! {
    // Omitting `proof_with!` is rejected before verification, as it is in attribute form.
    #[test] test_with_inside_verus_macro_missing_marker verus_code!{
        use vstd::prelude::*;

        fn test(a: u64)
            with Tracked(b): Tracked<u64>
            requires b == 1,
        {
        }

        fn call_missing() {
            test(0);
        }
    } => Err(e) => assert_vir_error_msg(e, "this function requires 1 extra tracked/ghost argument(s) via proof_with()")
}
test_verify_one_file! {
    #[test] test_with_on_assume_specification_fails_precondition
        ASSUME_SPEC_NEGATE_BOOL.to_string() + verus_code_str!{
        fn call_negate() {
            proof_with!{Tracked(4u8)}
            let r = negate_bool(true, 3); // FAILS
            assert(r == false);
        }
    } => Err(e) => assert_one_fails(e)
}
