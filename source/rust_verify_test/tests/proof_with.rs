#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Tests for `#[verus_spec(with ..)]`: extra ghost/tracked inputs and outputs.
//
// A call site written as `proof_with!{..} f(..)` is redirected to the verified
// counterpart of `f` on the lowered HIR, before type checking, so that rustc
// type checks, borrow checks and lifetime checks the extra arguments.
//
// Independent positive cases are grouped into a single `=> Ok(())` test, one
// case per module so that names do not clash and a failure points at the case;
// failing cases are kept separate so each keeps its own asserted diagnostic.

// Wrap the source of one case in a named module, keeping the cases of a grouped
// test independent.
fn in_mod(name: &str, body: &str) -> String {
    format!("mod {name} {{\n{body}\n}}\n")
}

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
    => Ok(())
}

test_verify_one_file! {
    // A wrong extra argument fails the precondition, and omitting `proof_with!`
    // reaches the stub with `requires(false)`.
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

        #[verus_spec]
        fn call_missing() {
            test(0); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
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
    // rustc checks the extra arguments of a redirected call; a wrong extra type
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
        // a wrong extra type on a call redirected to an `assume_specification`
        + EXTERNAL_FN_NEGATE_BOOL
        + code_str!{
            #[verus_spec]
            fn call_external() {
                proof_with!{Tracked(1u32)}
                let ret = negate_bool(true, 1);
            }
        }
    => Err(e) => {
        // one error per case, so no case can stop being rejected unnoticed
        assert_eq!(e.errors.len(), 4);
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
    #[test] test_proof_with_lifetime_mismatch
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

// ---- extra ghost/tracked outputs ----

test_verify_one_file! {
    #[test] test_extra_outputs_group
        code_str!{
            use vstd::prelude::*;

            // one extra Ghost output, produced with `proof_with!{|= ..}`, bound
            // at the call site or ignored with `=> _`
            #[verus_spec(ret =>
                with -> z: Ghost<u32>
                ensures ret == 1u64, z@ == 2u32,
            )]
            fn one_output() -> u64 {
                proof_with!{|= Ghost(2u32)}
                1
            }

            #[verus_spec]
            fn call_bind() {
                proof_with!{=> Ghost(z)}
                let r = one_output();
                proof!{ assert(r == 1); assert(z == 2); }
            }

            #[verus_spec]
            fn call_ignore() {
                proof_with!{=> _}
                let _ = one_output();
            }

            // several extra outputs, produced and bound as a tuple
            #[verus_spec(ret =>
                with -> y: Ghost<u8>, z: Ghost<u32>
                ensures ret == 1u64, y@ == 3u8, z@ == 2u32,
            )]
            fn many_outputs() -> u64 {
                proof_with!{|= (Ghost(3u8), Ghost(2u32))}
                1
            }

            #[verus_spec]
            fn call_many() {
                proof_with!{=> (Ghost(y), Ghost(z))}
                let r = many_outputs();
                proof!{ assert(r == 1); assert(y == 3); assert(z == 2); }
            }

            // extra inputs (including a `Tracked` mutable reference) and an
            // output together
            #[verus_spec(ret =>
                with Tracked(y): Tracked<&mut int>, Ghost(w): Ghost<u32> -> z: Ghost<u32>
                requires x < 100, *old(y) < 100,
                ensures *final(y) == x, ret == x, z@ == x,
            )]
            fn inout(x: u32) -> u32 {
                proof!{
                    *y = x as int;
                }
                proof_with!{|= Ghost(x)}
                x
            }

            #[verus_spec]
            fn call_inout() {
                proof_decl!{
                    let tracked mut y = 0int;
                }
                proof_with!{Tracked(&mut y), Ghost(0u32) => Ghost(z)}
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
            proof_with!{|= Ghost(3u32)}
            1
        }
    } => Err(e) => assert_one_fails(e)
}

// ---- calls through a path or an alias resolve to the same verified function ----

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
        // a qualified path and a module-item alias both reach the counterpart
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

test_verify_one_file! {
    // The same call without `proof_with!` reaches the unverified stub, both
    // through the qualified path and through the alias.
    #[test] test_proof_with_qualified_path_missing
        MOD_FN_WITH_TRACKED.to_string() + code_str!{
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

// An external function and its `assume_specification`, which gives it an extra
// `Tracked` input constrained to equal its `x` argument.
const EXTERNAL_FN_NEGATE_BOOL: &str = code_str! {
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
};

test_verify_one_file! {
    #[test] test_external_fn_group
        // an `assume_specification` with an extra `Tracked` input
        in_mod("input_only", &(EXTERNAL_FN_NEGATE_BOOL.to_string() + code_str!{
            #[verus_spec]
            fn call_external() {
                proof_with!{Tracked(1u8)}
                let ret = negate_bool(true, 1);
                proof!{ assert(!ret); }
            }
        }))
        // an `assume_specification` that also produces an extra `Ghost` output
        + &in_mod("extra_output", code_str!{
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
                proof!{ assert(!ret); assert(z == 1u8); }
            }
        })
    => Ok(())
}

test_verify_one_file! {
    // Without `proof_with!`, the call goes to the `assume_specification`, whose
    // precondition is `false`; with the wrong extra argument, its own
    // precondition fails.
    #[test] test_external_fn_missing_or_failed_requires
        EXTERNAL_FN_NEGATE_BOOL.to_string() + code_str!{
        #[verus_spec]
        fn call_missing() {
            let ret = negate_bool(true, 1); // FAILS
        }

        #[verus_spec]
        fn call_wrong_arg() {
            proof_with!{Tracked(99u8)}
            let ret = negate_bool(true, 1); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
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
    #[test] test_local_trait_group
        // One trait `X` with a `Ghost` input and output serves every case whose
        // shape is not itself the point; each case below is just a caller.
        TRAIT_WITH_GHOST_OUTPUT.to_string() + code_str!{
            // a generic caller passes the extra arguments with its bound; the
            // counterpart is declared by a companion supertrait
            #[verus_spec]
            fn call_generic<A: X>(x: &A) {
                proof_with!{Ghost(3u64) => Ghost(g2)}
                let r = x.f(7);
                proof!{ assert(r == 7); assert(g2 == 3); }
            }

            // a qualified call names the trait, which the rewrite replaces with
            // the companion trait that declares the counterpart
            #[verus_spec]
            fn qualified_call() {
                proof_with!{Ghost(3u64) => Ghost(g2)}
                let r = X::f(&S, 7);
                proof!{ assert(r == 7); assert(g2 == 3); }
            }

            // the counterpart trait may be reached through a supertrait `Y: X`
            #[verus_verify]
            trait Y: X {}

            #[verus_verify]
            impl Y for S {}

            #[verus_spec]
            fn call_via_subtrait<A: Y>(x: &A) {
                proof_with!{Ghost(3u64) => Ghost(g2)}
                let r = x.f(7);
                proof!{ assert(g2 == 3); }
            }

            // the companion bound is added to the item that declares the type
            // parameter, which is the impl here, not the method
            #[verus_verify]
            struct Wrapper<A>(A);

            #[verus_verify]
            impl<A: X> Wrapper<A> {
                #[verus_spec]
                fn call(&self) {
                    proof_with!{Ghost(3u64) => Ghost(g2)}
                    let r = self.0.f(7);
                    proof!{ assert(g2 == 3); }
                }
            }

            // a bound on one type parameter must not draw the companion bound
            // onto a call made through another
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
                    proof_with!{Ghost(g) => Ghost(inner)}
                    let r = self.0.f(a);
                    proof_with!{|= Ghost(inner)}
                    r
                }
            }


            // the companion bound the rewrite adds to a generic caller has to be
            // satisfied by a concrete argument, which only a real call checks
            #[verus_verify]
            fn call_the_generic_callers() {
                call_generic(&S);
                call_generic(&Fwd(S));
                call_via_subtrait(&S);
                let w = Wrapper(S);
                w.call();
            }
        }
        // the companion trait is declared next to the trait in another module,
        // so an impl reaches it through the same path
        + &in_mod("qualified_path", code_str!{
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

            // the call site names the companion through the trait it imported
            #[verus_verify]
            fn call_through_path(s: &S) {
                proof_with!{Ghost(3u64) => Ghost(g2)}
                let r = s.f(7);
                proof!{ assert(r == 7); assert(g2 == 3); }
            }
        })
        // several methods can each declare their own extra parameters, next to
        // a method that declares none and keeps its place in the trait
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
                    proof_decl!{ let ghost gg: int = g + 1; }
                    proof_with!{|= Ghost(gg)}
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

            // one bound gives a generic caller both counterparts at once
            #[verus_verify]
            fn call_all<A: X>(x: &A) {
                proof_with!{Ghost(3int) => Ghost(g2)}
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
        // the counterpart's signature can name an associated type of the trait
        + &in_mod("associated_type", code_str!{
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

            // the call site resolves the associated type of the counterpart
            #[verus_verify]
            fn call_assoc(s: &S) {
                proof_with!{Ghost(3u64) => Ghost(g2)}
                let _r = s.f(7);
                proof!{ assert(g2 == 3); }
            }
        })
    => Ok(())
}

test_verify_one_file! {
    // A plain call goes to the stub, which inherits `requires(false)` from the
    // trait declaration; a call with an argument that violates the declared
    // `requires` fails that precondition instead.
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
        fn call_missing(s: &S) {
            let r = s.f(3); // FAILS
        }

        #[verus_spec]
        fn call_failed_requires(s: &S) {
            proof_with!{Ghost(300u64)}
            let r = s.f(3); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

// A trait whose method `f` declares a `Ghost` input, and the type that the tests
// below implement it for.
const TRAIT_WITH_GHOST_INPUT: &str = code_str! {
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
};

// A trait whose method `f` declares a `Ghost` input and a `Ghost` output, with
// the identity implementation for `S`.
const TRAIT_WITH_GHOST_OUTPUT: &str = code_str! {
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
};

test_verify_one_file! {
    // An implementation that does not declare the `with` clause of the trait
    // implements no counterpart, so it cannot be called with extra arguments.
    #[test] test_trait_with_missing_in_impl
        TRAIT_WITH_GHOST_INPUT.to_string() + code_str!{
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
    #[test] test_trait_with_mismatched_in_impl
        TRAIT_WITH_GHOST_INPUT.to_string() + code_str!{
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
            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn g(&self) -> u64;

            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn f(&self) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl T for S {
            // `g` omits the `with` clause, so `_VERUS_VERIFIED_g` is left
            // unimplemented even though `f` makes the companion impl exist.
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
        proof_with!{Ghost(3int) => Ghost(g2)}
        let r = S.f(7);
        proof!{ assert(r == 7); assert(g2 == 4); }
    }
};

test_verify_one_file! {
    #[test] test_external_trait_group
        // The external trait `T`, its proxy `ExT`, and one impl serve the cases
        // whose shape is not the point; each is just a caller.
        EXTERNAL_TRAIT_DECL.to_string() + EXTERNAL_TRAIT + code_str!{
            // a method call reaches the counterpart of the external trait method
            #[verus_verify]
            fn call_method() {
                proof_with!{Ghost(3int) => Ghost(g2)}
                let r = S.f(7);
                proof!{ assert(r == 7); assert(g2 == 4); }
            }

            // a qualified call, whose counterpart the companion declares
            #[verus_verify]
            fn qualified_call() {
                proof_with!{Ghost(3int) => Ghost(g2)}
                let r = T::f(&S, 7);
                proof!{ assert(r == 7); assert(g2 == 4); }
            }

            // a generic caller gets the companion-trait bound added to it
            #[verus_spec]
            fn call_generic<A: T>(x: &A) {
                proof_with!{Ghost(3int) => Ghost(g2)}
                let r = x.f(7);
                proof!{ assert(r == 7); assert(g2 == 4); }
            }

            // the added bound has to be satisfied by a concrete argument
            #[verus_verify]
            fn call_the_generic_caller() {
                call_generic(&S);
            }
        }
        // the proxy may be generic, and its companion must carry those
        // parameters through to the implementation
        + &in_mod("generic_trait", code_str!{
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
                proof_with!{Ghost(3int) => Ghost(g2)}
                let r = S.f(7);
                proof!{ assert(r == 7); assert(g2 == 4); }
            }
        })
        // a proxy may describe some methods with `with` and some without, and
        // each `with` method gets a counterpart of its own, ghost or tracked
        + &in_mod("mixed_methods", code_str!{
            use vstd::prelude::*;

            #[verifier::external]
            trait T {
                fn ghost_method(&self, a: u64) -> u64;
                fn tracked_method(&self) -> u64;
                fn output_only(&self, a: u64) -> u64;
                fn plain(&self) -> u64;
            }

            #[verus_verify]
            #[verifier::external_trait_specification]
            trait ExT {
                type ExternalTraitSpecificationFor: T;

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

                // extra outputs alone are enough to need a counterpart
                #[verus_spec(r =>
                    with -> g2: Ghost<int>
                    ensures r == a, g2@ == a,
                )]
                fn output_only(&self, a: u64) -> u64;

                #[verus_spec(r => ensures r == 5)]
                fn plain(&self) -> u64;
            }

            #[verus_verify]
            struct S;

            #[verus_verify]
            impl T for S {
                #[verus_spec(with Ghost(g): Ghost<int> -> g2: Ghost<int>)]
                fn ghost_method(&self, a: u64) -> u64 {
                    proof_decl!{ let ghost gg: int = g + 1; }
                    proof_with!{|= Ghost(gg)}
                    a
                }

                #[verus_spec(with -> g2: Ghost<int>)]
                fn output_only(&self, a: u64) -> u64 {
                    proof_decl!{ let ghost gg: int = a as int; }
                    proof_with!{|= Ghost(gg)}
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

            #[verus_verify]
            fn call_all<A: T>(x: &A) {
                proof_with!{Ghost(3int) => Ghost(g2)}
                let r = x.ghost_method(7);
                proof_with!{Tracked(1u64)}
                let q = x.tracked_method();
                proof_with!{=> Ghost(g3)}
                let o = x.output_only(4);
                let p = x.plain();
                proof!{
                    assert(r == 7); assert(g2 == 4); assert(q == 2);
                    assert(o == 4); assert(g3 == 4); assert(p == 5);
                }
            }

            #[verus_verify]
            fn test() {
                call_all(&S);
                proof_with!{Tracked(1u64)}
                let r = S.tracked_method();
                proof!{ assert(r == 2); }
            }
        })
    => Ok(())
}

test_verify_one_file_with_options! {
    // The companion trait is erased away when the code is compiled: the body
    // stays in the implementation of the external trait.
    #[test] test_external_trait_with_compile ["--compile"] =>
        EXTERNAL_TRAIT_DECL.to_string() + EXTERNAL_TRAIT + CALL_EXTERNAL_TRAIT
    => Ok(())
}

test_verify_one_file! {
    // The method of the external trait has `requires(false)`: what it does
    // without the extra arguments is not specified.
    #[test] test_external_trait_with_plain_call
        EXTERNAL_TRAIT_DECL.to_string() + EXTERNAL_TRAIT + code_str!{
        #[verus_verify]
        fn test() {
            let r = S.f(7); // FAILS
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

            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn g(&self) -> u64;
        }

        #[verus_verify]
        impl T for S {}

        #[verus_verify]
        fn test() {
            proof_with!{Tracked(1u64)}
            let q = S.g();
        }
    } => Err(e) => assert_rust_error_msg_all(e, "no method named `_VERUS_VERIFIED_g` found for struct `S`")
}
