#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Use external_fn_specification on an external function from the same crate

test_verify_one_file! {
    #[test] test_basics verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }

        fn test1() {
            let ret_b = negate_bool(true, 1);
            assert(ret_b == false);
        }

        fn test2() {
            let ret_b = negate_bool(true, 0); // FAILS
        }

        fn test3() {
            let ret_b = negate_bool(true, 1);
            assert(ret_b == true); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

// Apply external_fn_specification on a function from an external crate
// don't import vstd for this test (it would cause overlap)

test_verify_one_file! {
    #[test] test_apply_spec_to_external verus_code! {
        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }

        fn test1() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 7 && y == 5);
        }

        fn test2() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 5); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// Import a specification from vstd of a function from std

test_verify_one_file! {
    #[test] test_import_spec_from_vstd verus_code! {
        use vstd::*;

        fn test1() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 7 && y == 5);
        }

        fn test2() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 5); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// Test for overlap

test_verify_one_file! {
    #[test] test_overlap verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures2(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `crate::negate_bool`")
}

test_verify_one_file! {
    #[test] test_overlap2 verus_code! {
        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }

        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures2<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `core::mem::swap`")
}

test_verify_one_file! {
    #[test] test_overlap3 verus_code! {
        use vstd::*;

        // This will conflict with the mem::swap specification declared in vstd
        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `core::mem::swap`")
}

// Test sane error message if you call a proxy

test_verify_one_file! {
    #[test] test_call_proxy verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }

        fn test() {
            negate_bool_requires_ensures(false, 1);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function marked `external_fn_specification` directly; call `negate_bool` instead")
}

test_verify_one_file! {
    #[test] test_call_proxy2 verus_code! {
        fn test() {
            let x: u8 = 5;
            let y: u8 = 7;
            vstd::std_specs::core::ex_swap(&mut x, &mut y);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function marked `external_fn_specification` directly; call `core::mem::swap` instead")
}

// If you wrongly try to apply a mode

test_verify_one_file! {
    #[test] test_proxy_marked_spec verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        spec fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
        {
            negate_bool(b, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "a function marked `external_fn_specification` cannot be marked `spec`")
}

test_verify_one_file! {
    #[test] test_proxy_marked_proof verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        proof fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
        {
            negate_bool(b, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "a function marked `external_fn_specification` cannot be marked `proof`")
}

// test visibility stuff

test_verify_one_file! {
    #[test] test_refers_to_closed_fn verus_code! {
        mod X {
            pub closed spec fn foo(b: bool, x: u8) -> bool {
                b && x == 0
            }

            #[verifier(external_fn_specification)]
            pub fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
                requires foo(b, x)
            {
                crate::negate_bool(b, x)
            }
        }

        #[verifier(external)]
        pub fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        pub fn test() {
            // this should fail because foo is closed
            negate_bool(true, 0); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_refers_to_open_fn verus_code! {
        mod X {
            pub open spec fn foo(b: bool, x: u8) -> bool {
                b && x == 0
            }

            #[verifier(external_fn_specification)]
            pub fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
                requires foo(b, x)
            {
                crate::negate_bool(b, x)
            }
        }

        #[verifier(external)]
        pub fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        pub fn test() {
            negate_bool(true, 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_refers_to_private_fn verus_code! {
        mod X {
            fn foo(b: bool, x: u8) -> bool {
                b && x == 0
            }

            #[verifier(external_fn_specification)]
            pub fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
                requires foo(b, x)
            {
                negate_bool(b, x)
            }

            #[verifier(external)]
            pub fn negate_bool(b: bool, x: u8) -> bool {
                !b
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "public function requires cannot refer to private items")
}

test_verify_one_file! {
    #[test] test_proxy_is_more_private verus_code! {
        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
        {
            negate_bool(b, x)
        }

        #[verifier(external)]
        pub fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }
    } => Err(err) => assert_vir_error_msg(err, "a function marked `external_fn_specification` must be at least as visible as the function it provides a spec for")
}

test_verify_one_file! {
    #[test] test_proxy_is_more_private2 verus_code! {
        mod X {
            #[verifier(external_fn_specification)]
            pub fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
            {
                crate::Y::negate_bool(b, x)
            }
        }

        pub mod Y {
            #[verifier(external)]
            pub fn negate_bool(b: bool, x: u8) -> bool {
                !b
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "a function marked `external_fn_specification` must be at least as visible as the function it provides a spec for")
}

test_verify_one_file! {
    #[test] test_proxy_is_more_private3 verus_code! {
        #[verifier(external_fn_specification)]
        fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "a function marked `external_fn_specification` must be at least as visible as the function it provides a spec for")
}

// Test the attribute in weird places

test_verify_one_file! {
    #[test] test_attr_on_const verus_code! {
        #[verifier(external_fn_specification)]
        const x: u8 = 5;
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not yet supported for const")
}

test_verify_one_file! {
    #[test] test_attr_on_struct verus_code! {
        #[verifier(external_fn_specification)]
        struct X { }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_impl verus_code! {
        struct X { }

        #[verifier(external_fn_specification)]
        impl X { }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_trait verus_code! {
        #[verifier(external_fn_specification)]
        trait Tr { }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_trait_fn verus_code! {
        trait Tr {
            #[verifier(external_fn_specification)]
            fn foo();
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_trait_fn_impl verus_code! {
        trait Tr {
            fn foo();
        }

        struct X { }

        impl Tr for X {
            #[verifier(external_fn_specification)]
            fn foo() { }
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_member_function verus_code! {
        struct X { }

        impl X {
            #[verifier(external_fn_specification)]
            fn stuff(&self) { }
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_assoc_function verus_code! {
        struct X { }

        impl X {
            #[verifier(external_fn_specification)]
            fn stuff() { }
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_foreign_function verus_code! {
        extern "C" {
            #[verifier(external_fn_specification)]
            fn stuff();
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported on foreign items")
}

// Mismatched type signatures

test_verify_one_file! {
    #[test] mixed_up_params verus_code! {
        #[verifier(external)]
        fn or_bools(b: bool, c: bool) -> bool {
            b || c
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, c: bool) -> (ret_b: bool)
            ensures ret_b == b || c
        {
            or_bools(c, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "params do not match")
}

test_verify_one_file! {
    #[test] wrong_num_params verus_code! {
        #[verifier(external)]
        fn or_bools(b: bool, c: bool) -> bool {
            b || c
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, c: bool) -> (ret_b: bool)
            ensures ret_b == b || c
        {
            or_bools(b)
        }
    } => Err(err) => assert_vir_error_msg(err, "params do not match")
}

test_verify_one_file! {
    #[test] wrong_num_params2 verus_code! {
        #[verifier(external)]
        fn or_bools(b: bool, c: bool) -> bool {
            b || c
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, c: bool) -> (ret_b: bool)
            ensures ret_b == b || c
        {
            or_bools(b, c, c)
        }
    } => Err(err) => assert_vir_error_msg(err, "params do not match")
}

test_verify_one_file! {
    #[test] extra_trait_bound verus_code! {
        #[verifier(external_fn_specification)]
        fn swap_requires_ensures<T: Copy>(a: &mut T, b: &mut T)
        {
            core::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "extra trait bound")
}

test_verify_one_file! {
    #[test] extra_trait_bound2 verus_code! {
        #[verifier(external)]
        fn sw(a: &mut T, b: &mut T) {
        }

        #[verifier(external_fn_specification)]
        fn swap_requires_ensures<T: Copy>(a: &mut T, b: &mut T)
        {
            sw(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "extra trait bound")
}

// Lifetime checking

test_verify_one_file! {
    #[test] checking_lifetime verus_code! {
        use vstd::*;
        fn main(x: u8) {
            let mut a = x;
            core::mem::swap(&mut a, &mut a);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `a` as mutable more than once at a time")
}

test_verify_one_file! {
    #[test] checking_lifetime2 verus_code! {
        #[verifier(external)]
        fn foo<'a>(b: &'a bool) -> &'a bool {
            b
        }

        #[verifier(external_fn_specification)]
        fn foo_requires_ensures<'a>(b: &'a bool) -> &'a bool
        {
            foo(b)
        }

        fn test() {
            let mut x: bool = true;
            let y = foo(&x);
            x = false;
            foo(y);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot assign to `x` because it is borrowed")
}
