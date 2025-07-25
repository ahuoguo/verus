//! The "standard library" for [Verus](https://github.com/verus-lang/verus).
//! Contains various utilities and datatypes for proofs,
//! as well as runtime functionality with specifications.
//! For an introduction to Verus, see [the tutorial](https://verus-lang.github.io/verus/guide/).
#![cfg_attr(not(feature = "std"), no_std)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![allow(rustdoc::invalid_rust_codeblocks)]
#![cfg_attr(verus_keep_ghost, feature(core_intrinsics))]
#![cfg_attr(any(verus_keep_ghost, feature = "allocator"), feature(allocator_api))]
#![cfg_attr(verus_keep_ghost, feature(step_trait))]
#![cfg_attr(verus_keep_ghost, feature(ptr_metadata))]
#![cfg_attr(verus_keep_ghost, feature(strict_provenance_atomic_ptr))]
#![cfg_attr(verus_keep_ghost, feature(freeze))]
#![cfg_attr(verus_keep_ghost, feature(derive_clone_copy))]
#![cfg_attr(all(feature = "alloc", verus_keep_ghost), feature(liballoc_internals))]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod arithmetic;
pub mod array;
pub mod atomic;
pub mod atomic_ghost;
pub mod bits;
pub mod bytes;
pub mod calc_macro;
pub mod cell;
pub mod compute;
pub mod function;
#[cfg(all(feature = "alloc", feature = "std"))]
pub mod hash_map;
#[cfg(all(feature = "alloc", feature = "std"))]
pub mod hash_set;
pub mod invariant;
pub mod layout;
pub mod logatom;
pub mod map;
pub mod map_lib;
pub mod math;
pub mod modes;
pub mod multiset;
pub mod multiset_lib;
pub mod pcm;
pub mod pcm_lib;
pub mod pervasive;
pub mod proph;
pub mod raw_ptr;
pub mod rwlock;
pub mod seq;
pub mod seq_lib;
pub mod set;
pub mod set_lib;
pub mod shared;
#[cfg(feature = "alloc")]
pub mod simple_pptr;
pub mod slice;
pub mod state_machine_internal;
pub mod storage_protocol;
pub mod string;
#[cfg(feature = "std")]
pub mod thread;
pub mod view;

pub mod relations;
#[cfg(verus_keep_ghost)]
pub mod std_specs;

// Re-exports all vstd types, traits, and functions that are commonly used or replace
// regular `core` or `std` definitions.
pub mod prelude;
pub mod tokens;

use prelude::*;

verus! {

#[cfg_attr(verus_keep_ghost, verifier::broadcast_use_by_default_when_this_crate_is_imported)]
pub broadcast group group_vstd_default {
    //
    // basic Verus math, types, and features
    //
    seq::group_seq_axioms,
    seq_lib::group_seq_lib_default,
    map::group_map_axioms,
    set::group_set_axioms,
    set_lib::group_set_lib_default,
    multiset::group_multiset_axioms,
    compute::all_spec_ensures,
    function::group_function_axioms,
    //
    // Rust types
    //
    slice::group_slice_axioms,
    array::group_array_axioms,
    string::group_string_axioms,
    raw_ptr::group_raw_ptr_axioms,
    layout::group_layout_axioms,
    //
    // core std_specs
    //
    std_specs::range::group_range_axioms,
    std_specs::bits::group_bits_axioms,
    std_specs::control_flow::group_control_flow_axioms,
    std_specs::slice::group_slice_axioms,
    //
    // std_specs for alloc (with or without std)
    //
    #[cfg(feature = "alloc")]
    std_specs::vec::group_vec_axioms,
    #[cfg(feature = "alloc")]
    std_specs::vecdeque::group_vec_dequeue_axioms,
    //
    // std_specs for alloc + std
    //
    #[cfg(all(feature = "alloc", feature = "std"))]
    std_specs::hash::group_hash_axioms,
}

} // verus!
// This allows us to use `$crate::vstd` or `crate::vstd` to refer to vstd
// both in verus_verify_core mode (vstd is a module) and out (vstd is a crate)
#[cfg(not(verus_verify_core))]
#[doc(hidden)]
pub use crate as vstd;
