//! §3.1 caller-side borrow-elision — the per-argument RC decision matrix
//! (`design/backend/ownership-codegen.md` §3.1 / §13.5 apply row, Principle 23).
//!
//! `moded_arg_rc` is the pure decision core of
//! `FnCompiler::compile_consuming_arg_list_moded`: it maps
//! `{heap category} × {callee param mode} × {owned-binding vs temporary}` to the
//! RC action emitted at the call site. This module pins the FULL matrix — every
//! implied cell, complexity/edge/negative classes — so `/qa` can audit coverage
//! mechanically and the strategy's scenario space is guarded independent of the
//! spec-derived e2e lanes.

use super::{moded_arg_rc, ModedArgRc};
use crate::heap::HeapCategory;
use cranelisp_types::Mode;

// --- Negative / scalar class: NeverHeap is ALWAYS a no-op, whatever mode or
//     binding kind — RC never touches a scalar. ---
#[test]
fn never_heap_is_always_none() {
    for mode in [Mode::Owned, Mode::Borrowed, Mode::Copy] {
        for owned in [true, false] {
            assert_eq!(
                moded_arg_rc(HeapCategory::NeverHeap, mode, owned),
                ModedArgRc::None,
                "NeverHeap must never emit an RC op (mode={mode:?}, owned={owned})",
            );
        }
    }
}

// --- Byte-identical-off class: the conservative point (every param `Owned`)
//     must reproduce the pre-S102 `compile_consuming_arg_list` behaviour —
//     inc an owned-binding Var, do nothing for a temporary. This is the §2.2
//     else-arm identity at the decision grain. ---
#[test]
fn owned_mode_reproduces_pre_s102_consuming() {
    // Owned-binding Var → consuming inc (guarded iff Mixed).
    assert_eq!(moded_arg_rc(HeapCategory::AlwaysHeap, Mode::Owned, true), ModedArgRc::Inc);
    assert_eq!(moded_arg_rc(HeapCategory::Mixed, Mode::Owned, true), ModedArgRc::IncGuarded);
    // Temporary → transfer, no op.
    assert_eq!(moded_arg_rc(HeapCategory::AlwaysHeap, Mode::Owned, false), ModedArgRc::None);
    assert_eq!(moded_arg_rc(HeapCategory::Mixed, Mode::Owned, false), ModedArgRc::None);
}

// --- Elision class: a `Borrowed` param elides the consuming inc on an
//     owned-binding Var (the caller retains ownership; its scope-cleanup dec is
//     the single accounting). ---
#[test]
fn borrowed_owned_binding_elides_inc() {
    assert_eq!(moded_arg_rc(HeapCategory::AlwaysHeap, Mode::Borrowed, true), ModedArgRc::None);
    assert_eq!(moded_arg_rc(HeapCategory::Mixed, Mode::Borrowed, true), ModedArgRc::None);
}

// --- Post-call-dec class: a TEMPORARY (fresh rc=1, no scope owner) handed to a
//     `Borrowed` param owes a post-call dec — the callee/adapter will not dec
//     it. Unguarded for AlwaysHeap, guarded for Mixed. THIS is the cell whose
//     absence leaked the fn-as-value closure (repro_d). ---
#[test]
fn borrowed_temporary_owes_post_call_dec() {
    assert_eq!(moded_arg_rc(HeapCategory::AlwaysHeap, Mode::Borrowed, false), ModedArgRc::PostDec);
    assert_eq!(
        moded_arg_rc(HeapCategory::Mixed, Mode::Borrowed, false),
        ModedArgRc::PostDecGuarded
    );
}

// --- Copy class: `Copy` is value-representation (no RC identity). Pass-through
//     in every position — never minted for a heap category in increment I, but
//     the mapping is total and defensive. ---
#[test]
fn copy_mode_is_pass_through() {
    for cat in [HeapCategory::AlwaysHeap, HeapCategory::Mixed] {
        for owned in [true, false] {
            assert_eq!(
                moded_arg_rc(cat, Mode::Copy, owned),
                ModedArgRc::None,
                "Copy is value-repr — no RC op (cat={cat:?}, owned={owned})",
            );
        }
    }
}

// --- Exhaustive matrix witness: the full 3×3×2 table, so a future edit that
//     shifts any single cell fails loudly with the cell named. ---
#[test]
fn full_matrix_is_pinned() {
    use HeapCategory::{AlwaysHeap as A, Mixed as M, NeverHeap as N};
    use Mode::{Borrowed as B, Copy as C, Owned as O};
    use ModedArgRc::*;
    // (category, mode, owned_binding) => expected
    let cases = [
        ((N, O, true), None), ((N, O, false), None),
        ((N, B, true), None), ((N, B, false), None),
        ((N, C, true), None), ((N, C, false), None),
        ((A, O, true), Inc), ((A, O, false), None),
        ((A, B, true), None), ((A, B, false), PostDec),
        ((A, C, true), None), ((A, C, false), None),
        ((M, O, true), IncGuarded), ((M, O, false), None),
        ((M, B, true), None), ((M, B, false), PostDecGuarded),
        ((M, C, true), None), ((M, C, false), None),
    ];
    for ((cat, mode, owned), expected) in cases {
        assert_eq!(
            moded_arg_rc(cat, mode, owned),
            expected,
            "matrix cell ({cat:?}, {mode:?}, owned={owned})",
        );
    }
}
