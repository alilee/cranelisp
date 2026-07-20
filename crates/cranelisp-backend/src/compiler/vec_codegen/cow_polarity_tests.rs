//! §13.5 branch × polarity matrix — the `SourceOwnership` consumed-source
//! contract on the shared COW cores (design/backend/ownership-codegen.md §13.3
//! Ruling 2; the FIXME-0474 cure). These are the `/dev` unit-tier cells `/qa`
//! audits (0495 step-2 rc_emission/fn_as_value drain), pinning the SPECIFIC
//! copy-branch RC emission per cell — not "no crash".
//!
//! Contract under test: a COW op's **copy** branch (rc>1) returns a NEW Vec, so
//! an `Owned` consumed-source reference (wrapper/curry bodies) MUST be released
//! there via `emit_vec_rc_dec_with_drop` (an `atomic_rmw.i64 sub` guarding the
//! `vec_drop` free); the **mutate**/**grow** branches (rc==1, same pointer
//! returned) release nothing; a `Borrowed` source (static in-place sites — the
//! arg compilation emitted no consuming inc) releases nothing on ANY branch.
//!
//! Method: emit each core into a scratch probe function over a fresh JIT module
//! with dummy `dealloc`/`vec_drop` externs and NeverHeap element metadata (so
//! the ONLY rc-dec traffic possible is the consumed-source release), then read
//! the function's CLIF text. With `old_elem_category = None` and `inc_fn = 0`,
//! an `atomic_rmw.i64 sub` appears in the core's CLIF **iff** the polarity is
//! `Owned` — the copy-branch release. That single instruction is the contract.

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::Span;

use super::{emit_vec_push_cow_core, emit_vec_set_cow_core, SourceOwnership, VecSetCow};
use crate::jit::Jit;

/// COW source polarity for the probe harness (R14 / §13.7).
#[derive(Clone, Copy)]
enum Own {
    /// Wrapper/curry consuming, fresh-temp, or toggle-off all-Owned — the copy
    /// branch releases; the mutate branch transfers (no inc).
    Owned,
    /// analysis-ON live-`Var` binding, result ESCAPES — the mutate/grow branch
    /// incs the reused pointer (the 0641 B-2/I-2 retention).
    BorrowedEscaping,
    /// analysis-ON live-`Var` binding, result does NOT escape (recur-transfer /
    /// in-frame consume) — no mutate inc (l_c3 in-place reuse preserved).
    BorrowedInFrame,
}

/// Build a probe function `(i64) -> i64` whose body is a single COW core
/// (`vec-set` if `set`, else `vec-push`) at the given polarity, and return its
/// CLIF text. Dummy `dealloc`/`vec_drop` externs stand in for the runtime; the
/// element category is NeverHeap (`None` / `inc_fn = 0`) so no element RC
/// traffic can mask the consumed-source release or the §13.7 retention inc.
fn cow_core_clif(set: bool, own: Own) -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let module = jit.jit_module();

    let mut da_sig = module.make_signature();
    da_sig.params.push(AbiParam::new(types::I64));
    let dealloc_id = module
        .declare_function("test_dealloc", Linkage::Import, &da_sig)
        .expect("declare dealloc");

    let mut vd_sig = module.make_signature();
    vd_sig.params.push(AbiParam::new(types::I64));
    vd_sig.params.push(AbiParam::new(types::I64));
    let vec_drop_id = module
        .declare_function("test_vec_drop", Linkage::Import, &vd_sig)
        .expect("declare vec_drop");

    let mut ctx = module.make_context();
    let mut fctx = FunctionBuilderContext::new();
    ctx.func.signature.params.push(AbiParam::new(types::I64));
    ctx.func.signature.returns.push(AbiParam::new(types::I64));

    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fctx);
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);
    let vec_val = builder.block_params(entry)[0];
    let idx = builder.ins().iconst(types::I64, 0);
    let new_val = builder.ins().iconst(types::I64, 9);
    let inc_fn = builder.ins().iconst(types::I64, 0);
    let dec_fn = builder.ins().iconst(types::I64, 0);

    let source_ownership = match own {
        Own::Owned => SourceOwnership::Owned {
            vec_drop_func_id: vec_drop_id,
            elem_dec_fn_ptr: dec_fn,
        },
        Own::BorrowedEscaping => SourceOwnership::Borrowed { retain_reused: true },
        Own::BorrowedInFrame => SourceOwnership::Borrowed { retain_reused: false },
    };

    let result = if set {
        emit_vec_set_cow_core(
            &mut builder,
            module,
            VecSetCow {
                vec_val,
                idx_val: idx,
                new_val,
                inc_fn_ptr: inc_fn,
                old_elem_category: None,
                dealloc_id,
                source_ownership,
                // Source-ownership polarity harness exercises the DYNAMIC rc==1
                // token path (no static proof) — the copy branch must be reachable.
                elide_rc_check: false,
            },
            Span::SYNTHETIC,
        )
    } else {
        emit_vec_push_cow_core(
            &mut builder,
            module,
            vec_val,
            new_val,
            inc_fn,
            source_ownership,
            false,
            Span::SYNTHETIC,
        )
    }
    .expect("emit cow core");

    builder.ins().return_(&[result]);
    builder.seal_all_blocks();
    builder.finalize();
    ctx.func.display().to_string()
}

/// `atomic_rmw.i64 sub` occurrences — with NeverHeap elements the ONLY such
/// op the core can emit is the consumed-source rc-dec (`emit_vec_rc_dec_with_drop`).
fn rc_dec_count(clif: &str) -> usize {
    clif.matches("atomic_rmw.i64 sub").count()
}

/// `atomic_rmw.i64 add` occurrences — with NeverHeap elements + `RC_STATS` off,
/// the ONLY such op the core can emit is the §13.7 escape-gated retention inc
/// (`retain_reused_source`, Borrowed-escaping only).
fn rc_inc_count(clif: &str) -> usize {
    clif.matches("atomic_rmw.i64 add").count()
}

// spec: design/backend/ownership-codegen.md §13.3 — vec-set COW core, Owned
// polarity: the copy branch releases the consumed source (one rc-dec).
#[test]
fn vec_set_cow_copy_branch_releases_owned_source() {
    let clif = cow_core_clif(true, Own::Owned);
    assert_eq!(
        rc_dec_count(&clif),
        1,
        "vec-set COW core with Owned source MUST emit exactly one consumed-source \
         rc-dec (the copy-branch release, §13.3 Ruling 2). CLIF:\n{clif}"
    );
    // The release is rc-CHECKED: the `atomic_rmw.i64 sub` (the dec) feeds an
    // `icmp` == 1 guarding a `brif` into the vec_drop free path — never an
    // unconditional free.
    assert!(
        clif.contains("atomic_rmw.i64 sub") && clif.contains("brif"),
        "the Owned release must route through the rc-checked vec_drop teardown \
         (atomic dec + brif on rc==1), not an unconditional free. CLIF:\n{clif}"
    );
}

// spec: design/backend/ownership-codegen.md §13.3 — vec-set COW core, Borrowed
// polarity (static in-place site): NO branch releases the source (scope owns it).
#[test]
fn vec_set_cow_borrowed_source_releases_nothing_neg() {
    let clif = cow_core_clif(true, Own::BorrowedInFrame);
    assert_eq!(
        rc_dec_count(&clif),
        0,
        "vec-set COW core with Borrowed source MUST NOT emit any consumed-source \
         rc-dec — the scope binding owns the reference; a release here would \
         double-free (§13.3 Ruling 2 static-site polarity). CLIF:\n{clif}"
    );
}

// spec: design/backend/ownership-codegen.md §13.3 — vec-push COW core, Owned:
// copy branch releases the consumed source exactly once.
#[test]
fn vec_push_cow_copy_branch_releases_owned_source() {
    let clif = cow_core_clif(false, Own::Owned);
    assert_eq!(
        rc_dec_count(&clif),
        1,
        "vec-push COW core with Owned source MUST emit exactly one consumed-source \
         rc-dec on the copy branch (§13.3 Ruling 2). CLIF:\n{clif}"
    );
}

// spec: design/backend/ownership-codegen.md §13.3 — vec-push COW core, Borrowed:
// mutate/grow/copy all release nothing.
#[test]
fn vec_push_cow_borrowed_source_releases_nothing_neg() {
    let clif = cow_core_clif(false, Own::BorrowedInFrame);
    assert_eq!(
        rc_dec_count(&clif),
        0,
        "vec-push COW core with Borrowed source MUST NOT emit any consumed-source \
         rc-dec (§13.3 Ruling 2 static-site polarity). CLIF:\n{clif}"
    );
}

// spec: design/backend/ownership-codegen.md §13.3 — polarity is the SOLE
// difference: Owned emits exactly one more rc-dec than Borrowed, for both ops.
// (The contract, not a spot dec: the delta is attributable to the polarity
// parameter alone — Principle 18.)
#[test]
fn cow_core_owned_minus_borrowed_is_exactly_one_release() {
    for set in [true, false] {
        let owned = rc_dec_count(&cow_core_clif(set, Own::Owned));
        let borrowed = rc_dec_count(&cow_core_clif(set, Own::BorrowedInFrame));
        assert_eq!(
            owned - borrowed,
            1,
            "the Owned/Borrowed rc-dec delta MUST be exactly one release \
             (set={set}): owned={owned} borrowed={borrowed}"
        );
    }
}

// =============================================================================
// §13.7 escape-gate matrix (S113 W5b, FIXME-0664 /arch ruling) — the mutate/grow
// branch retention INC. Fires ONLY for a Borrowed live-`Var` binding whose result
// ESCAPES the source's scope (`BorrowedEscaping`): the returned same pointer
// outlives the binding's scope-dec and must own an independent reference (the
// 0641 B-2/I-2 UAF). A recur-transfer / in-frame consume (`BorrowedInFrame`) and
// `Owned` (transfer) emit NO inc — preserving l_c3 loop reuse and killing the
// fresh-temp/loop over-retain. The VALUE-correctness half is the committed e2e
// repros + the toggle × modes lane.
// =============================================================================

// spec: design/backend/ownership-codegen.md §13.7 — vec-set mutate branch,
// Borrowed-ESCAPING: exactly one retention inc on the returned same pointer.
#[test]
fn vec_set_cow_borrowed_escaping_retains_reused_source() {
    let clif = cow_core_clif(true, Own::BorrowedEscaping);
    assert_eq!(
        rc_inc_count(&clif),
        1,
        "vec-set COW core, Borrowed-escaping source MUST emit exactly one \
         mutate-branch retention inc (§13.7). CLIF:\n{clif}"
    );
}

// spec: §13.7 — vec-push unique branch, Borrowed-ESCAPING: one retention inc
// (covers both fast + grow, which return the same pointer).
#[test]
fn vec_push_cow_borrowed_escaping_retains_reused_source() {
    let clif = cow_core_clif(false, Own::BorrowedEscaping);
    assert_eq!(
        rc_inc_count(&clif),
        1,
        "vec-push COW core, Borrowed-escaping source MUST emit exactly one \
         unique-branch retention inc (§13.7, one covers fast+grow). CLIF:\n{clif}"
    );
}

// spec: §13.7 — the escape gate: an IN-FRAME Borrowed source (recur-transfer /
// non-escape) and an Owned source emit NO mutate-branch inc. The in-frame case
// is the l_c3 in-place-reuse preservation; the Owned case is the transfer. Both
// = zero inc, for both ops. (The negative side that kills the fresh-temp/loop
// over-retain the FIXME-0664 falsification found.)
#[test]
fn cow_core_no_retention_inc_for_inframe_or_owned_neg() {
    for set in [true, false] {
        assert_eq!(
            rc_inc_count(&cow_core_clif(set, Own::BorrowedInFrame)),
            0,
            "in-frame Borrowed (non-escape) MUST NOT emit a retention inc \
             (set={set}) — preserves l_c3 loop reuse"
        );
        assert_eq!(
            rc_inc_count(&cow_core_clif(set, Own::Owned)),
            0,
            "Owned source MUST NOT emit a retention inc (set={set}) — transfer"
        );
    }
}

// spec: §13.7 — the retention inc is attributable to the ESCAPE gate ALONE
// (Principle 18): Borrowed-escaping emits exactly one more mutate-branch inc than
// Borrowed-in-frame, for both ops.
#[test]
fn cow_core_escaping_minus_inframe_is_exactly_one_retention() {
    for set in [true, false] {
        let escaping = rc_inc_count(&cow_core_clif(set, Own::BorrowedEscaping));
        let inframe = rc_inc_count(&cow_core_clif(set, Own::BorrowedInFrame));
        assert_eq!(
            escaping - inframe,
            1,
            "the escaping/in-frame retention-inc delta MUST be exactly one \
             (set={set}): escaping={escaping} inframe={inframe}"
        );
    }
}

