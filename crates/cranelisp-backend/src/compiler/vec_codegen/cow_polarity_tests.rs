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

/// Build a probe function `(i64) -> i64` whose body is a single COW core
/// (`vec-set` if `set`, else `vec-push`) at the given polarity, and return its
/// CLIF text. Dummy `dealloc`/`vec_drop` externs stand in for the runtime; the
/// element category is NeverHeap (`None` / `inc_fn = 0`) so no element RC
/// traffic can mask the consumed-source release.
fn cow_core_clif(set: bool, owned: bool) -> String {
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

    let source_ownership = if owned {
        SourceOwnership::Owned {
            vec_drop_func_id: vec_drop_id,
            elem_dec_fn_ptr: dec_fn,
        }
    } else {
        SourceOwnership::Borrowed
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

// spec: design/backend/ownership-codegen.md §13.3 — vec-set COW core, Owned
// polarity: the copy branch releases the consumed source (one rc-dec).
#[test]
fn vec_set_cow_copy_branch_releases_owned_source() {
    let clif = cow_core_clif(true, /*owned=*/ true);
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
    let clif = cow_core_clif(true, /*owned=*/ false);
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
    let clif = cow_core_clif(false, /*owned=*/ true);
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
    let clif = cow_core_clif(false, /*owned=*/ false);
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
        let owned = rc_dec_count(&cow_core_clif(set, true));
        let borrowed = rc_dec_count(&cow_core_clif(set, false));
        assert_eq!(
            owned - borrowed,
            1,
            "the Owned/Borrowed rc-dec delta MUST be exactly one release \
             (set={set}): owned={owned} borrowed={borrowed}"
        );
    }
}
