use super::*;

// spec: 12-runtime §12.1.4 — ADT heap layout offsets (tag at 16, fields at 24+)
#[test]
fn test_heap_adt_layout() {
    assert_eq!(HeapAdt::TAG_OFFSET, 16);
    assert_eq!(HeapAdt::FIELDS_START, 24);
    assert_eq!(HeapAdt::field_offset(0), 24);
    assert_eq!(HeapAdt::field_offset(1), 32);
    assert_eq!(HeapAdt::payload_size(0), 8); // tag only
    assert_eq!(HeapAdt::payload_size(2), 24); // tag + 2 fields
}

// spec: 12-runtime §12.1.3 — closure heap layout (code_ptr at 16, drop_glue at 24, captures at 32+)
#[test]
fn test_heap_closure_layout() {
    assert_eq!(HeapClosure::CODE_PTR_OFFSET, 16);
    assert_eq!(HeapClosure::DROP_GLUE_PTR_OFFSET, 24);
    assert_eq!(HeapClosure::CAPTURES_START, 32);
    assert_eq!(HeapClosure::capture_offset(0), 32);
    assert_eq!(HeapClosure::capture_offset(1), 40);
    assert_eq!(HeapClosure::payload_size(0), 16); // code_ptr + drop_glue_ptr only
    assert_eq!(HeapClosure::payload_size(3), 40); // code_ptr + drop_glue_ptr + 3 captures
}

// spec: 12-runtime §12.1.5 — Vec heap layout (len/cap/data_ptr at 16/24/32)
#[test]
fn test_heap_vec_layout() {
    assert_eq!(HeapVec::LEN_OFFSET, 16);
    assert_eq!(HeapVec::CAP_OFFSET, 24);
    assert_eq!(HeapVec::DATA_PTR_OFFSET, 32);
    assert_eq!(HeapVec::payload_size(), 24);
    assert_eq!(std::mem::size_of::<HeapVec>(), 40);
}

// spec: sprints/SPRINT.md §"Wave 0" R4 — byte-identical-off guard for the RC
// inc codegen switch. With both S99 env gates unset (the test-process default),
// `emit_rc_inc` must emit the blessed inline `atomic_rmw` and NO `rc_stat_inc`
// tally call — i.e. the pre-S99 emission, unchanged.
#[test]
fn s99_emit_rc_inc_default_is_atomic_rmw_no_stat() {
    use crate::jit::Jit;
    use cranelift::prelude::*;

    let mut jit = Jit::new_with_symbols(&[]).expect("jit construction");
    let module = jit.jit_module();
    let mut ctx = module.make_context();
    ctx.func.signature.params.push(AbiParam::new(types::I64));

    let mut fbc = FunctionBuilderContext::new();
    {
        let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fbc);
        let entry = fb.create_block();
        fb.append_block_params_for_function_params(entry);
        fb.switch_to_block(entry);
        fb.seal_block(entry);
        let ptr = fb.block_params(entry)[0];
        super::emit_rc_inc(&mut fb, module, ptr);
        fb.ins().return_(&[]);
        fb.finalize();
    }
    let clif = ctx.func.display().to_string();

    assert!(
        clif.contains("atomic_rmw"),
        "default RC inc must emit atomic_rmw (byte-identical-off), got:\n{clif}"
    );
    assert!(
        !clif.contains("rc_stat_inc"),
        "RC-stats gate must be off by default (no tally call emitted):\n{clif}"
    );
}

// ===========================================================================
// The `CRANELISP_NONATOMIC_RC` probe (`design/backend/ownership-codegen.md`
// §5.1): every inline RC helper asks `use_nonatomic_arm`, whose only input is
// the probe. The probe is read once per process, so each leg runs the five
// helpers in a child process started with exactly the environment it names.
// The two legs discriminate each other: a probe that is ignored fails the
// probe leg, and a non-atomic default fails the default leg.
// ===========================================================================
#[cfg(test)]
mod rc_probe_tests {
    use crate::heap::{
        emit_rc_dec, emit_rc_dec_guarded, emit_rc_inc, emit_rc_inc_guarded, rc_emit_counts,
    };
    use crate::jit::Jit;
    use crate::test_child;
    use cranelift::prelude::*;
    use cranelift_module::{FuncId, Linkage, Module};

    const CHILD: &str = "child_emits_rc_helpers";
    const PASSED: &str = "RC_PROBE_CHILD_PASSED";

    /// Build a one-arg function, run `emit` (given builder + module + the arg
    /// pointer), and return the CLIF text.
    fn clif_of(
        emit: impl FnOnce(&mut FunctionBuilder, &mut cranelift_jit::JITModule, Value),
    ) -> String {
        let mut jit = Jit::new_with_symbols(&[]).expect("jit construction");
        let module = jit.jit_module();
        let mut ctx = module.make_context();
        ctx.func.signature.params.push(AbiParam::new(types::I64));
        let mut fbc = FunctionBuilderContext::new();
        {
            let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fbc);
            let entry = fb.create_block();
            fb.append_block_params_for_function_params(entry);
            fb.switch_to_block(entry);
            fb.seal_block(entry);
            let ptr = fb.block_params(entry)[0];
            emit(&mut fb, module, ptr);
            fb.ins().return_(&[]);
            fb.finalize();
        }
        ctx.func.display().to_string()
    }

    fn import(module: &mut cranelift_jit::JITModule, name: &str, params: usize) -> FuncId {
        let mut sig = module.make_signature();
        for _ in 0..params {
            sig.params.push(AbiParam::new(types::I64));
        }
        module
            .declare_function(name, Linkage::Import, &sig)
            .expect("declare import")
    }

    /// `(helper, is_dec, CLIF)` for each inline RC helper.
    fn emissions() -> Vec<(&'static str, bool, String)> {
        vec![
            ("emit_rc_inc", false, clif_of(emit_rc_inc)),
            ("emit_rc_inc_guarded", false, clif_of(emit_rc_inc_guarded)),
            (
                "emit_rc_dec",
                true,
                clif_of(|b, m, p| {
                    let d = import(m, "runtime/dealloc", 1);
                    emit_rc_dec(b, m, p, d, None);
                }),
            ),
            (
                "emit_rc_dec_guarded",
                true,
                clif_of(|b, m, p| {
                    let d = import(m, "runtime/dealloc", 1);
                    emit_rc_dec_guarded(b, m, p, d, None, true);
                }),
            ),
            (
                "emit_vec_rc_dec_with_drop",
                true,
                clif_of(|b, m, p| {
                    let d = import(m, "runtime/vec_drop", 2);
                    let no_elem_release = b.ins().iconst(types::I64, 0);
                    crate::compiler::vec_codegen::emit_vec_rc_dec_with_drop(
                        b,
                        m,
                        p,
                        d,
                        no_elem_release,
                    );
                }),
            ),
        ]
    }

    /// The plain arm is a load / `iadd`|`isub` / store of the count with no
    /// `atomic_rmw`; a decrement keeps its free-path `fence`.
    fn assert_nonatomic(helper: &str, is_dec: bool, clif: &str) {
        assert!(
            !clif.contains("atomic_rmw"),
            "{helper}: atomic_rmw under the probe:\n{clif}"
        );
        assert!(
            clif.contains("load.i64"),
            "{helper}: no count load:\n{clif}"
        );
        let op = if is_dec { "isub" } else { "iadd" };
        assert!(clif.contains(op), "{helper}: no {op}:\n{clif}");
        assert!(clif.contains("store"), "{helper}: no count store:\n{clif}");
        if is_dec {
            assert!(
                clif.contains("fence"),
                "{helper}: free-path fence lost:\n{clif}"
            );
        }
    }

    /// The default arm updates the count with exactly one `atomic_rmw` and
    /// never loads it.
    fn assert_atomic(helper: &str, is_dec: bool, clif: &str) {
        let op = if is_dec {
            "atomic_rmw.i64 sub"
        } else {
            "atomic_rmw.i64 add"
        };
        assert_eq!(clif.matches("atomic_rmw").count(), 1, "{helper}:\n{clif}");
        assert!(clif.contains(op), "{helper}: expected {op}:\n{clif}");
        assert!(
            !clif.contains("load.i64"),
            "{helper}: plain count load by default:\n{clif}"
        );
    }

    // Child body: emit every helper and check the arm the parent's `EXPECT`
    // names, then that one emission advanced the tally on the same arm.
    #[test]
    fn child_emits_rc_helpers() {
        if !test_child::selected(CHILD) {
            return;
        }
        let nonatomic = test_child::arg::<String>("EXPECT") == "nonatomic";
        for (helper, is_dec, clif) in emissions() {
            if nonatomic {
                assert_nonatomic(helper, is_dec, &clif);
            } else {
                assert_atomic(helper, is_dec, &clif);
            }
        }
        let (na0, tot0) = rc_emit_counts();
        let _ = clif_of(emit_rc_inc);
        let (na1, tot1) = rc_emit_counts();
        assert_eq!(tot1, tot0 + 1, "one emission advances the total");
        assert_eq!(
            na1,
            na0 + u64::from(nonatomic),
            "the non-atomic tally follows the arm"
        );
        println!("{PASSED}");
    }

    fn run_child(env: &[(&str, String)]) -> test_child::Ending {
        let path = test_child::child_path(module_path!(), CHILD);
        test_child::run(&path, env)
    }

    #[track_caller]
    fn assert_child_passed(ending: &test_child::Ending, what: &str) {
        assert_eq!(ending.code, Some(0), "{what}\nstderr:\n{}", ending.stderr);
        assert!(
            ending.stdout.contains(PASSED),
            "{what}: child body did not run\n{}",
            ending.stdout
        );
    }

    #[test]
    fn probe_unset_emits_the_atomic_sequence() {
        // spec: design/backend/ownership-codegen.md §5.2 — atomic unless the probe is set
        let ending = run_child(&[("EXPECT", "atomic".into())]);
        assert_child_passed(&ending, "probe unset");
    }

    #[test]
    fn probe_set_emits_the_plain_sequence() {
        // spec: design/backend/ownership-codegen.md §5.1 — the probe selects the non-atomic arm
        let ending = run_child(&[
            ("EXPECT", "nonatomic".into()),
            ("CRANELISP_NONATOMIC_RC", "1".into()),
        ]);
        assert_child_passed(&ending, "probe set");
    }

    // --- the codegen-time stack-slot-hit counter (h2 backend half, B3.4) ---
    #[test]
    fn stack_slot_hits_counter_tallies_emitted_slots() {
        // spec: design/backend/ownership-codegen.md §11 — backend-side stack-slot counter
        use crate::heap::{emit_stack_alloc, stack_slot_hits};
        let h0 = stack_slot_hits();
        let _ = clif_of(|b, _m, _p| {
            let _ = emit_stack_alloc(b, crate::heap::HeapAdt::payload_size(2) as i64);
        });
        assert_eq!(
            stack_slot_hits(),
            h0 + 1,
            "one stack alloc must advance the counter"
        );
        let _ = clif_of(|b, _m, _p| {
            let _ = emit_stack_alloc(b, crate::heap::HeapAdt::payload_size(1) as i64);
            let _ = emit_stack_alloc(b, crate::heap::HeapAdt::payload_size(3) as i64);
        });
        assert_eq!(
            stack_slot_hits(),
            h0 + 3,
            "two more stack allocs must advance by 2"
        );
    }
}

// ===========================================================================
// B3.4 stack-slot emission mechanism (design/backend/ownership-codegen.md
// §4.1/§4.2): `emit_stack_alloc` places a statically-sized, scalar-payload,
// NoEscape aggregate on a Cranelift stack slot with an IMMORTAL-RC header, so
// the existing RC/COW machinery composes untouched. This module pins the
// EMISSION mechanism at its seam (the consumption is gated OFF at the
// conservative point pending FIXME 0523 — the escape-fact soundness gap). When
// 0523 lands and the gate flips, this mechanism activates unchanged.
// ===========================================================================
#[cfg(test)]
mod stack_slot_b34_tests {
    use crate::heap::{HeapAdt, IMMORTAL_RC, emit_stack_alloc};
    use cranelift::prelude::*;
    use cranelisp_types::HeapHeader;

    /// Build a trivial function, run `emit_stack_alloc` in it, return the CLIF.
    fn clif_of(emit: impl FnOnce(&mut FunctionBuilder) -> Value) -> String {
        let mut fbc = FunctionBuilderContext::new();
        let mut func = cranelift::codegen::ir::Function::new();
        {
            let mut fb = FunctionBuilder::new(&mut func, &mut fbc);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.seal_block(entry);
            let v = emit(&mut fb);
            fb.ins().return_(&[v]);
            fb.finalize();
        }
        func.display().to_string()
    }

    // spec: design/backend/ownership-codegen.md §4.1 — stack slot instead of runtime/alloc
    #[test]
    fn emits_explicit_slot_and_stack_addr_not_a_call() {
        let clif = clif_of(|b| emit_stack_alloc(b, HeapAdt::payload_size(2) as i64));
        assert!(
            clif.contains("explicit_slot"),
            "must declare an explicit stack slot:\n{clif}"
        );
        assert!(
            clif.contains("stack_addr"),
            "must take the slot's address:\n{clif}"
        );
        assert!(
            !clif.contains("call fn"),
            "stack alloc must NOT call runtime/alloc:\n{clif}"
        );
    }

    // spec: design/backend/ownership-codegen.md §4.1 — slot size = header + payload
    #[test]
    fn slot_size_is_header_plus_payload() {
        // 2-field ADT: HeapHeader(16) + payload_size(2)=24 → explicit_slot 40.
        let total = HeapHeader::SIZE + HeapAdt::payload_size(2);
        assert_eq!(total, 40);
        let clif = clif_of(|b| emit_stack_alloc(b, HeapAdt::payload_size(2) as i64));
        assert!(
            clif.contains("explicit_slot 40"),
            "slot must be header+payload bytes:\n{clif}"
        );
    }

    // spec: design/backend/ownership-codegen.md §4.2 — immortal-RC sentinel header
    #[test]
    fn header_initialises_alloc_size_and_immortal_rc() {
        let clif = clif_of(|b| emit_stack_alloc(b, HeapAdt::payload_size(2) as i64));
        // alloc_size (total=40) stored at offset 0; IMMORTAL_RC stored at +8.
        assert!(
            clif.contains("iconst.i64 40"),
            "must iconst the total size (40):\n{clif}"
        );
        // IMMORTAL_RC = 1<<62; Cranelift prints it as a hex immediate.
        assert_eq!(IMMORTAL_RC, 1i64 << 62);
        assert!(
            clif.contains("0x4000_0000_0000_0000"),
            "must iconst the IMMORTAL_RC sentinel (1<<62) for the rc field:\n{clif}"
        );
        // Two header stores at the header offsets (alloc_size@0, rc@8).
        let stores = clif.matches("store").count();
        assert!(stores >= 2, "must store both header fields:\n{clif}");
    }

    // spec: design/backend/ownership-codegen.md §4.2 — sentinel is far above the
    // nullary-tag threshold AND clear of i64 overflow under +1 drift. Compile-time
    // invariants (mirrors heap.rs's `const _: () = assert!(...)` layout guards).
    const _: () = assert!(IMMORTAL_RC == 1i64 << 62);
    const _: () = assert!(IMMORTAL_RC > crate::heap::NULLARY_THRESHOLD_I64);
    // Never satisfies the free trigger (old==1) or the COW unique trigger (rc==1),
    // and stays clear of i64::MAX under bounded +1 drift.
    const _: () = assert!(IMMORTAL_RC != 1 && IMMORTAL_RC < i64::MAX - 1_000_000);
}
