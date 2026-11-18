use super::*;

// spec: 12-runtime §12.1.5 — Vec heap layout (len/cap/data_ptr at 16/24/32).
// The layout is intrinsics'; codegen's i32 offsets are its values.
#[test]
fn vec_codegen_offsets_are_the_intrinsics_layout() {
    assert_eq!(VEC_LEN_OFFSET, 16);
    assert_eq!(VEC_CAP_OFFSET, 24);
    assert_eq!(VEC_DATA_PTR_OFFSET, 32);
    assert_eq!(VEC_LEN_OFFSET as usize, vec_runtime::LEN_OFFSET);
    assert_eq!(VEC_CAP_OFFSET as usize, vec_runtime::CAP_OFFSET);
    assert_eq!(VEC_DATA_PTR_OFFSET as usize, vec_runtime::DATA_PTR_OFFSET);
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
        emit: impl FnOnce(&mut FunctionBuilder, &mut crate::jit::FarCallModule, Value),
    ) -> String {
        let mut jit = Jit::new_with_symbols(&[]).expect("jit construction");
        let module = jit.far_call_module();
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

    fn import(module: &mut crate::jit::FarCallModule, name: &str, params: usize) -> FuncId {
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
}
