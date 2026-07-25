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

// spec: 12-runtime §12.3 — last-use analysis for RC consuming calling convention
#[test]
fn test_compute_last_uses() {
    use cranelisp_types::{ConcreteType, MonoExpr, Span, Symbol};

    let x = Symbol::from("x");
    let var = |name: Symbol, span: Span| MonoExpr::Var {
        resolution: cranelisp_types::VarRef::Local {
            binder: name.clone(),
            binding_span: cranelisp_types::Span::SYNTHETIC,
        },
        name,
        span,
        resolved_call: None,
        ty: ConcreteType::Int,
    };
    let expr = MonoExpr::Apply {
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
        callee: Box::new(var(Symbol::from("f"), Span::new(0, 1))),
        args: vec![
            var(x.clone(), Span::new(2, 3)),
            var(x.clone(), Span::new(4, 5)),
        ],
        span: Span::new(0, 6),
        resolved_call: None,
        ty: ConcreteType::Int,
        confined: None,
        escapes: None,
        provenance: None,
        unique_static: None,
    };

    let last_uses = compute_last_uses(&expr);
    // First use of x is NOT last use.
    assert_eq!(last_uses.get(&(x.clone(), Span::new(2, 3))), Some(&false));
    // Second use of x IS last use.
    assert_eq!(last_uses.get(&(x.clone(), Span::new(4, 5))), Some(&true));
}

// spec: 12-runtime §12.3.3 — last-use must follow consumption order, not
// textual pre-order: a direct `Var` argument to a call is held until the
// call executes, so it outlives any use of the same var nested inside a
// SIBLING argument — even when that nested use is textually later. This is
// the seam of the DEF-2/T2 vec-push borrowed-recursive use-after-free:
// `(loop v (sub n 1) (... (vec-push v "z") ...))` — the direct `v` arg
// (span 2..3, occurrence #1) must be last-use; the nested `vec-push v`
// (span 10..11, occurrence #2) must NOT, so Vec COW takes the copy path
// instead of mutating the still-live `v` in place. Regression: a naive
// textual-last heuristic marks the nested use last and corrupts `v`.
#[test]
fn last_use_direct_arg_outlives_nested_sibling_arg() {
    use cranelisp_types::{ConcreteType, MonoExpr, Span, Symbol};

    let v = Symbol::from("v");
    let var = |name: Symbol, span: Span, ty: ConcreteType| MonoExpr::Var {
        resolution: cranelisp_types::VarRef::Local {
            binder: name.clone(),
            binding_span: cranelisp_types::Span::SYNTHETIC,
        },
        name,
        span,
        resolved_call: None,
        ty,
    };
    let vec_ty = ConcreteType::Int; // type is irrelevant to last-use ordering

    // (loop v (g) (h (vec-push v ...)))  modelled as nested Applys:
    //   callee = loop
    //   arg0   = v                      (direct Var, occurrence #1, span 2..3)
    //   arg1   = (g)                    (no v)
    //   arg2   = (h (push v))           v nested deep, occurrence #2, span 10..11
    let inner_push = MonoExpr::Apply {
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
        callee: Box::new(var(
            Symbol::from("vec-push"),
            Span::new(8, 9),
            vec_ty.clone(),
        )),
        args: vec![var(v.clone(), Span::new(10, 11), vec_ty.clone())],
        span: Span::new(7, 12),
        resolved_call: None,
        ty: vec_ty.clone(),
        confined: None,
        escapes: None,
        provenance: None,
        unique_static: None,
    };
    let arg2 = MonoExpr::Apply {
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
        callee: Box::new(var(Symbol::from("h"), Span::new(6, 7), vec_ty.clone())),
        args: vec![inner_push],
        span: Span::new(5, 13),
        resolved_call: None,
        ty: vec_ty.clone(),
        confined: None,
        escapes: None,
        provenance: None,
        unique_static: None,
    };
    let arg1 = MonoExpr::Apply {
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
        callee: Box::new(var(Symbol::from("g"), Span::new(4, 5), vec_ty.clone())),
        args: vec![],
        span: Span::new(4, 6),
        resolved_call: None,
        ty: vec_ty.clone(),
        confined: None,
        escapes: None,
        provenance: None,
        unique_static: None,
    };
    let expr = MonoExpr::Apply {
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
        callee: Box::new(var(Symbol::from("loop"), Span::new(0, 1), vec_ty.clone())),
        args: vec![var(v.clone(), Span::new(2, 3), vec_ty.clone()), arg1, arg2],
        span: Span::new(0, 14),
        resolved_call: None,
        ty: vec_ty,
        confined: None,
        escapes: None,
        provenance: None,
        unique_static: None,
    };

    let last_uses = compute_last_uses(&expr);
    // The direct recursive-call argument `v` is the LAST live use.
    assert_eq!(
        last_uses.get(&(v.clone(), Span::new(2, 3))),
        Some(&true),
        "direct call-arg occurrence of v must be last-use"
    );
    // The textually-later nested `(vec-push v ...)` use is NOT last-use.
    assert_eq!(
        last_uses.get(&(v.clone(), Span::new(10, 11))),
        Some(&false),
        "nested-in-sibling-arg occurrence of v must NOT be last-use"
    );
}

// spec: design/backend/ownership-codegen.md §6.3 — pure-SSA alias liveness. A
// `(let [w v …] …)` binding whose value is a bare `Var` makes `w` a second
// handle on `v`'s buffer, so a use of `w` must extend `v`'s live range. Without
// this, `v`'s use at an intervening `(vec-set v …)` is falsely marked last-use
// ⇒ in-place COW ⇒ the aliased `w` reads corrupted data (the discovered S103
// defect: exit 198 vs 109; e2e guard
// `tests/ownership_reuse.rs::l_c3_pure_ssa_alias_vec_set_preserves_value_semantics`).
// This unit pins the seam: `v`'s use at the `vec-set` span is NOT last-use, and
// `v`'s last-use is the alias's later body occurrence (propagated by the alias
// map in `compute_last_uses`).
#[test]
fn pure_ssa_alias_use_extends_root_live_range() {
    use cranelisp_types::{ConcreteType, MonoExpr, Span, Symbol};

    let v = Symbol::from("v");
    let w = Symbol::from("w");
    let vec_ty = ConcreteType::ADT(
        cranelisp_types::FQTypeName {
            module: cranelisp_types::ModuleFullPath::from("primitives"),
            name: cranelisp_types::TypeName::from("Vec"),
        },
        vec![ConcreteType::Int],
    );
    let var = |name: Symbol, span: Span, ty: ConcreteType| MonoExpr::Var {
        resolution: cranelisp_types::VarRef::Local {
            binder: name.clone(),
            binding_span: cranelisp_types::Span::SYNTHETIC,
        },
        name,
        span,
        resolved_call: None,
        ty,
    };
    let apply =
        |callee: Symbol, args: Vec<MonoExpr>, span: Span, ty: ConcreteType| MonoExpr::Apply {
            dispatch: cranelisp_types::ApplyRef::ViaCallee,
            callee: Box::new(var(
                callee,
                Span::new(span.start, span.start + 1),
                ty.clone(),
            )),
            args,
            span,
            resolved_call: None,
            ty,
            confined: None,
            escapes: None,
            provenance: None,
            unique_static: None,
        };

    // (let [v [10 20 30]                        ; VecLit
    //       w v                                 ; pure SSA alias, v use @ (30,31)
    //       v2 (vec-set v 0 99)]                ; v use @ (40,41), last binding use
    //   (add-i64 (vec-get w 0) (vec-get v2 0))) ; w use @ (60,61) → propagates to v
    let vlit = MonoExpr::VecLit {
        elements: vec![],
        span: Span::new(10, 11),
        ty: vec_ty.clone(),
        escapes: None,
        confined: None,
        unique_static: None,
    };
    let vec_set = apply(
        Symbol::from("vec-set"),
        vec![
            var(v.clone(), Span::new(40, 41), vec_ty.clone()),
            MonoExpr::IntLit {
                value: 0,
                span: Span::new(42, 43),
                ty: ConcreteType::Int,
            },
            MonoExpr::IntLit {
                value: 99,
                span: Span::new(44, 45),
                ty: ConcreteType::Int,
            },
        ],
        Span::new(39, 46),
        vec_ty.clone(),
    );
    let body = apply(
        Symbol::from("add-i64"),
        vec![
            apply(
                Symbol::from("vec-get"),
                vec![
                    var(w.clone(), Span::new(60, 61), vec_ty.clone()),
                    MonoExpr::IntLit {
                        value: 0,
                        span: Span::new(62, 63),
                        ty: ConcreteType::Int,
                    },
                ],
                Span::new(59, 64),
                ConcreteType::Int,
            ),
            apply(
                Symbol::from("vec-get"),
                vec![
                    var(Symbol::from("v2"), Span::new(70, 71), vec_ty.clone()),
                    MonoExpr::IntLit {
                        value: 0,
                        span: Span::new(72, 73),
                        ty: ConcreteType::Int,
                    },
                ],
                Span::new(69, 74),
                ConcreteType::Int,
            ),
        ],
        Span::new(50, 80),
        ConcreteType::Int,
    );
    let expr = MonoExpr::Let {
        bindings: vec![
            (v.clone(), vlit),
            (w.clone(), var(v.clone(), Span::new(30, 31), vec_ty.clone())),
            (Symbol::from("v2"), vec_set),
        ],
        body: Box::new(body),
        span: Span::new(0, 81),
        ty: ConcreteType::Int,
    };

    let last_uses = compute_last_uses(&expr);
    // v's use at the intervening vec-set is NOT last-use — the aliased w keeps
    // v's buffer live, so COW must take the copy path, not mutate in place.
    assert_eq!(
        last_uses.get(&(v.clone(), Span::new(40, 41))),
        Some(&false),
        "v's vec-set use must NOT be last-use — alias w keeps the buffer live"
    );
    // v's genuine last use is the alias occurrence in the body (propagated via w).
    assert_eq!(
        last_uses.get(&(v.clone(), Span::new(60, 61))),
        Some(&true),
        "v's last use is the alias w's body occurrence (propagated)"
    );
    // The alias binding occurrence of v is also not last-use.
    assert_eq!(last_uses.get(&(v.clone(), Span::new(30, 31))), Some(&false));
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
// B3.3 — per-site non-atomic RC for Confined cells
// (`design/backend/ownership-codegen.md` §5; §13.5 rc_emission/heap.rs matrix).
//
// Seam-level scenario matrix: {emit_rc_inc, emit_rc_inc_guarded, emit_rc_dec,
// emit_rc_dec_guarded, emit_vec_rc_dec_with_drop} × RcAtomicity → {non-atomic
// arm, atomic arm verbatim}. The negative (else-arm) class asserts the
// `Atomic` arm is CLIF-text-identical to the plain (pre-B3.3) helper — the
// §2.2 byte-identity discipline, which under `confined = Some(false) | None`
// (analysis off) is exactly what every call site emits.
// ===========================================================================
#[cfg(test)]
mod rc_atomicity_b33_tests {
    use crate::heap::{
        self, RcAtomicity, emit_rc_dec, emit_rc_dec_guarded, emit_rc_dec_guarded_atomicity,
        emit_rc_inc, emit_rc_inc_atomicity, emit_rc_inc_guarded, emit_rc_inc_guarded_atomicity,
        rc_emit_counts,
    };
    use crate::jit::Jit;
    use cranelift::prelude::*;
    use cranelift_module::Module;

    /// Build a one-arg function, run `emit` (given builder + module + the arg
    /// pointer), and return the CLIF text. The blessed harness mirror of
    /// `s99_emit_rc_inc_default_is_atomic_rmw_no_stat`.
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

    /// The non-atomic RC arm is a plain read-modify-write: it must contain the
    /// three-instruction `load` / `iadd`|`isub` / `store` sequence and NO
    /// `atomic_rmw` on the count. (The dec free path keeps its `fence`, but
    /// that is not `atomic_rmw`.)
    fn asserts_nonatomic(clif: &str, is_dec: bool) {
        assert!(
            !clif.contains("atomic_rmw"),
            "non-atomic arm must not emit atomic_rmw:\n{clif}"
        );
        assert!(
            clif.contains("load.i64"),
            "non-atomic arm must load the count:\n{clif}"
        );
        let op = if is_dec { "isub" } else { "iadd" };
        assert!(clif.contains(op), "non-atomic {op} arm missing:\n{clif}");
        assert!(
            clif.contains("store"),
            "non-atomic arm must store the count:\n{clif}"
        );
    }

    fn asserts_atomic(clif: &str) {
        assert!(
            clif.contains("atomic_rmw"),
            "atomic arm must emit atomic_rmw:\n{clif}"
        );
    }

    fn dealloc_id(module: &mut cranelift_jit::JITModule) -> cranelift_module::FuncId {
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        module
            .declare_function("runtime/dealloc", cranelift_module::Linkage::Import, &sig)
            .expect("declare dealloc")
    }

    // --- emit_rc_inc: {NonAtomic → non-atomic, Atomic → atomic} + else-arm id ---
    #[test]
    fn inc_confined_true_emits_nonatomic() {
        // spec: design/backend/ownership-codegen.md §5.1 — confined=Some(true) ⇒ non-atomic inc
        let clif = clif_of(|b, m, p| emit_rc_inc_atomicity(b, m, p, RcAtomicity::NonAtomic));
        asserts_nonatomic(&clif, false);
    }
    #[test]
    fn inc_crossing_and_absent_emit_atomic_verbatim() {
        // spec: design/backend/ownership-codegen.md §5.1 — Some(false)/None ⇒ atomic verbatim
        let atomic = clif_of(|b, m, p| emit_rc_inc_atomicity(b, m, p, RcAtomicity::Atomic));
        asserts_atomic(&atomic);
        // else-arm identity (§2.2): the plain helper == the Atomic-parameterised one.
        let plain = clif_of(|b, m, p| emit_rc_inc(b, m, p));
        assert_eq!(
            plain, atomic,
            "emit_rc_inc must equal emit_rc_inc_atomicity(Atomic) — §2.2 else-arm identity"
        );
    }

    // --- emit_rc_inc_guarded ---
    #[test]
    fn inc_guarded_confined_true_emits_nonatomic() {
        // spec: design/backend/ownership-codegen.md §5.2 — guarded inc gated per-site
        let clif =
            clif_of(|b, m, p| emit_rc_inc_guarded_atomicity(b, m, p, RcAtomicity::NonAtomic));
        asserts_nonatomic(&clif, false);
    }
    #[test]
    fn inc_guarded_atomic_is_else_arm_identity() {
        // spec: design/backend/ownership-codegen.md §2.2 — else-arm identity
        let atomic = clif_of(|b, m, p| emit_rc_inc_guarded_atomicity(b, m, p, RcAtomicity::Atomic));
        let plain = clif_of(|b, m, p| emit_rc_inc_guarded(b, m, p));
        asserts_atomic(&atomic);
        assert_eq!(plain, atomic);
    }

    // --- emit_rc_dec / emit_rc_dec_guarded ---
    #[test]
    fn dec_guarded_confined_true_emits_nonatomic() {
        // spec: design/backend/ownership-codegen.md §5.3 — non-atomic dec, free path kept
        let clif = clif_of(|b, m, p| {
            let d = dealloc_id(m);
            emit_rc_dec_guarded_atomicity(b, m, p, d, None, false, RcAtomicity::NonAtomic);
        });
        asserts_nonatomic(&clif, true);
        assert!(
            clif.contains("fence"),
            "non-atomic dec must keep the free-path fence:\n{clif}"
        );
    }
    #[test]
    fn dec_atomic_is_else_arm_identity() {
        // spec: design/backend/ownership-codegen.md §2.2 — plain emit_rc_dec == guarded(false, Atomic)
        let plain = clif_of(|b, m, p| {
            let d = dealloc_id(m);
            emit_rc_dec(b, m, p, d, None);
        });
        let atomic = clif_of(|b, m, p| {
            let d = dealloc_id(m);
            emit_rc_dec_guarded_atomicity(b, m, p, d, None, false, RcAtomicity::Atomic);
        });
        asserts_atomic(&atomic);
        assert_eq!(plain, atomic);
    }
    #[test]
    fn dec_guarded_atomic_is_else_arm_identity() {
        // spec: design/backend/ownership-codegen.md §2.2 — guarded dec else-arm identity
        let plain = clif_of(|b, m, p| {
            let d = dealloc_id(m);
            emit_rc_dec_guarded(b, m, p, d, None, true);
        });
        let atomic = clif_of(|b, m, p| {
            let d = dealloc_id(m);
            emit_rc_dec_guarded_atomicity(b, m, p, d, None, true, RcAtomicity::Atomic);
        });
        asserts_atomic(&atomic);
        assert_eq!(plain, atomic);
    }

    // --- the probe (CRANELISP_NONATOMIC_RC) shares the same non-atomic arm ---
    // NOTE: the probe is a process-global env read (OnceLock); it is exercised
    // end-to-end (excluded-from-canonical) rather than unit-forced here so the
    // OnceLock is not poisoned for sibling tests. The per-site gate and the
    // probe route through the SAME `use_nonatomic_arm` decision point (one
    // code path, two gates — Principle 7), verified by construction above.

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

    // --- the codegen-time non-atomic-op-share counter (h2 backend half) ---
    #[test]
    fn nonatomic_share_counter_tallies_emitted_ops() {
        // spec: design/backend/ownership-codegen.md §11 — backend-side counter
        let (na0, tot0) = rc_emit_counts();
        // One atomic inc: total++ , nonatomic unchanged.
        let _ = clif_of(|b, m, p| emit_rc_inc_atomicity(b, m, p, RcAtomicity::Atomic));
        let (na1, tot1) = rc_emit_counts();
        assert_eq!(tot1, tot0 + 1, "total RC-emit count must advance");
        assert_eq!(
            na1, na0,
            "an Atomic emit must NOT advance the non-atomic tally"
        );
        // One non-atomic inc: both advance.
        let _ = clif_of(|b, m, p| emit_rc_inc_atomicity(b, m, p, RcAtomicity::NonAtomic));
        let (na2, tot2) = rc_emit_counts();
        assert_eq!(tot2, tot1 + 1);
        assert_eq!(
            na2,
            na1 + 1,
            "a NonAtomic emit must advance the non-atomic tally"
        );
        let _ = heap::use_nonatomic_arm; // keep the shared decision point referenced
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
