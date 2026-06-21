use super::*;

// ── Trace machinery basics (relocated from int) ──────────────────────────

#[test]
fn test_current_thread_id_stable() {
    let id1 = current_thread_id();
    let id2 = current_thread_id();
    assert_eq!(id1, id2, "thread ID must be stable across calls");
}

#[test]
fn test_alloc_adt_creates_valid_heap() {
    let adt = alloc_adt(TAG_TRACE_CALL, &[100, 200, 300, 400, 500]);
    assert!(adt != 0, "allocation must return non-null");
    let tag = unsafe { read_i64(adt, PAYLOAD_OFFSET) };
    assert_eq!(tag, TAG_TRACE_CALL);
    let f0 = unsafe { read_i64(adt, FIELD0_OFFSET) };
    assert_eq!(f0, 100);
    let f4 = unsafe { read_i64(adt, FIELD0_OFFSET + 4 * 8) };
    assert_eq!(f4, 500);
}

#[test]
fn test_build_runtime_list_empty() {
    let list = build_runtime_list(&[]);
    assert_eq!(list, TAG_SNIL);
}

#[test]
fn test_build_runtime_list_items() {
    let list = build_runtime_list(&[10, 20, 30]);
    assert!(list >= NULLARY_THRESHOLD, "list head should be heap pointer");
    let tag = unsafe { read_i64(list, PAYLOAD_OFFSET) };
    assert_eq!(tag, TAG_SCONS);
    let head = unsafe { read_i64(list, FIELD0_OFFSET) };
    assert_eq!(head, 10);
}

// ── Nested-trace guard state machine (testable without JIT) ───────────────

#[test]
fn nested_guard_multi_module_swap_allowed() {
    // Simulate role-acquire on this thread, then a SECOND swap by the same
    // thread BEFORE any wrapper fires (TRACE_BODY_RUNNING == false). The
    // second swap must NOT raise (it returns a real saved-GOT, not the
    // sentinel-on-panic path).
    let my_tid = current_thread_id();
    // Acquire the role directly (mimicking a successful first swap).
    TRACE_THREAD_ID.store(my_tid, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));

    // A real swap needs a GOT + slot/wrapper arrays; build minimal ones.
    let mut got = vec![0i64; GOT_TABLE_SIZE];
    let slots: Vec<u32> = vec![0];
    let wrappers: Vec<i64> = vec![0xdead];
    let saved = cranelisp_trace_swap_got(
        got.as_mut_ptr() as i64,
        1,
        slots.as_ptr() as i64,
        wrappers.as_ptr() as i64,
    );
    // Legitimate multi-module swap returns a real (non-sentinel) saved-GOT.
    assert_ne!(saved, SENTINEL_SAVED_GOT, "multi-module swap must proceed");
    cranelisp_trace_restore_got(got.as_mut_ptr() as i64, saved);

    // Cleanup: release role + flag.
    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));
    let _ = crate::panic::take_runtime_error();
}

#[test]
fn nested_guard_reentrant_raises() {
    // Simulate role-acquired + body running (a wrapper has fired), then an
    // inner swap by the SAME thread. This is (trace (trace ...)) and must
    // raise via runtime_panic (returning the sentinel).
    let my_tid = current_thread_id();
    TRACE_THREAD_ID.store(my_tid, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(true));
    let _ = crate::panic::take_runtime_error(); // clear any prior

    let mut got = vec![0i64; GOT_TABLE_SIZE];
    let slots: Vec<u32> = vec![0];
    let wrappers: Vec<i64> = vec![0xbeef];
    let saved = cranelisp_trace_swap_got(
        got.as_mut_ptr() as i64,
        1,
        slots.as_ptr() as i64,
        wrappers.as_ptr() as i64,
    );
    assert_eq!(saved, SENTINEL_SAVED_GOT, "re-entrant swap must not proceed");
    let err = crate::panic::take_runtime_error();
    assert!(err.is_some(), "re-entrant swap must raise a runtime error");
    assert!(
        err.unwrap().contains("nested trace is not supported"),
        "guard message must name nested trace"
    );

    // Cleanup.
    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));
}

// spec: spec/04-expressions.md §4.12.5 — LEXICAL nested trace
// `(trace (trace e))` must raise even though no wrapper has fired (so
// TRACE_BODY_RUNNING is still false). FIXME 0283. The inner form re-swaps a
// GOT base the outer form already swapped; the already-swapped-base check
// catches it where the boundary flag misses it.
#[test]
fn nested_guard_lexical_reentrant_raises() {
    // Start clean on this thread.
    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));
    SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());
    let _ = crate::panic::take_runtime_error();

    let mut got = vec![0i64; GOT_TABLE_SIZE];
    let base = got.as_mut_ptr() as i64;
    let slots: Vec<u32> = vec![0];
    let wrappers: Vec<i64> = vec![0xfeed];

    // Outer form's swap: claims the role, records `base`.
    let outer_saved = cranelisp_trace_swap_got(
        base,
        1,
        slots.as_ptr() as i64,
        wrappers.as_ptr() as i64,
    );
    assert_ne!(outer_saved, SENTINEL_SAVED_GOT, "outer swap must proceed");
    // CRITICAL: no wrapper has fired, so the boundary flag is still false —
    // this is exactly the lexical-nesting condition the old guard missed.
    assert!(
        !TRACE_BODY_RUNNING.with(Cell::get),
        "precondition: lexical case has body_running == false"
    );

    // Inner form's swap of the SAME base while the role is held: re-entrant.
    let inner_saved = cranelisp_trace_swap_got(
        base,
        1,
        slots.as_ptr() as i64,
        wrappers.as_ptr() as i64,
    );
    assert_eq!(
        inner_saved, SENTINEL_SAVED_GOT,
        "lexical re-entrant swap must NOT proceed"
    );
    let err = crate::panic::take_runtime_error();
    assert!(
        err.as_deref()
            .is_some_and(|m| m.contains("nested trace is not supported")),
        "lexical nested trace must raise the nested-trace error; got {err:?}"
    );

    // Cleanup: restore the outer swap + release role/flag/set.
    cranelisp_trace_restore_got(base, outer_saved);
    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));
    SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());
}

// A legitimate two-MODULE swap of ONE form uses two DISTINCT got bases and
// must proceed for both (the multi-module case the lexical guard must not
// false-positive on). FIXME 0283.
#[test]
fn nested_guard_two_distinct_bases_allowed() {
    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));
    SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());
    let _ = crate::panic::take_runtime_error();

    let mut got_a = vec![0i64; GOT_TABLE_SIZE];
    let mut got_b = vec![0i64; GOT_TABLE_SIZE];
    let base_a = got_a.as_mut_ptr() as i64;
    let base_b = got_b.as_mut_ptr() as i64;
    let slots: Vec<u32> = vec![0];
    let wrappers: Vec<i64> = vec![0xcafe];

    let saved_a = cranelisp_trace_swap_got(
        base_a, 1, slots.as_ptr() as i64, wrappers.as_ptr() as i64,
    );
    let saved_b = cranelisp_trace_swap_got(
        base_b, 1, slots.as_ptr() as i64, wrappers.as_ptr() as i64,
    );
    assert_ne!(saved_a, SENTINEL_SAVED_GOT, "first module swap must proceed");
    assert_ne!(saved_b, SENTINEL_SAVED_GOT, "second module swap must proceed");
    assert!(
        crate::panic::take_runtime_error().is_none(),
        "distinct-base multi-module swap must NOT raise"
    );

    cranelisp_trace_restore_got(base_b, saved_b);
    cranelisp_trace_restore_got(base_a, saved_a);
    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));
    SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());
}

#[test]
fn enter_sets_body_running_collect_clears() {
    // enter (when we own the role) raises TRACE_BODY_RUNNING;
    // collect_trace clears it.
    let my_tid = current_thread_id();
    TRACE_THREAD_ID.store(my_tid, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));
    // Push a root frame so collect has something to pop.
    lock_trace_stack().push(TraceFrame {
        name: "::trace::".to_string(),
        params: vec![],
        result: 0,
        start: Instant::now(),
        children: vec![],
    });

    let name = "f";
    cranelisp_trace_enter(name.as_ptr() as i64, name.len() as i64, 0, 0);
    assert!(TRACE_BODY_RUNNING.with(Cell::get), "enter must raise the flag");
    // Pop the frame enter pushed.
    let _ = cranelisp_trace_exit(0, alloc_string(b"") as i64);

    let t = cranelisp_collect_trace();
    assert!(!TRACE_BODY_RUNNING.with(Cell::get), "collect must clear the flag");
    consume_trace_call(t);

    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
}

// ── 0340 capture-fidelity durable guard (intrinsics-side; FIXME 0340) ─────
//
// The 0340 "degenerate capture" symptom — `(Trace.TraceCall "::trace::" SNil
// …)` — is a NON-DEFECT in intrinsics. It was reproduced tracing `add-i64`,
// an inline-CLIF primitive with NO GOT slot: it is never wrapped, so its
// enter/exit wrappers never fire, the trace body adds no child frame, and
// `cranelisp_collect_trace` over the bare synthetic root yields the faithful
// empty shape. The 12 trace bodies capture name+operands CORRECTLY whenever
// a wrapper fires; this guard pins that fact at the enter→exit→collect seam
// so a future refactor cannot silently regress correct capture into the
// degenerate shape and re-attribute 0340 to intrinsics.
//
// Driven directly (no codegen) for a SIMULATED GOT-slotted callee: we play
// the exact sequence backend's wrapper emits — claim the role + push the
// synthetic root (as the first `swap_got` does), then `enter` with a real
// name + pre-formatted param Strings, then `exit` with a result String, then
// `collect`. The marshalled root must carry ONE child whose TraceCall NAMES
// the call (not "::trace::") and whose `tparams` is a non-empty SList (not
// SNil) — the load-bearing facts the degenerate shape lacks.
//
// spec: spec/04-expressions.md §4.12.3 — `(trace expr)` captures the traced
// call's name + operands.
#[test]
fn capture_fidelity_got_slotted_callee_names_call_and_carries_operands() {
    let my_tid = current_thread_id();
    // Clean start.
    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));
    let _ = crate::panic::take_runtime_error();

    // Claim the role + push the synthetic root frame exactly as the first
    // `cranelisp_trace_swap_got` does for a GOT-slotted module.
    TRACE_THREAD_ID.store(my_tid, Ordering::SeqCst);
    lock_trace_stack().push(TraceFrame {
        name: "::trace::".to_string(),
        params: vec![],
        result: 0,
        start: Instant::now(),
        children: vec![],
    });

    // The wrapper for a GOT-slotted callee fires `enter` with the call's
    // real name and its pre-formatted operand Strings, then `exit` with the
    // pre-formatted result String. Simulate tracing `(user/add 2 3) => 5`.
    let name = "user/add";
    let p0 = alloc_string(b"2") as i64;
    let p1 = alloc_string(b"3") as i64;
    let params_array: [i64; 2] = [p0, p1];
    cranelisp_trace_enter(
        name.as_ptr() as i64,
        name.len() as i64,
        2,
        params_array.as_ptr() as i64,
    );
    let result_str = alloc_string(b"5") as i64;
    let _ = cranelisp_trace_exit(0, result_str);

    // Collect the root: it should now hold the child TraceCall the wrapper
    // produced.
    let root = cranelisp_collect_trace();

    // The ROOT names "::trace::" with no operands (that's the synthetic
    // root — faithful), but its tchildren must hold the captured call.
    let root_children = unsafe { read_i64(root, TRACE_TCHILDREN_OFFSET) };
    assert!(
        root_children >= NULLARY_THRESHOLD,
        "root must have a child (the GOT-slotted callee was captured)"
    );
    let scons_tag = unsafe { read_i64(root_children, PAYLOAD_OFFSET) };
    assert_eq!(scons_tag, TAG_SCONS, "tchildren must be a non-empty SList");
    let child = unsafe { read_i64(root_children, FIELD0_OFFSET) };

    // FIDELITY 1: the child NAMES the call — NOT the "::trace::" placeholder.
    let child_name_heap = unsafe { read_i64(child, TRACE_TNAME_OFFSET) };
    let child_name =
        unsafe { crate::heap_string::read_string_as_str(child_name_heap) };
    assert_eq!(
        child_name, "user/add",
        "captured TraceCall must name the traced call, not the placeholder"
    );
    assert_ne!(
        child_name, "::trace::",
        "captured call name must NOT be the degenerate placeholder"
    );

    // FIDELITY 2: operands captured — tparams is a non-empty SList, NOT SNil.
    let child_params = unsafe { read_i64(child, TRACE_TPARAMS_OFFSET) };
    assert!(
        child_params >= NULLARY_THRESHOLD,
        "captured tparams must be a heap SList, not SNil (operands captured)"
    );
    assert_ne!(
        child_params, TAG_SNIL,
        "captured tparams must NOT be the degenerate empty SNil"
    );
    let params_tag = unsafe { read_i64(child_params, PAYLOAD_OFFSET) };
    assert_eq!(params_tag, TAG_SCONS, "tparams SList must have an operand");
    let first_param = unsafe { read_i64(child_params, FIELD0_OFFSET) };
    let first_param_str =
        unsafe { crate::heap_string::read_string_as_str(first_param) };
    assert_eq!(first_param_str, "2", "first operand must be captured verbatim");

    // Release ownership (consume the marshalled tree).
    consume_trace_call(root);
    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));
}

// Companion guard: `cranelisp_collect_trace` over an EMPTY stack returns the
// `::trace::` / SNil node. This is the INTENDED faithful shape for a trace
// whose body fired no wrapper (e.g. tracing an inline-CLIF primitive with no
// GOT slot, like `add-i64` — the exact shape 0340 mistook for a defect). An
// empty trace is NOT a bug: with no wrapped call there is nothing to name or
// capture, so the synthetic-root placeholder + empty operands is correct.
//
// spec: spec/04-expressions.md §4.12.3 — a trace over an un-wrappable call
// faithfully captures nothing.
#[test]
fn empty_trace_yields_faithful_placeholder_not_a_defect() {
    // Ensure a clean (empty) stack + no role held on this thread.
    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));
    {
        // Drain any residue so collect hits the empty-stack fallback.
        lock_trace_stack().clear();
    }

    let root = cranelisp_collect_trace();

    // Name is the synthetic placeholder — faithful, NOT degenerate-by-bug.
    let name_heap = unsafe { read_i64(root, TRACE_TNAME_OFFSET) };
    let name = unsafe { crate::heap_string::read_string_as_str(name_heap) };
    assert_eq!(
        name, "::trace::",
        "empty-stack collect intentionally yields the synthetic placeholder"
    );
    // Operands + children are empty SNil — the faithful shape for a trace
    // that wrapped nothing. (This is the 0340 symptom shape; it is CORRECT
    // here because no GOT-slotted call was traced.)
    let params = unsafe { read_i64(root, TRACE_TPARAMS_OFFSET) };
    assert_eq!(params, TAG_SNIL, "empty-trace operands are faithfully SNil");
    let children = unsafe { read_i64(root, TRACE_TCHILDREN_OFFSET) };
    assert_eq!(children, TAG_SNIL, "empty-trace children are faithfully SNil");

    consume_trace_call(root);
}

// spec: spec/04-expressions.md §4.12.5 — panic-unwind trace-guard cleanup
// (0258 NOTE-2 / test-discovery.md §5 item 5). Simulate a panic crossing an
// actively-tracing body: role held + TRACE_BODY_RUNNING set. The cleanup
// must clear the flag AND release the role so the next trace starts clean.
#[test]
fn panic_clears_stuck_trace_guard() {
    let my_tid = current_thread_id();
    TRACE_THREAD_ID.store(my_tid, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(true));

    clear_trace_guard_on_panic();

    assert!(
        !TRACE_BODY_RUNNING.with(Cell::get),
        "cleanup must clear TRACE_BODY_RUNNING after a mid-trace panic"
    );
    assert_eq!(
        TRACE_THREAD_ID.load(Ordering::Relaxed),
        0,
        "cleanup must release the trace role after a mid-trace panic"
    );
}

// The cleanup must NOT steal a role owned by another thread: if this thread
// does not own the role, the CAS no-ops and the foreign owner is preserved.
#[test]
fn panic_cleanup_does_not_steal_foreign_role() {
    // A foreign owner id distinct from this thread's id.
    let foreign = current_thread_id() + 100_000;
    TRACE_THREAD_ID.store(foreign, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));

    clear_trace_guard_on_panic();

    assert_eq!(
        TRACE_THREAD_ID.load(Ordering::Relaxed),
        foreign,
        "cleanup must not release a role owned by another thread"
    );
    // Restore for other tests.
    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
}

// ── 0130 harvest: Trace ADT field-accessor offset + RC fidelity ───────────
//
// These are the intrinsics-owned trace-body-runtime slice of the legacy
// `ring4_trace_taxonomy.rs` GAPs (FIXME 0130). The legacy file asserted the
// *type-shape* of each accessor (`name : String`, `params : (SList String)`,
// …) — that slice is typecheck's (done). The RUNTIME behaviour of the five
// `cranelisp_trace_*` accessor bodies — that each reads its field at the
// correct TraceCall offset, returns the stored field value, RC-incs heap
// fields (so the returned reference is independent of the parent), and
// consumes the TraceCall under the Decision-24 convention — lives here and
// was not exercised by any prior unit (the W2 guards cover swap/guard/empty,
// not the accessors) nor by `tests/trace.rs` (the e2e witnesses the unwrapped
// value, not the offset/RC fidelity of the accessor body).

/// Read the RC field (offset 8) of a heap value.
fn read_rc(ptr: i64) -> i64 {
    unsafe { read_i64(ptr, HeapHeader::RC_OFFSET as usize) }
}

/// Build a fully-populated TraceCall ADT (heap String name, two-operand
/// String SList, String result, one-child SList, nanos) and return its base
/// pointer plus the heap field pointers the accessors should read back.
fn build_populated_trace_call() -> (i64, i64, i64, i64, i64, i64) {
    let p0 = alloc_string(b"2") as i64;
    let p1 = alloc_string(b"3") as i64;
    let result = alloc_string(b"5") as i64;
    // One child TraceCall so tchildren is a non-empty SList.
    let child = build_trace_call(
        TraceFrame {
            name: "child".to_string(),
            params: vec![],
            result: 0,
            start: Instant::now(),
            children: vec![],
        },
        7,
    );
    let frame = TraceFrame {
        name: "user/add".to_string(),
        params: vec![p0, p1],
        result,
        start: Instant::now(),
        children: vec![child],
    };
    let trace = build_trace_call(frame, 4242);
    // Read back the stored heap field ptrs the accessors must return.
    let name = unsafe { read_i64(trace, TRACE_TNAME_OFFSET) };
    let params = unsafe { read_i64(trace, TRACE_TPARAMS_OFFSET) };
    let res = unsafe { read_i64(trace, TRACE_TRESULT_OFFSET) };
    let children = unsafe { read_i64(trace, TRACE_TCHILDREN_OFFSET) };
    let nanos = unsafe { read_i64(trace, TRACE_TNANOS_OFFSET) };
    (trace, name, params, res, children, nanos)
}

// spec: spec/04-expressions.md §4.12.4 — `name` reads the tname field at the
// correct offset, returns it, RC-incs it (Decision 24), and consumes the
// TraceCall.
#[test]
fn accessor_name_reads_offset_and_rc_incs_field() {
    let (trace, name, params, result, children, _nanos) =
        build_populated_trace_call();
    let rc_before = read_rc(name);

    let got = cranelisp_trace_name(trace);

    // Correct offset: the returned value IS the stored tname ptr.
    assert_eq!(got, name, "name must read the tname field at offset 24");
    // Decision-24 consuming convention: the accessor RC-incs the field (so
    // the returned reference is independent of the parent) and THEN consumes
    // the TraceCall — whose last-ref drop dec's the field. Net field rc is
    // unchanged (+1 inc, -1 parent-drop), and the returned reference is now
    // the sole live owner (the value is NOT freed).
    assert_eq!(
        read_rc(got),
        rc_before,
        "field rc net-unchanged: +1 accessor inc, -1 parent consume (Decision 24)"
    );
    // Content fidelity.
    assert_eq!(unsafe { crate::heap_string::read_string_as_str(got) }, "user/add");

    // The TraceCall was consumed (rc 1 -> 0 -> freed); the returned name
    // survives because of the inc. Drop the remaining fields + the name's
    // extra ref to balance.
    unsafe { crate::alloc::dealloc(got as *mut u8) }; // the inc'd ref
    // params/result/children were dropped by consume_trace_call; nothing
    // else to free.
    let _ = (params, result, children);
}

// spec: spec/04-expressions.md §4.12.4 — `params` reads tparams (offset 32),
// RC-incs the SList head, consumes the TraceCall.
#[test]
fn accessor_params_reads_offset_and_rc_incs_field() {
    let (trace, name, params, result, children, _nanos) =
        build_populated_trace_call();
    let rc_before = read_rc(params);

    let got = cranelisp_trace_params(trace);

    assert_eq!(got, params, "params must read the tparams field at offset 32");
    assert_eq!(
        read_rc(got),
        rc_before,
        "SList-head rc net-unchanged: +1 accessor inc, -1 parent consume"
    );
    // It is a non-empty SList (SCons).
    assert_eq!(unsafe { read_i64(got, PAYLOAD_OFFSET) }, TAG_SCONS);

    // Balance: consume the inc'd SList ref (the TraceCall consumed the
    // original). The SList holds two String heads.
    consume_slist_of_string(got);
    let _ = (name, result, children);
}

// spec: spec/04-expressions.md §4.12.4 — `result` reads tresult (offset 40),
// RC-incs it, consumes the TraceCall.
#[test]
fn accessor_result_reads_offset_and_rc_incs_field() {
    let (trace, name, params, result, children, _nanos) =
        build_populated_trace_call();
    let rc_before = read_rc(result);

    let got = cranelisp_trace_result(trace);

    assert_eq!(got, result, "result must read the tresult field at offset 40");
    assert_eq!(
        read_rc(got),
        rc_before,
        "heap-String rc net-unchanged: +1 accessor inc, -1 parent consume"
    );
    assert_eq!(unsafe { crate::heap_string::read_string_as_str(got) }, "5");

    unsafe { crate::alloc::dealloc(got as *mut u8) }; // the inc'd ref
    let _ = (name, params, children);
}

// spec: spec/04-expressions.md §4.12.4 — `children` reads tchildren
// (offset 48), RC-incs the SList head, consumes the TraceCall.
#[test]
fn accessor_children_reads_offset_and_rc_incs_field() {
    let (trace, name, params, result, children, _nanos) =
        build_populated_trace_call();
    let rc_before = read_rc(children);

    let got = cranelisp_trace_children(trace);

    assert_eq!(
        got, children,
        "children must read the tchildren field at offset 48"
    );
    assert_eq!(
        read_rc(got),
        rc_before,
        "SList-head rc net-unchanged: +1 accessor inc, -1 parent consume"
    );
    assert_eq!(unsafe { read_i64(got, PAYLOAD_OFFSET) }, TAG_SCONS);

    consume_slist_of_trace(got); // balance the inc'd ref
    let _ = (name, params, result);
}

// spec: spec/04-expressions.md §4.12.4 — `nanos` reads tnanos (offset 56) as
// a bare Int (no RC-inc — payload is not heap-typed) and consumes the
// TraceCall.
#[test]
fn accessor_nanos_reads_offset_no_rc_inc() {
    let (trace, _name, _params, _result, _children, nanos) =
        build_populated_trace_call();
    assert_eq!(nanos, 4242, "tnanos stored at offset 56");

    let got = cranelisp_trace_nanos(trace);

    assert_eq!(got, 4242, "nanos must read the tnanos Int field at offset 56");
    // The TraceCall was consumed; all heap fields freed. Nothing survives
    // (nanos is a bare Int, not RC-managed).
}

// spec: spec/04-expressions.md §4.12.4 + appendix-a-builtins — the /run-tests
// helper `cranelisp_trace_first_child_nanos` walks tchildren -> first SCons
// head -> that child's tnanos (offset 56), then consumes the root under the
// Decision-24 convention. Build a root whose single child carries a known
// nanos value.
#[test]
fn first_child_nanos_walks_slist_to_child_tnanos() {
    let child = build_trace_call(
        TraceFrame {
            name: "child".to_string(),
            params: vec![],
            result: 0,
            start: Instant::now(),
            children: vec![],
        },
        999,
    );
    let root = build_trace_call(
        TraceFrame {
            name: "::trace::".to_string(),
            params: vec![],
            result: 0,
            start: Instant::now(),
            children: vec![child],
        },
        1,
    );

    let got = cranelisp_trace_first_child_nanos(root);
    assert_eq!(got, 999, "must return the first child's tnanos");
    // Root (and its child) consumed by the accessor.
}

// spec: spec/04-expressions.md §4.12.4 — first_child_nanos over a childless
// root returns 0 (SNil tchildren) and still consumes the root.
#[test]
fn first_child_nanos_empty_children_returns_zero() {
    let root = build_trace_call(
        TraceFrame {
            name: "::trace::".to_string(),
            params: vec![],
            result: 0,
            start: Instant::now(),
            children: vec![],
        },
        1,
    );
    assert_eq!(
        cranelisp_trace_first_child_nanos(root),
        0,
        "no children -> 0"
    );
}

// ── 0130 harvest: ::skipped:: concurrent-skip sentinel ────────────────────
//
// `tracing.md` §thread-safety: when a DIFFERENT thread already owns the trace
// role, `cranelisp_trace_swap_got` does NOT swap — it pushes a `::skipped::`
// sentinel frame and returns SENTINEL_SAVED_GOT (the concurrent-trace skip).
// This is the `current_owner != my_tid` branch; the W2 guards cover only the
// same-thread (`current_owner == my_tid`) branches. Simulate a foreign owner
// and assert the skip path. `restore_got` on the sentinel is a no-op.
//
// spec: spec/04-expressions.md §4.12.5 — concurrent trace on another thread
// is skipped, not nested.
#[test]
fn concurrent_foreign_owner_skips_with_sentinel() {
    // Install a FOREIGN owner (distinct from this thread's id).
    let foreign = current_thread_id() + 100_000;
    TRACE_THREAD_ID.store(foreign, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));
    let stack_depth_before = lock_trace_stack().len();
    let _ = crate::panic::take_runtime_error();

    let mut got = vec![0i64; GOT_TABLE_SIZE];
    let base = got.as_mut_ptr() as i64;
    let slots: Vec<u32> = vec![0];
    let wrappers: Vec<i64> = vec![0xabcd];

    let saved = cranelisp_trace_swap_got(
        base,
        1,
        slots.as_ptr() as i64,
        wrappers.as_ptr() as i64,
    );

    // Skipped: returns the sentinel, does NOT touch the GOT, does NOT raise.
    assert_eq!(
        saved, SENTINEL_SAVED_GOT,
        "concurrent foreign-owned trace must return the skip sentinel"
    );
    assert_eq!(got[0], 0, "skipped swap must NOT install a wrapper into the GOT");
    assert!(
        crate::panic::take_runtime_error().is_none(),
        "concurrent skip is NOT an error (distinct from same-thread nesting)"
    );

    // A `::skipped::` sentinel frame was pushed.
    let mut stack = lock_trace_stack();
    assert_eq!(
        stack.len(),
        stack_depth_before + 1,
        "skip must push exactly one sentinel frame"
    );
    assert_eq!(
        stack.last().map(|f| f.name.as_str()),
        Some("::skipped::"),
        "the pushed sentinel frame must be named ::skipped::"
    );
    stack.pop(); // remove our sentinel
    drop(stack);

    // restore_got on the sentinel is a no-op (does not touch the GOT).
    cranelisp_trace_restore_got(base, SENTINEL_SAVED_GOT);
    assert_eq!(got[0], 0, "restore on sentinel must be a no-op");

    // Restore global state.
    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
}

// spec: spec/04-expressions.md §4.12.2 — the synthetic ROOT frame on
// role-acquire is named `::trace::` (distinct from the `::skipped::`
// sentinel). First swap by an unowned thread claims the role and pushes the
// `::trace::` root.
#[test]
fn first_swap_pushes_trace_root_frame() {
    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));
    SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());
    lock_trace_stack().clear();
    let _ = crate::panic::take_runtime_error();

    let mut got = vec![0i64; GOT_TABLE_SIZE];
    let base = got.as_mut_ptr() as i64;
    let slots: Vec<u32> = vec![0];
    let wrappers: Vec<i64> = vec![0x1234];

    let saved = cranelisp_trace_swap_got(
        base,
        1,
        slots.as_ptr() as i64,
        wrappers.as_ptr() as i64,
    );
    assert_ne!(saved, SENTINEL_SAVED_GOT, "first swap claims the role");
    assert_eq!(
        got[0], 0x1234,
        "first swap installs the wrapper into the GOT slot"
    );
    // The synthetic root frame is named ::trace:: (NOT ::skipped::).
    {
        let stack = lock_trace_stack();
        assert_eq!(
            stack.last().map(|f| f.name.as_str()),
            Some("::trace::"),
            "role-acquire pushes the ::trace:: synthetic root"
        );
    }

    // Cleanup.
    cranelisp_trace_restore_got(base, saved);
    lock_trace_stack().clear();
    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());
}
