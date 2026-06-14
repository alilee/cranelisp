# S82 harvest disposition — ring4_trace_taxonomy.rs + lenient.rs + v4_jit_reclaim.rs

- **Files:** `ring4_trace_taxonomy.rs` (599 LOC, 31), `lenient.rs` (302 LOC, 16), `v4_jit_reclaim.rs` (734 LOC, 6)
- **FIXMEs:** 0130 (trace), 0135 (lenient), 0133 (jit)
- **Prior audit:** none

## ring4_trace_taxonomy.rs (31) — FIXME 0130

- **Owner:** `cranelisp-typecheck` with co-owner **`cranelisp-intrinsics`**
  (trace bodies / `DisplayDescriptor`; post-D43 relabel — README says
  "/runtime", which no longer exists).

| Disposition | Count | Notes |
|---|---:|---|
| COVERED | 27 | trace type returns, children, root-name capture, field accessors (name/nanos), nested-trace error, composability via let/pattern-match, no-import availability, run-tests pass/fail/multiple/empty/mixed — `tests/trace.rs`, `tests/got_trace.rs`, `tests/spec_12_runtime.rs`, `tests/spec_04_expressions.rs`. (Includes 4 "COVERED-with-caveat" where the e2e witnesses the unwrapped value because internal `IO`/heap-pointer shapes can't cross the binary boundary — correctly closed by e2e.) |
| GAP | 4 | trace field type-shape assertions `(SList String)` / `Type::String` / `(SList Trace)` for params/result/children + trace-as-fn-arg inference → `cranelisp-typecheck` (co: intrinsics) `#[cfg(test)]` units |
| OBSOLETE | 0 | |

## lenient.rs (16) — FIXME 0135

- **Owner:** `cranelisp-backend` with co-owner **`cranelisp-primitives`**
  (post-D43 relabel — README says "/runtime").

| Disposition | Count | Notes |
|---|---:|---|
| COVERED | 11 | lenient-eval correctness: independent/dependent bindings, cheap-builtin threshold, min-two-sparkable, `CRANELISP_NO_LENIENT`, nested lets, mixed, heap-typed, closures, neg-literals-not-sparkable — `spec_04_expressions.rs` + `spec_12_runtime.rs` (carry-comments present in active files) |
| GAP | 5 | IO-scheduling `io_schedule_*` (Par node emission, sequential, data-dependent, ResourceSerial same/diff token) → `cranelisp-backend` (Par codegen) + `cranelisp-platform` (test-capture DLL classification). Not e2e-witnessable without the test-capture commutative/ResourceSerial fixture. |
| OBSOLETE | 0 | |

## v4_jit_reclaim.rs (6) — FIXME 0133

- **Owner:** `cranelisp-backend` (Arc/Jit reclaim; runtime counter atomics).

All 6 are pure GAP — no e2e equivalent; each asserts Rust-internal state
(`Arc::strong_count`, `jit_free_memory_call_count()`, `bytes_current()`,
`Code` enum shapes) unobservable at the binary boundary. **All 6 are
REGRESSION-GUARDs** (Decision-31 Scenario-1/2 reclaim + Wave-3b
carry-forward `register_defn_does_not_drop_existing_arc_jit`).

| Disposition | Count |
|---|---:|
| COVERED | 0 |
| GAP | 6 (all reg-guard) |
| OBSOLETE | 0 |

Harvest → `cranelisp-backend` `#[cfg(test)]` (Jit drop count, Arc
lifecycle); pre-Wave-3b would show unbounded reclaim accumulation / GOT
dangling on failed redef — durable regression guards.

## Summary

- **ring4_trace_taxonomy.rs: 31 tests: 27 covered / 4 gap / 0 obsolete** (0 reg-guard)
- **lenient.rs: 16 tests: 11 covered / 5 gap / 0 obsolete** (0 reg-guard)
- **v4_jit_reclaim.rs: 6 tests: 0 covered / 6 gap / 0 obsolete** (6 reg-guard)

## Exit checklist
- [x] (a) dispositioned; [ ] (b) GAP harvested (Wave 2); [ ] (c) deleted; [ ] (d) README rows; [ ] (e) FIXMEs 0130/0135/0133 closed
