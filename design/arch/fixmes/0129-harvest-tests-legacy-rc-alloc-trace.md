---
number: 0129
target: /qa
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/rc_alloc_trace.rs
status: open
harvested_by: /dev (S81, ported crate-internal RC-balance slice to cranelisp-intrinsics #[cfg(test)])
---

## S81 /dev harvest disposition (re-targeted to /qa for deletion)

The crate-internal "alloc count == dealloc count for every category of heap
value" slice is **ported** into a new `#[cfg(test)] mod rc_balance` in
`crates/cranelisp-intrinsics/src/drop.rs` — where the counters (`crate::alloc`)
and the drop glue actually live (the D43 runtime split routed the
allocator/RC/drop-glue here; there is no `cranelisp-runtime` to harvest into,
and `cranelisp-primitives` builds `SymbolTable<(),()>` with no runtime-counter
dependency per Decision 48, so it is NOT a counter home). The new module uses a
shared `assert_balanced` helper (the crate-internal analogue of the legacy
`assert_rc_balanced`) asserting **exact** parity through the real runtime drop
primitives, stronger than the legacy `>=` checks. New tests (10), one per
invariant cluster named in this FIXME:

- `rc_balance_adt_sum_with_string_field` — ADT sum heap field freed with container
- `rc_balance_adt_product_two_string_fields` — product, both fields freed
- `rc_balance_nested_recursive` — nested ADT recursive RC walk
- `rc_balance_closure_env` — closure environment freed
- `rc_balance_closure_captures_string` — single-capture env + capture freed (inline drop glue)
- `rc_balance_closure_multiple_captures` — multiple captures freed
- `rc_balance_vec_cow_set` — Vec COW: original + copy both freed (no double-free/leak)
- `rc_balance_vec_of_strings` — Vec element Strings freed with the Vec
- `rc_balance_consume_unused_string_param` — consuming convention: callee frees unused heap param
- `rc_balance_consume_multiple_unused_params` — multiple unused heap params freed

These complement the pre-existing per-primitive counter tests already in
`crates/cranelisp-intrinsics/src/{alloc,rc,drop,heap_string,vec_runtime}.rs`
`#[cfg(test)]` modules (which together already cover String/Vec/ADT/closure/IO
counter parity at the primitive level).

The whole-program `assert_rc_balanced` (stderr `CRANELISP_RC_TRACE=1` parsing)
form is the e2e tier; its language-observable property is preserved in
`tests/spec_12_runtime.rs` (heap-using bodies run cleanly).

**Remaining action (/qa):** delete `tests/legacy/rc_alloc_trace.rs` + remove its
row from `tests/legacy/README.md`. Crate-internal slice is fully ported (gate
green: `cargo nextest run -p cranelisp-intrinsics` 138 passed; canonical
`cargo nextest run` 1289 passed / 0 failed / 0 skipped). Left `status: open` —
the /qa deletion closes it.

# Harvest tests/legacy/rc_alloc_trace.rs into cranelisp-runtime + cranelisp-backend unit tests

## Issue

The Sprint 64 test-port quarantined `tests/legacy/rc_alloc_trace.rs` (1,191
LOC, 81 tests). The file uses two integration-tier helpers:

- `compile_and_run_simple(src)` — Rust-API pipeline driver returning the
  Int the program produced. ~43 tests use this shape.
- `assert_rc_balanced(src)` — runs the program with `CRANELISP_RC_TRACE=1`
  and parses stderr alloc/dealloc trace lines, asserting the totals match.
  ~38 tests use this shape.

The user-observable spec property (spec/12-runtime.md §12.3.1 — heap-using
programs run cleanly without leaks) is preserved as e2e tests in
`tests/spec_12_runtime.rs` (string alloc/drop, ADT product/sum, closure
captures, Vec COW). The Rust-internal portion — alloc/free counter parity
asserted via stderr trace parsing — has no e2e analogue and quarantines
for crate-side harvest.

## Proposed resolution

The trace-counter assertions split into two homes by where the counters
fire:

- **`cranelisp-runtime` `#[cfg(test)]`** — alloc/dealloc counters are owned
  by the runtime allocator. Translate `assert_rc_balanced` into a thin
  test helper that drives a small piece of generated code via the
  runtime's heap primitives directly, asserting the counter pair is
  balanced. The counters' atomic shape (`bytes_current`, `alloc_count`,
  `dealloc_count`) is the surface to assert on; the trace formatting
  (stderr line shape) is a debugging-aid concern that doesn't need
  preservation.

- **`cranelisp-backend` `#[cfg(test)]`** — drop-glue emission and
  consuming-call ABI live in the backend. The "ADT product alloc balanced
  on match unwrap" / "Vec COW preserves both old and new" / "closure env
  freed on capture drop" properties are best validated via backend unit
  tests that compile small ASTs and inspect the emitted CLIF (or run the
  compiled function in a test JIT) for the expected drop-glue signature.

The 81 source tests do not need to translate 1:1 — many duplicate
coverage (see the original file's organisation by type: ~12 string, ~12
ADT, ~10 closure, ~10 Vec, plus Sprint-NN-specific reduction batches).
Pick representatives for each invariant cluster:

- String alloc/dealloc balance (1 test)
- ADT heap field freed with container (1 product, 1 sum)
- Closure environment freed (1 capture, 1 multiple-capture)
- Vec COW preserves alloc count when both old and new accessed (1 test)
- Lambda unused-heap-param freed (D3 / Sprint 18 cohort, ~3 tests)
- Nested ADT (Option(Option(...))) recursive RC (1-2 tests)

Aim for ~12-15 unit tests covering the spec property "alloc count ==
dealloc count for every category of heap value".

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. Until it
lands, the trace-counter portion is inert (the file is not compiled).
The user-observable spec property is covered by `tests/spec_12_runtime.rs`
and the e2e test suite as a whole (every passing test that exercises
heap values is implicitly an RC balance assertion — leaks would surface
as memory pressure in long-running tests; double-frees would crash the
process).

Per FIXMEs 0098-0103 + Decisions 38-42, the runtime/backend boundary may
shift in S65+. The harvest target follows the counter location at the
time of harvest.

When complete, delete `tests/legacy/rc_alloc_trace.rs` and remove its
row from `tests/legacy/README.md`. Git history preserves provenance.
