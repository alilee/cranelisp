# Sprint 61 Wave 1 Slice 0 — /review Report

**Reviewer**: /review
**Date**: 2026-04-22
**Verdict**: **PASS WITH FINDINGS**
**Scope**: Observability infrastructure — scheduler/worker event log
(`src/observability.rs`) + IO trampoline event log
(`crates/cranelisp-runtime/src/io_trace.rs`) + instrumentation call sites
in `src/scheduler.rs`, `src/worker.rs`, `src/session_v4.rs`,
`crates/cranelisp-runtime/src/io.rs`; shared `Instant` anchor; RAII
flush guards; panic hooks; 19 integration tests under
`tests/sprint61_observability_*.rs`.

## Summary

- Blockers: 0
- Importants: 1
- Suggestions: 4

All 13 review dimensions checked. No architectural drift, no
boundary-type leakage, no `cranelisp_alloc` in trace paths, no
`#[ignore]` in integration tests, no new `unwrap()` in pipeline code.
Design-doc adherence is strong on both sides. One Important finding on
test robustness: two sibling unit tests each call
`reset_panic_hook_installed_for_tests()` which mutates process-global
state and can desync an adjacent test running concurrently in the same
test binary (nextest runs each `#[test]` in its own process, but that is
a property of the runner, not of the test). Suggestions are minor
polish.

## Blockers (B)

None.

## Importants (I)

1. **`src/observability.rs:1027–1080` + `crates/cranelisp-runtime/src/io_trace.rs:884–942` — `reset_panic_hook_installed_for_tests()` mutates process-global state without a synchronisation lock.**

   Two unit tests (`install_panic_hook_is_idempotent`,
   `install_panic_hook_runs_flush_on_panic`) each call
   `reset_panic_hook_installed_for_tests()` at entry *and* exit to
   force the install-once guard to re-arm. Inside a single test binary
   `cargo test` (i.e. NOT nextest) runs `#[test]`s concurrently on a
   thread pool by default. If a sibling test in the same file ever
   depends on the `AtomicBool` being in its canonical state, or if
   another future test is added that calls `install_panic_hook`
   without an explicit reset, the sequencing becomes order-sensitive.
   Today nextest isolates each test into its own subprocess — which
   makes this safe for the project's stated `cargo nextest run`
   workflow — but the test relies on nextest-specific isolation
   without declaring the dependency. If anyone runs
   `cargo test -p cranelisp` (the non-nextest invocation the rust
   toolchain enables by default), the `install_panic_hook_runs_flush_on_panic`
   test also calls `std::panic::take_hook` and
   `std::panic::set_hook` — global mutations that will flap other
   tests.

   **Recommendation**: either (a) serialise these tests with a
   `Mutex<()>` held for the duration of each, named e.g.
   `PANIC_HOOK_TEST_GUARD`, or (b) annotate them with a doc comment
   that names the nextest dependency and adds
   `#[cfg_attr(not(nextest), ignore)]` — the latter is ugly but
   explicit. Preferred: (a). This is the same pattern other
   process-global-state tests (e.g. env-var tests) already use
   implicitly via the snapshot-save-restore idiom.

   **Owning skill**: `/int` (scheduler side) + `/backend` (IO side);
   parallel fix.

   **Classification rationale**: Important, not Blocker — nextest
   isolation covers the project's actual workflow; regression only
   bites a future contributor who uses `cargo test` directly. Not
   shipping infrastructure that will break under the documented
   test-runner.

## Suggestions (S)

1. **`src/observability.rs:197` — `Module.module: String` could use `ModuleFullPath`.**

   The design doc §3.1 describes events as parameterised by
   `ModuleFullPath` (the project's typed identifier for a module's
   fully-qualified path) and §5's filter example uses
   `TraceFilter::Module(ModuleFullPath::from(s))`. The implementation
   chose `String` with the rationale "integration-layer type; the
   boundary prohibition is on `cranelisp-shared` / `cranelisp-types`
   — owned String here is fine." That is defensible
   (trace events never cross a boundary, typed identifiers save no
   validation work for ephemeral payloads, and the filter compares
   string-to-string anyway), but it diverges from the design sketch.

   Either update the design to say `String`, or promote the payload
   to `ModuleFullPath` for consistency with the rest of `src/`. Zero
   functional impact.

   **Recommendation**: keep `String` — event payloads are not typed
   identifiers in the usual sense, and the hot-path allocator cost
   of `ModuleFullPath` is equivalent. Update the design doc one-line
   to note the divergence, or add a terse comment on the field
   explaining the choice.

2. **`crates/cranelisp-runtime/src/io_trace.rs:180` — `scheduling_class: u8` emitted as `0`.**

   Already documented as a FIXME(/backend) in `io.rs:173` and
   cross-referenced in the design doc header. No action needed this
   sprint; this is a tracking note so the finding survives into
   Slice 4. If Slice 4 picks hypothesis 2 (stdio buffer ordering), the
   missing class field becomes the first thing Slice 4 needs.

3. **`src/observability.rs:251` — `SCHEDULER_TRACE_BUFFER_CAPACITY = 65_536` matches IO trace cap by convention, not by extract-constant.**

   Both logs independently declare `pub const … = 65_536` with a
   comment citing "per /arch Phase 3a cross-doc consistency note".
   If these ever need to diverge, that's fine; if they ever need to
   stay locked together (e.g., because a test depends on per-thread
   worst-case memory ceiling), the duplication risks drift. Low
   priority — both are file-level constants with doc comments, not
   scattered magic numbers.

   **Recommendation**: leave as-is; acknowledge as a known duplication
   for the life of Slice 0. If Slice 4 evidence shows asymmetric
   memory pressure that drives one higher, the asymmetry is then
   real and the duplication becomes the correct shape.

4. **`src/observability.rs:211` — `SchedulerTracePayload::module_path()` has pub(private) visibility via `fn`, consumers use a local `passes()` helper in the selective-filter test instead of it.**

   The test at `src/observability.rs:779–786` re-implements
   `passes()` locally because `record_event`'s filter logic is
   inline. Extracting a shared `matches_filter(&TraceFilter,
   &SchedulerTracePayload) -> bool` helper would both simplify the
   test and expose the invariant separately from the hot-path emit.
   Non-blocking — the test's local helper is three lines.

## Design-adherence audit

- **`design/int/observability.md §3.1` — 15 `SchedulerTraceTag`
  variants**: matched (11 listed in design + 4 pool-state variants
  match the `ModuleState*` tags in `observability.rs:143–190`).
  Tag names match one-to-one with design prose. ✓
- **§4 hard constraints (crate placement, no boundary leak, no
  serialised format, no `cranelisp_alloc`, `Send + Sync` explicit)**:
  all upheld — verified by grep
  (`IoTraceEvent|SchedulerTraceEvent|...Tag` does NOT appear in any
  file under `crates/cranelisp-shared`, `crates/cranelisp-types`; no
  `cranelisp_alloc` reference outside doc comments; `const _: fn() =
  ||` assertions on `Send + Sync` present at
  `observability.rs:237–242` and `io_trace.rs:217–222`). ✓
- **§5 parse-once**: `OnceLock<Option<TraceFilter>>` on both sides,
  parse function isolated and pure, `std::env::var` appears only
  inside parse helpers + unit tests. ✓
- **§6 event struct shape**: timestamp u64, ThreadId, tag + payload
  — matches. Scheduler payload uses `timestamp` (not
  `timestamp_ns`) which is a minor inconsistency with the IO
  payload's field name. Both are u64-nanoseconds-from-anchor
  semantics, so functionally identical; purely a nit. Classified as
  doc hygiene, not a finding.
- **§7 dump format**: marker line
  `=== CRANELISP_SCHEDULER_TRACE DUMP ===` present
  (`observability.rs:472`). Merge-sort by `(timestamp, thread_ord_id)`
  implemented in `dump_all_buffers` + `dump_thread_buffer`. IO
  dump also merge-sorts; both use `sort_by_key`. ✓
- **§7.1 wiring primitives**: `SchedulerTraceFlushGuard` RAII +
  `install_panic_hook` idempotent guard + `publish_thread_buffer`
  worker-shutdown calls — all three primitives land, consumed by
  `src/main.rs:45–48` for the scheduler side and re-exported via
  `cranelisp-runtime/src/lib.rs:77–87` for the IO side. ✓
- **`design/backend/io-trampoline-trace.md §3` event taxonomy**:
  12 tags enumerated (`TrampolineEnter`, `TrampolineExit`,
  `PureStep`, `BindEnter`, `BindExit`, `PlatformEffect`,
  `ContPush`, `ContPop`, `ParSpark`, `ParSerialGroupEnter`,
  `ParJoin`, `ParBarrierForce`). All 12 present in
  `IoTraceTag` enum (`io_trace.rs:127–154`). ✓
- **§4 struct shape**: `IoTraceEvent` is ≤ 64 B (asserted by unit
  test `event_size_is_bounded`). `Send + Sync` via compile-time
  `const _: fn() = ||` block. No `Box<…>`, no `String` in
  `IoTracePayload` — largest variant is `PlatformEffect` (2×i64 +
  u8). ✓
- **§5 crate placement**: `io_trace.rs` lives in
  `crates/cranelisp-runtime/src/`, separate from existing `trace.rs`
  (which hosts `(trace …)` special form). Module name disambiguation
  works. ✓
- **§6.1 wiring primitives**: `FlushGuard` RAII + `install_panic_hook`
  idempotent guard — both present
  (`io_trace.rs:481–502`, `io_trace.rs:524–541`). Re-exported at
  `crates/cranelisp-runtime/src/lib.rs:77–87`. ✓
- **`run_io_trampoline_inner` wrapper**: `io.rs:92–103` adds the
  outer wrapper whose only job is to emit `TrampolineEnter` and
  `TrampolineExit` bookends; the inner loop is unchanged. Match
  with design §3 ("TrampolineEnter | top of cranelisp_run_io,
  TrampolineExit | return from cranelisp_run_io") ✓.
- **Shared `Instant` anchor**: design requires both traces reference
  the same `OnceLock<Instant>`. Implementation exports
  `trace_instant_anchor()` from `cranelisp-runtime`
  (`io_trace.rs:58–65`); `src/observability.rs:314` calls
  `cranelisp_runtime::trace_instant_anchor()`. Unit test
  `anchor_is_the_shared_runtime_anchor` asserts pointer equality.
  ✓ This matches /arch Phase 3a "Recommendation (non-blocking):
  at implementation time, the two crates should depend on a single
  exported Instant" — adopted.
- **Resolved pre-Wave FIXME(/arch) items**: all 4 from Phase 3a
  confirmed resolved in-doc prior to implementation.

## Boundary-hygiene audit

Grep evidence for all four hard constraints from `/arch` Phase 2:

- `rg 'IoTraceEvent|SchedulerTraceEvent|IoTraceTag|SchedulerTraceTag'
  crates/cranelisp-shared crates/cranelisp-types` — **0 matches**.
  Event types are confined to their owning crates. ✓
- `rg 'cranelisp_alloc' src/observability.rs
  crates/cranelisp-runtime/src/io_trace.rs` — **0 matches** in code;
  only the doc-comment prohibition at `observability.rs:34` and
  `io_trace.rs:28`. Trace storage is `VecDeque` + `Vec` on the host
  allocator, as specified. ✓
- `rg 'Serialize|Deserialize|serde' src/observability.rs
  crates/cranelisp-runtime/src/io_trace.rs` — no matches in either.
  Event structs have no Serde derives; they never cross any
  serialised artefact boundary. ✓
- `rg 'Send \+ Sync' src/observability.rs
  crates/cranelisp-runtime/src/io_trace.rs` — both files carry a
  `const _: fn() = || { fn assert_send_sync<T: Send + Sync>() { };
  assert_send_sync::<…>(); };` block that causes a compile error if
  any future field breaks the auto-trait. ✓
- `rg 'std::env::var' src/observability.rs
  crates/cranelisp-runtime/src/io_trace.rs` — each appears only in
  `parse_filter_from_env`, `parse_filter_from_env_value`, and two
  unit-test snapshot-save-restore blocks. Zero `std::env::var` calls
  from the hot path. ✓

The integration test
`tests/sprint61_observability_shared.rs::trace_event_types_do_not_appear_in_boundary_crate_sources`
scans `cranelisp-types`, `cranelisp-frontend`, and
`cranelisp-typecheck` for leaks of any of the six trace type names
and asserts zero matches. This is a durable guard that future
refactors will hit if they attempt to move the types into a boundary
crate. ✓

## Test audit

- **No `#[ignore]`**: `rg '#\[ignore\]' tests/sprint61_observability_*.rs`
  — 0 matches. One occurrence in a doc comment explaining *why*
  subprocess tests are not ignored (surface-level diagnostic
  assertion preferred — the correct pattern per
  `memory/feedback_failing_not_ignored.md`).
- **No `flaky` disposition**: `rg 'flaky|skip|todo!|unimplemented!'` —
  only two matches, both in doc comments describing test layering.
  No `#[flaky]` disposition, no `todo!()` stubs, no skipped tests.
  ✓
- **Unit vs integration separation**:
  - Unit tests live with implementation: 25 unit tests inside
    `src/observability.rs` `#[cfg(test)] mod tests`, 20 unit tests
    inside `crates/cranelisp-runtime/src/io_trace.rs` `#[cfg(test)]
    mod tests`. Both cover parse-layer correctness, ring-buffer
    semantics, Send + Sync at compile time, flush-guard drop, panic
    hook idempotency, cross-thread merge-sort. ✓
  - Integration tests live in `tests/`: 19 tests across 3 files
    (`sprint61_observability_scheduler.rs`, `..._io.rs`, `..._shared.rs`).
    Subprocess tests exist alongside Rust-API tests. ✓
- **Ledger disclosure**: Task prompt says "16 currently passing / 3
  ledgered to S61 Slice 4 + S61 Wave 5". Not hidden — those are
  design-driven failing tests that document evidence-gated open
  work, consistent with `memory/feedback_failing_not_ignored.md`. ✓
- **Cross-log shared invariant**: the `shared` test file verifies
  anchor-equality and boundary-hygiene structural properties that
  would otherwise live implicitly in code. Durable signal for
  future drift. ✓

## Review dimensions — all 13 checked

| # | Dimension | Status |
|---|---|---|
| 1 | Design adherence | ✓ strong |
| 2 | Boundary hygiene (Principle 3) | ✓ |
| 3 | Allocator discipline | ✓ |
| 4 | Env-var parse-once | ✓ |
| 5 | Performance when disabled | ✓ — single OnceLock load + null check |
| 6 | Send + Sync | ✓ — compile-time enforced |
| 7 | Panic-hook idempotency | ✓ — AtomicBool compare-exchange |
| 8 | Flush-on-exit discipline | ✓ — plus explicit `flush_traces()` at `process::exit` sites |
| 9 | Code structure (max 100 LOC, max 8 params, named structs) | ✓ — largest fn is `format_event_line` at ~42 LOC |
| 10 | Error handling (no unwrap/panic in pipeline) | ✓ — all unwrap/panic confined to `#[cfg(test)]` |
| 11 | Naming (typed identifiers, named constants) | ✓ with minor caveat (S1) |
| 12 | Test hygiene (unit with impl, integration in `tests/`, no `#[ignore]`, no `flaky`) | ✓ |
| 13 | Clippy cleanliness | out of scope — not run per review instructions |

## Recommendations to /sprint

1. **Accept the Wave 1 Slice 0 submission as PASS WITH FINDINGS**.
   No Blockers; the single Important finding (I-1) is a test-robustness
   concern that does not affect the documented `cargo nextest run`
   workflow. It CAN be carried to a follow-on wave ticket without
   holding up Wave 1 close.

2. **Log I-1 as a deferred Important** in the Wave 1 close readout.
   Owning skills: `/int` + `/backend` (parallel fix, same pattern).
   Fix size: ~10 LOC each (a `once_cell::sync::Lazy<Mutex<()>>`
   grabbed at test entry). Not a Sprint 62 ROADMAP line item; a
   sprint-local cleanup.

3. **Note the Slice 4 dependency on S2 (scheduling_class)**. The
   `PlatformEffect { scheduling_class: 0 }` placeholder is a known
   deferred thread — if Slice 4 picks hypothesis 2 (stdio DLL buffer
   ordering), the FIXME(/backend) at `io.rs:173` becomes the first
   item on the Slice 4 implementation list. Slice 4 readout should
   confirm this path before committing to a fix shape.

4. **Suggestions S1–S4 can slide to Wave 5 polish** if the sprint
   carries further — none are urgent. Recommended: skip S3, fold
   S1+S4 into a single small doc/API tidy during Slice 5 E cleanup.

5. **Cross-reference the two design docs' field-naming inconsistency**
   (`timestamp_ns` on IO side, `timestamp` on scheduler side) in the
   wave 5 doc-hygiene pass. One-line fix.

Wave 1 Slice 0 is the correct observability floor for Slices 3 and 4
to build on. Ship it.

End of review.
