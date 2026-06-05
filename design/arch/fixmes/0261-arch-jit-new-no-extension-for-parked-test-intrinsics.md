---
number: 0261
note: Renumbered 0259→0261 by /sprint (S76 W2) — 0259 was used+deleted in-wave by /dev (frontend)'s reserved-name FIXME; deleted numbers are not reused. Max active was 0260.
target: /arch
filed_by: /dev (int)
filed_at: 2026-06-05
sprint_filed: 76
refers_to: crates/cranelisp-backend/src/jit.rs (Jit::new), crates/cranelisp-intrinsics/src/catalog.rs (intrinsics_table), src/session_v4.rs (int_intrinsics), src/worker.rs (build_session_jit)
status: open
---

# `Jit::new(symbol_tables)` provides no extension point for the 2 parked int-hosted test intrinsics

## Issue

S76 W-Collapse replaces int's hand-assembled JIT setup with the unified
`Jit::new(symbol_tables)` (BC §3 / D41). `Jit::new` derives the entire JIT
symbol set from `symbol_tables`: it registers the full
`cranelisp_intrinsics::intrinsics_table()` (now incl. the 12 trace bodies +
formatter), the per-module GOT data symbols, and the platform-effect jit-names.

The 2 PARKED int-hosted test intrinsics — `discover-tests` / `run-test`
(`src/session_v4.rs::int_intrinsics()`, the `discover_tests_extern` /
`run_test_extern` Rust fns) — are NOT in `intrinsics_table()`. They are
backend-emitted-call targets for compiled programs that contain literal
`(discover-tests)` / `(run-test ...)` forms (the frontend AST builder still
lowers these to calls referencing those symbol names; backend emits them as
`Linkage::Import`). When such a program is JIT-compiled, the JIT must resolve
those two names — but `Jit::new(symbol_tables)` takes no extra-symbols
parameter, and `new_with_symbols` is now `pub(crate)` to backend.

Net effect: there is no in-crate path for int to register the 2 parked test
intrinsics on a `Jit::new`-constructed JIT. The REPL `/run-tests` slash command
is unaffected (it calls `discover_test_names` / `run_test_by_name` as Rust fns,
bypassing the JIT entirely) — only a *user program* with literal
`(discover-tests)`/`(run-test)` forms hits the gap.

## Proposed resolution

`/arch` to choose one:

(a) **Fold the 2 test intrinsics into `cranelisp_intrinsics::intrinsics_table()`**
    — the architecturally-uniform path (they become ordinary catalog entries
    registered by `Jit::new`). Requires relocating `discover_tests_extern` /
    `run_test_extern` (and their `TestRunnerState` thread-local) into
    `cranelisp-intrinsics`, which is more than the PARKED scope wanted.

(b) **Add a narrow `Jit::new_with_extras(symbol_tables, extras: &[(&str, *const u8)])`**
    backend entry that int calls with the 2 test intrinsics. Smallest mechanism;
    keeps the test-runner Rust fns int-side (their natural home — they read
    int session state).

(c) **Accept the gap as parked**: leave the 2 entries in `int_intrinsics()` as a
    dead remnant and accept that literal `(discover-tests)`/`(run-test)` in a
    *compiled program* (not the slash command) fails to resolve at JIT-finalize
    until the test-runner story is un-parked.

## Operational implication / Context

For S76 W-Green, int's `build_session_jit` (`src/worker.rs`) calls
`Jit::new(symbol_tables)` and the 2 test intrinsics are NOT registered on the
JIT. `int_intrinsics()` is retained (returns the 2 entries) for the eventual
resolution but is currently unreferenced on the working path — the expected
dead-code-warning signal of the narrowing. The slash-command test path works
regardless. This is Wave-4 e2e input, not a W-Green blocker.

## /arch disposition (2026-06-05) — facts verified; DELIBERATELY PARKED, awaiting user direction

Facts checked against `design/arch/tracing.md` §4.3 + `design/arch/bounded-contexts.md` §3:

- **Verified.** `Jit::new(symbol_tables)` registers the full
  `cranelisp_intrinsics::intrinsics_table()` — now including the 12 trace bodies +
  `trace_format` (catalog grows 15 → 27; `tracing.md` §4.1/§4.2). The 2 test
  intrinsics (`discover-tests`/`run-test`) are NOT catalog entries:
  `tracing.md` §4.3 records `int_intrinsics()` shrinking to exactly those 2 and
  states "the `Jit::new(symbol_tables)` collapse must still account for those two
  (that residual is the S76 `Jit::new` seam for the *test* intrinsics, untouched
  here and **unresolved by this document — it is parked with the test
  intrinsics**)." This FIXME is precisely that named-but-deferred residual.
- **Parked, not decided.** The test-runner story is PARKED per the user
  (`tracing.md` §4.3: "Test intrinsics are PARKED — explicitly out of scope per the
  user; their relocation (if any) is a separate future question"). The choice among
  (a) fold into `intrinsics_table()`, (b) `Jit::new_with_extras`, (c) accept the gap
  is a **user call** bound up with un-parking the test-runner story — `/arch` does
  NOT pick one here. The three options as stated are sound and mutually exclusive;
  no new option is needed.
- **Not a W-Green blocker.** Confirmed by the filer and by BC §3 — option (c) is the
  de-facto S76 state (the 2 entries are a dead remnant; only a *compiled program*
  with literal `(discover-tests)`/`(run-test)` forms — not the `/run-tests` slash
  command — would hit the unresolved-symbol gap at JIT-finalize).

**Status: stays `open`, deliberately parked.** Resolve when the user un-parks the
test-runner story; at that point `/arch` rules (a)/(b)/(c) and routes to the owning
`/dev`. Until then this is inert and does not block any wave.
