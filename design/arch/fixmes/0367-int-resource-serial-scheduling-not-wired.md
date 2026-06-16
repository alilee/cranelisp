---
number: 0367
target: /int
filed_by: /qa
filed_at: 2026-06-16
sprint_filed: 83
refers_to: spec/10-io.md §10.12 §10.12.4, src/bind_chain_analysis.rs, src/session_setup.rs (apply_bind_chain_analysis), tests/spec_10_io.rs::resource_serial_diff_token_parallelizes
status: open
---

# Automatic IO scheduling (§10.12) is not wired into the live pipeline — no `Par` node is ever emitted

## Issue

Spec §10.12 ("Automatic IO Scheduling") is a MUST: the compiler MUST perform
independence analysis on `bind!` chains and MUST insert `Par` nodes for
commutative / data-independent effect pairs (§10.12.1), and the trampoline MUST
serialise same-resource-token branches while running different-token branches
concurrently (§10.12.4).

**None of this is observable end-to-end** because the int-side pass that inserts
`Expr::ParBind` from a `bind` chain is dead code:

- `src/bind_chain_analysis.rs::auto_schedule_defn` (the only live entry point) is
  called ONLY from `src/session_setup.rs::apply_bind_chain_analysis`.
- `apply_bind_chain_analysis` is itself `#[allow(dead_code)]` with **zero live
  callers** — nothing in the `--run` / `--link` / REPL pipeline invokes it.
- Consequently the only non-test construction of `Expr::ParBind` anywhere in the
  source tree (`bind_chain_analysis.rs:350`) is never reached. No `Par` node is
  ever produced from user source.

The backend HAS full `Par` support — codegen (`compiler/mod.rs`,
`control_flow.rs`, `heap.rs`, `lib.rs`), the trampoline dispatch
(`dispatch_par_branches`, design/backend/io-scheduling.md §5.2), and the
ResourceSerial token-grouping logic. The backend unit tests
(`control_flow.rs::par_codegen_tests`) verify codegen of a *hand-constructed*
`ParBind` node. But nothing in the live pipeline ever hands the backend such a
node, so the entire feature is inert from the user's perspective.

### Observed (S83, FIXME 0353 timing e2e)

Two data-independent ResourceSerial calls (each sleeping 200 ms) in one `bind`
chain run **sequentially in all modes**:

| Program | `--run` wall-clock | `--link` (produced binary) |
|---|---|---|
| same token (1, 1) | ~420 ms | ~409 ms |
| diff tokens (1, 2) | ~415–437 ms | ~409–417 ms |

Same- and diff-token timings are indistinguishable (~2×200 ms) — diff tokens did
NOT parallelise. A Commutative-pair control (`commutative-sleep-ms` ×2) also runs
sequentially (~430 ms), confirming the defect is the missing wiring, not
ResourceSerial-specific. `CRANELISP_CODEGEN_TRACE=1` shows zero `Par` nodes.

This is the runtime-dispatch remainder that FIXME 0353 set out to witness. The
fixture half (the `resource-serial-sleep-ms` test-capture function) landed
correctly; the witness exposes that the dispatch it was meant to observe never
runs because the upstream Par-insertion pass is disconnected.

## Proposed resolution

Re-wire the bind-chain independence analysis onto the live compile path so
`auto_schedule_defn` runs over each defn body after macro expansion / AST build,
before typecheck (per the algorithm comment in `bind_chain_analysis.rs` and
`design/int/bind-chain-analysis.md`). Candidate seam: invoke
`apply_bind_chain_analysis` (drop its `#[allow(dead_code)]`) from the worker's
build/check form chain in `--run`, `--link`, and REPL, so the pass is
mode-uniform. The note in `bind_chain_analysis.rs` ("REPL eval-expression path
currently does not invoke auto-scheduling") and the "FIXME 0176" reference in
`src/lib.rs` (`activate on the hot path`) both point at this same dormant wiring.

The grouping logic itself (`rebuild_chain` / `flush_par_group` /
`classify_expr` / `is_independent`) appears complete and is unit-tested; the
work is the integration wiring, not the algorithm. After wiring, verify the
data-dependency and Sequential-class negatives still hold (a dependent binding
or a `read-line`/`print` Sequential pair MUST NOT Par-group).

## Operational implication / Context

- The failing-not-ignored regression guard is committed:
  `tests/spec_10_io.rs::resource_serial_diff_token_parallelizes` (asserts
  diff-token concurrent wall-clock < 1.5× single-call duration in BOTH `--run`
  and `--link`; currently RED at ~2×). It flips green when this wiring lands.
- The positive serialization companion
  `tests/spec_10_io.rs::resource_serial_same_token_serializes` passes in both
  the wired and un-wired states (sequential satisfies "> 1.5× single") — it is
  the same-token witness and a regression guard against a future change that
  wrongly parallelises same-token calls.
- **FIXME 0353 must NOT be closed as "witnessed" until this is fixed.** The
  fixture + the failing guard ARE the durable record (per the project's
  defect-needs-a-failing-test discipline); 0353's "timing e2e is the witness"
  closure condition is only met when `resource_serial_diff_token_parallelizes`
  is green.
- This is a real spec-conformance defect (§10.12 is MUST), surfaced — not
  introduced — by the 0353 witness. No test margin tweak can or should mask it.
