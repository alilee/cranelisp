---
number: 0141
target: /spec
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: spec/12-runtime.md §12.5, tests/spec_12_runtime.rs (5 #[ignore]'d TCO tests pending), tests/legacy/ring0.rs (TCO cluster)
status: open
---

# Upgrade spec/12-runtime.md §12.5 from SHOULD to MUST

## Issue

`spec/12-runtime.md §12.5 Tail Call Optimization` currently reads:

> Implementations SHOULD optimize self-recursive tail calls into loops.

The Wave 5.5 dedupe-verification audit deferred the TCO cluster from
`tests/legacy/ring0.rs` (5 tests: `tco_deep_countdown`,
`tco_match_tail_position`, `tco_accumulator`,
`tco_let_body_tail_position`, `tco_non_tail_recursion_unchanged`).
Wave 5.6 carries them forward as `#[ignore]`'d tests in
`tests/spec_12_runtime.rs` because the assertions rely on the *normative
guarantee* that self-TCO is optimised — but `SHOULD` is non-normative
("recommended but not required"), so a conformant implementation could
fail `tco_deep_countdown` with stack overflow and still be in spec.

The legacy tests assert that:

 - Self-recursive tail calls do not consume stack frames (deep
   countdown to 100k–1M without overflow).
 - Tail position is preserved through `match` arms, `let` bodies, and
   `if` branches.
 - Non-tail recursion is NOT optimised (the negative-of-TCO assertion).

The reimplementation delivered TCO in Sprint 22 (per
`memory/macros.md §"Tail Call Optimization (TCO)"`) and the existing
spec annotation `[Tested+Neg tests/ring0.rs::tco_deep_countdown]`
already implies TCO is treated as a tested guarantee. The text and the
annotation disagree: SHOULD vs. tested.

## Proposed resolution

Upgrade §12.5's normative verb from `SHOULD` to `MUST` for the
self-recursive case. Suggested wording:

> Implementations MUST optimize self-recursive tail calls into loops
> (no stack frame consumed per recursive call).

Keep the existing tail-position recursion definition unchanged. Keep
the implementation-defined clause for mutual / lambda /
constrained-polymorphic recursion as `MAY` — Sprint 22 explicitly
left those out of scope and the existing wording matches.

Once `MUST` lands, `/qa` removes the `#[ignore]` attributes from the
5 TCO tests in `tests/spec_12_runtime.rs` and re-runs the suite. The
existing `// spec: spec/12-runtime.md §12.5` citations resolve clean
through the linter without further edit.

## Operational implication / Context

Filed during Sprint 64 Wave 5.6 file 4 (ring0.rs) carry-forward
authoring. Without the MUST upgrade, the 5 TCO tests would be
INVENTED-style — asserting on behaviour the spec only recommends —
and `/qa` would have to keep them `#[ignore]`'d to honour the
failing-not-ignored / no-test-against-non-spec rule. The
ignore-with-reason form is the correct interim disposition until
`/spec` ratifies; target activation is Sprint 65.

The implementation contract that justifies the MUST upgrade is
documented at `memory/macros.md §"Tail Call Optimization (TCO)"`:

> Loop-based self-TCO: self-recursive tail calls jump to loop header
> block instead of calling … `compile_body` creates loop_header block
> with block params … `compile_tail_self_call`: compile args →
> `emit_scope_cleanup_for_tco` → jump to loop_header → dead block +
> dummy return.

This is a structural property of the backend's emit, not a
heuristic — every self-recursive call in tail position becomes a
jump. `/spec` can lift this contract directly into the normative
text.

## Test inventory awaiting activation

In `tests/spec_12_runtime.rs`:

 1. `tco_deep_countdown` — REGRESSION-GUARD; 1M-iteration countdown
    returns 0 without stack overflow.
 2. `tco_match_tail_position` — REGRESSION-GUARD; match arm in tail
    position recurses 100k times.
 3. `tco_accumulator` — REGRESSION-GUARD; accumulator-style recursion
    (sum 0..100 = 5050).
 4. `tco_let_body_tail_position` — `let` body in tail position
    recurses 100k times to return 42.
 5. `tco_non_tail_recursion_unchanged` — negative-of-TCO; non-tail
    recursion still returns the correct value at small depth.
