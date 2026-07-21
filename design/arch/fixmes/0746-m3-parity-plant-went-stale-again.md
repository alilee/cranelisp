---
number: 0746
target: /testing
filed_by: /dev (cranelisp-backend, S115 W3)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/ms_p6_mode_self_tests.rs::m3_parity_catches_planted_leak (LEAK_PROG)
status: open
---

# The M3 alloc-parity capability fence's planted leak went stale again — its own FLIP-HAZARD note fired

## Severity
Important (a capability fence is inverted to RED; the mode it guards is
unverified until re-planted).

## Issue

`m3_parity_catches_planted_leak` asserts that `CRANELISP_ALLOC_PARITY` ABORTS on
a program with a deliberate alloc/dealloc imbalance. Its plant is

```
(defn g [] (let [s "hi"] (Pure 9)))
(defn main [] (g))
```

whose imbalance was, per the test's own comment, "the general G2/item-26 protect
over-inc [that] leaves one of the two heap boxes unfreed on `g`'s return".

S115 W3 change-set 2 FIXED exactly that over-inc: `protect_return_value` no
longer emits a protective inc for a **fresh-construction return** in any
function (the item-26 generalisation, superseding the `main`-keyed F-R1 special
case and resolving FIXME 0696 against its design ruling direction (b),
`design/backend/s115-carrier-and-rc-sweep.md` §7). `(Pure 9)` returned through a
`let` is a fresh construction, so `g` now balances and the parity mode has
nothing to catch — the fence inverts to RED.

**This is the second time this plant has gone stale, and the test predicted it
verbatim:**

> FLIP-HAZARD: if the G2/item-26 protect over-inc is ever fixed this fence
> re-inverts — re-plant on another deterministic imbalance.

(The first staleness was S114 FIXME 0690, when the W4 F-R1 fix balanced the
original entry-`main` plant.)

## Proposed resolution

Re-plant `LEAK_PROG` on a deterministic imbalance that is not a return-protect
artifact — the class keeps disappearing precisely because it is a live defect
family under active repair, so a plant drawn from it has a short half-life.
Candidates that are currently imbalanced and are NOT this family:

- the entry-`main` IO-result **heap payload** leak —
  `(defn main [] (Pure "hi"))` → 2 allocs / 1 free, toggle-INDEPENDENT, and now
  known to be owned outside the backend (FIXME 0745), so it will not be silently
  balanced by a backend wave;
- a synthetic plant that does not depend on any open defect at all (the
  structurally durable option — e.g. an intrinsic-level injected imbalance behind
  a test-only hook), which would make the fence fail-on-revert of the MODE rather
  than of some unrelated fix.

`/qa` may want the second shape as a standing rule for capability fences: a
capability fence whose stimulus is a live defect re-inverts every time that
defect is fixed.

## Context

Surfaced by the S115 W3 full-suite run. Not a regression: the compiler behaviour
moved in the CORRECT direction (one fewer leak), and the RED is the fence's
stimulus evaporating. `/dev`(backend) does not author `tests/` sources, hence
this FIXME rather than an in-place re-plant.

## /qa RULING (2026-07-21, S115 mid-Phase-5 disposition batch)

**Confirmed on source: this is the `memory-safety-coverage.md` §4.1 prong-2
lifecycle case** (an e2e capability fence whose plant is a live compiler
defect, reaching end of life when that defect drains). NOT a regression.
Durable record: `tests/plan/s115-test-plan.md` §8.2.

**Re-plant shape — SYNTHETIC, per the S114 MS-P6 precedent**
(`safety_lane_detects_falsified_clean_expectation_capability_green`,
`7c2d5168`): a test-only injected imbalance at the intrinsics
allocator/diagnostics seam behind an inert-unless-set env gate, so the fence
is fail-on-revert of **the MODE**. The hook must join
`diagnostics/tests.rs::all_gates_default_off` in the same change-set.
Requires a small `/dev`(intrinsics) hook alongside the `/testing` re-plant.

**Candidate 1 REJECTED** (re-plant on the entry-`main` heap-payload leak):
per FIXME 0745's /qa attribution that defect now has an owner
(`/design`(int) → `/dev`(src)) and a fix path, so planting on it repeats the
anti-pattern a third time.

**Compliant FALLBACK if W7 capacity does not admit the hook** — retire
`m3_parity_catches_planted_leak` with the §4.1 tombstone. This needs no user
sign-off and is not a coverage regression: prong 1 is in place (four M3
parity self-tests, `crates/cranelisp-intrinsics/src/diagnostics/tests.rs`
`:100/:108/:116/:124`) and prong 3 is in place
(`m3_parity_no_false_abort_on_clean` keeps the env wiring exercised).
Tombstone names the drained fault set (0690 F-R1; S115 W3 item-26), the
unit-tier successor, and the surviving wiring face.

**Binding on the schedule: this must not reach certification RED.** W7, one
slot; `/testing` takes the fallback in the same slot if the hook slips.

**Standing rule added** (`tests/plan/memory-safety-coverage.md` §4.1,
prong-2 amendment): a plant drawn from a live defect is self-expiring —
prefer a synthetic plant whenever a test-only injection hook is
constructible; never plant on a live defect that already has an owner and a
fix path.
