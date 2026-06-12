---
number: 0317
target: /spec
filed_by: /sprint
filed_at: 2026-06-12
sprint_filed: 79
refers_to: spec/02-grammar.md §2.1 (line 23/25), spec/10-io.md §10.6 (line 242–254) + §10.6.1, spec/12-runtime.md §12.6 (line 171–173), tests/spec_10_io.rs::batch_main_pure_int_return_is_rejected, tests/plan/ledger.md (S79 RED row), tests/plan/PLAN.md §"Mode canonicalisation"
status: open
---

# Enforce `main : (Fn [] (IO _))` for batch mode + close the output-coverage / mode-equivalence reshape

## Issue (surfaced S79 Phase 5, user-directed forcing function)

The spec states a MUST in three places — a batch-mode (`--run` + `--link`) `main`
MUST return `IO _`:
- `spec/02-grammar.md:25` — "the program MUST define a function named `main` … returns a value of type `IO _`."
- `spec/10-io.md:244–247` — "The return type of `main` MUST be `IO _`" → `main :: (Fn [] (IO _))`.
- `spec/12-runtime.md:173` — same MUST; exit code is the inner Int.

**The compiler does not enforce it** — it leniently accepts a bare-`Int` `main`
(`(defn main [] 0)`). Worse, a **traceability audit (S79)** found the requirement
was never traced (all three refs carry stale `[R4 S10]`), AND existing tests
**positively certify the violation**:
- `tests/spec_10_io.rs::run_mode_main_returns_int_exit_code` asserts `(defn main [] 7)` → exit 7.
- `tests/spec_12_runtime.rs` exit-code witnesses use `(defn main [] 42)` / `… true`.
- `tests/link.rs::link_error_when_main_returns_wrong_type` uses an `Int || IO`
  disjunction that *accepts* a bare-`Int` main.

A failing-first negative test now encodes the requirement and rides RED
(`tests/spec_10_io.rs::batch_main_pure_int_return_is_rejected`, ledgered,
un-ignored) — the durable obligation guard. The suite cannot be fully green
until this is resolved. (REPL mode is exempt — no `main` requirement, `spec/10-io.md:268`.)

## Proposed resolution (a dedicated increment — the sweep is only sensible once enforcement is live)

1. **`/spec` confirms the MUST stands as enforce-able** (vs relaxing the spec to
   permit a bare-`Int` batch main for ergonomics — the explicit fork). User
   intent (S79) is enforcement. On confirmation, cascade:
2. **`/dev` (typecheck)** enforces it — reject a batch `main` whose return type
   is not `IO _`, with a clear error naming the `(Fn [] (IO _))` requirement.
3. **`/qa` suite-wide sweep** — ~125 batch bare-`Int` mains across ~11 test files
   → `IO` (`(pure 0)` smoke / `(print …)` observable), ~22 `examples/` files
   rewrapped, exemplar inline repros, and the **examples exit-code-checksum
   convention reworked** (`IO Int` inner-Int exit semantics differ from a bare-Int
   return). Fix the three test-design defects above (they certify the violation).
4. **Output-coverage reshape (pairs with the sweep)** — `run_through_all_modes_output`
   stdout harness + convert the mode-equivalence corpus so the **majority of
   programs produce + assert observable output** verified byte-equivalent across
   REPL/`--run`/`--link` (today only 3 of 911 tests assert program stdout, all
   `--run`). Update `tests/plan/PLAN.md §"Mode canonicalisation"` so
   output-equivalence is the primary invariant and exit-code-equivalence is the
   pure-smoke minority. Consider whether a normative "observable output is
   identical across run modes" invariant belongs in `spec/10-io.md` (it currently
   lives only in PLAN.md + Principle 11; precedent: the trace "behaves identically
   across modes" sentence at `spec/04-expressions.md:850`).
5. **`/spec` annotation upgrade** — `02-grammar.md:23` / `10-io.md §10.6` + §10.6.1 /
   `12-runtime.md §12.6` from stale `[R4 S10]` → `[Tested+Neg tests/spec_10_io.rs::batch_main_pure_int_return_is_rejected]`.
6. The RED forcing-function test flips green.

## Operational implication / Context

Deferred from S79 by user decision (2026-06-12): the failing test stays as the
guard; the enforcement + suite-wide sweep + output reshape land together as a
dedicated increment (S80-shaped), because rewriting ~150 mains to `IO` *before*
the compiler requires it is premature. S79 retains only the RED guard + a minimal
`--link` + `stdio` `print` R1 guard. This is the largest single deferral of S79;
the ledger row + this FIXME + the failing test are its durable record.
