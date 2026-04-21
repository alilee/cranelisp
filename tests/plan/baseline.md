# Baseline Failure Ledger

Owned by `/qa`. Verified at every sprint open and every sprint close.

## Discipline

Every test currently failing in `cargo nextest run --no-fail-fast` MUST have an entry in this file. There are no other legitimate places for a failing test to live: `#[ignore]` hides the fact, and undocumented failure relies on institutional memory.

**Allowed dispositions:**

- `under-investigation` — owner is actively reducing or fixing; target sprint names when the work lands.
- `out-of-scope (owner=/skill)` — a real defect that is not in the current sprint's scope; target sprint names when it will be picked up. An owning skill MUST be named.
- `exemplar-gap (owner=/port)` — a failure that lives in `exemplar/` (a Cranelisp-level test, not a cargo test) and reflects a real language or runtime defect surfaced by the exemplar. Owner is always `/port` for the repro; the underlying fix may be owned by a compiler skill which is named in the entry's `underlying-owner` field.

**Explicitly NOT allowed:**

- `flaky` — never. Local tests are deterministic; if a test fails intermittently, the cause is a real race, ordering bug, or uninitialised state. "Flaky" closes investigation prematurely and forfeits the regression guard. Per user directive 2026-04-21: *"we need to be really clear about 'flaky' — that is not a thing in local tests."*
- `timing-sensitive` — equivalent to flaky. Tests that assume a particular scheduling order are either testing something real (name it and pin it) or they are incorrectly written (fix them).
- `documented race` — the race is the bug. Fix it.
- `pre-existing` — historical dispositions rely on commit-SHA amnesia. "Pre-existing" is not a disposition: the same tests either get a real disposition (`under-investigation` + target sprint, or `out-of-scope (owner=/skill)` + target sprint) or they are deleted.

**Required fields per entry:**

- Test name (fully-qualified: `binary::test_function_name`)
- Current commit SHA (short form)
- Exact stderr signature (2–5 line excerpt, quoted verbatim)
- Owning skill (`/qa`, `/int`, `/backend`, `/port`, etc.)
- Target sprint
- Disposition + one-sentence rationale

A failing test without all six fields is treated as a sprint-blocking issue. `/sprint` MUST refuse to close a sprint that contains unentered failures.

## Current Entries (as of 2026-04-21, sprint 60 wave 3, SHA `f78adf3`)

### Cargo test suite

**None.** `cargo nextest run --no-fail-fast` reports **1837 passed / 0 failed / 0 skipped** in ~30s at SHA `f78adf3`.

### Exemplar-level tests (non-cargo)

| Field | Value |
|---|---|
| Test name | `exemplar/solver.cl::test-unsolvable` (run via `/run-tests` inside the exemplar, not a cargo test) |
| SHA | `f78adf3` |
| Stderr / observable signature | `(Some "puzzle with two 5s in row 0 should be unsolvable")` — solver returns `Success` on a grid with two `5`s in row 0 where it should return `Unsolvable`. Symptom in `--run` main: "Solution" board with duplicate values in row 0 (e.g. `4 5 3 \| 9 2 1 \| 6 7 7`). |
| Owning skill | `/port` (repro authored), `/qa` (narrow integration test handoff pending), `/backend` (suspected underlying codegen/RC interaction) |
| Target sprint | Sprint 61 |
| Disposition | `exemplar-gap (owner=/port)` with `underlying-owner=/backend` |
| Rationale | `test-unsolvable` was re-enabled in Wave 3 commit `f78adf3` after Defects 4–6 resolved. The solver's `eliminate` no-ops when called on a same-value `Given`/`Solved` cell; patching it to return `None` breaks valid puzzles, implicating peers iteration, Vec COW, or match-arm sharing rather than pure algorithmic logic. `FIXME(/qa)` and `FIXME(/backend)` are filed in `exemplar/solver.cl` lines 380–406 documenting the investigation notes. `/qa` will own narrowing this into a compile-time integration test once `/port` hands off minimal repro per `memory/feedback_cross_skill_minimal_repro.md`. |

## Close-time Verification Protocol

`/sprint` MUST re-verify every entry in this file at sprint close:

1. Check out the commit named in the entry's SHA field and run the test.
2. Confirm the test still fails with the same stderr signature.
3. One of:
   - **Resolved** — the test now passes on HEAD. Remove the entry from this file and note the removal in the sprint close report.
   - **Still failing, same signature** — entry is current. If the target sprint has passed, update it; the owning skill MUST justify the slip in the close report.
   - **Still failing, different signature** — the underlying defect has shifted. Update SHA, signature, and (if relevant) owner in-place; do not delete. A changed signature usually means an unrelated interacting defect landed; investigate before accepting the update.
4. If a new failure appeared during the sprint that does not have an entry, `/sprint` MUST block close until `/qa` adds it per the required-fields list above.

This protocol runs at every close — no exceptions. "We're in a hurry" is how flaky dispositions creep in.
