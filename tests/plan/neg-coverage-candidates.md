# Negative-Coverage Candidates for Slice 5 H (Sprint 61)

**Audit date**: 2026-04-22
**Commit SHA**: `a9028c0`
**Auditor**: `/qa` (Sprint 61 Phase 3)
**Method**: Grep `\[Tested [^+\]]` across `spec/` and `repl/spec.md`,
then filter to MUST / MUST NOT rows that have a positive test today and
carry an **authorable negative assertion** — a concrete "what must NOT
happen" that a test can verify.

**Sprint target**: 3–5 promotions in Wave 2. This shortlist
deliberately over-nominates (7 candidates ranked) so Wave 2 can pick
the cheapest/highest-value subset after /review feedback.

## Shortlist

### 1. `repl/spec.md §5.1` — Errors on stdout; stderr is for traces only

- **Current annotation**: `[Tested tests/e2e::e2e_s5_1_errors_on_stdout]`
  (line 816)
- **Spec text**: "Errors MUST be written to stdout … Stderr is reserved
  for traces and diagnostic output. Errors MUST NOT crash the REPL
  session."
- **Positive path covered**: Stdout contains `error:` prefix or
  equivalent error marker.
- **Negative assertion**: Stderr is empty (or contains only trace
  output matched by the `CRANELISP_*_TRACE` patterns, never the error
  body). Distinct second assertion: session accepts subsequent input
  after the error (the "MUST NOT crash" clause).
- **Authoring cost**: **S** — one new E2E test alongside
  `e2e_s5_1_errors_on_stdout`. The existing test harness already
  captures stderr separately.
- **Priority**: **HIGH**. This is the exact shape `qa.md` flags as
  top-priority for neg coverage ("Errors display on stdout" vs "stderr
  is empty"). A regression here (error text accidentally routed to
  stderr) would pass every positive test today.
- **Proposed test**: `tests/e2e::e2e_s5_1_errors_on_stdout_neg_stderr_empty`.

---

### 2. `repl/spec.md §5.2` — Error recovery does not corrupt prior state

- **Current annotation**: `[Tested
  tests/repl_experience::type_error_does_not_corrupt_state]` (line 825)
- **Spec text**: "The session state (defined functions, types,
  modules) MUST NOT be corrupted by an error in a subsequent
  expression."
- **Positive path covered**: After a type error, a previously-defined
  symbol still resolves.
- **Negative assertion**: The *erroring* expression's partial effects
  are absent — the erroring `defn` does NOT leave a half-formed entry
  in the symbol table (e.g., calling the failed name after the error
  reports "unbound", not a half-installed signature; `/list` does not
  show the failed symbol).
- **Authoring cost**: **S–M**. Requires constructing an input that
  would partially commit state if the rollback were missing, and
  asserting that `/list` / bare-name lookup reports the pre-error
  view.
- **Priority**: **HIGH**. Session-state corruption on error is a
  Sprint 59/60-class defect shape that has surfaced before (the
  "dual-path persistence collapse" anti-pattern). A neg test here
  installs a regression guard for exactly the class of bug the
  discipline is designed to prevent.
- **Proposed test**:
  `tests/repl_experience::type_error_does_not_corrupt_state_neg_failed_defn_absent`.

---

### 3. `repl/spec.md §3.4` — `/imports` on fresh session shows only Special forms

- **Current annotation**: `[Tested tests/e2e::e2e_s3_4_imports_empty]`
  (line 502)
- **Spec text**: "In a fresh session with no explicit `(import ...)`
  and no prelude, `/imports` MUST show only Special forms. … the
  `primitives` module's implicit availability is via the module
  resolution fallback, NOT via import — so primitives do not appear in
  `/imports` unless explicitly imported."
- **Positive path covered**: Special forms present.
- **Negative assertion**: `primitives/add-i64`, `primitives/Int`,
  `primitives/eq-i64` (etc.) do NOT appear in `/imports` on a fresh
  no-prelude session. No `Fns:`, `Types:`, `Traits:`, `Macros:`
  category is printed.
- **Authoring cost**: **S**. Single E2E test with bare REPL (no
  prelude): run `/imports`, assert the output does not contain any of
  `add-i64`, `Int`, `eq-i64`, `sub-i64`, `primitives/`.
- **Priority**: **HIGH**. Module-boundary MUST NOT — exactly the
  shape `qa.md` §"Negative Test Guidance" calls out as priority
  ("Primitives are in `primitives` module … `user/add-i64` does NOT
  appear"). Ties directly to Slice 1's defect (bare-primitive-name
  resolution) — closing that defect should NOT make primitives leak
  into `/imports`, and the neg test pins that invariant.
- **Proposed test**:
  `tests/e2e::e2e_s3_4_imports_empty_neg_no_primitives_leak`.

---

### 4. `repl/spec.md §1.5.1` (§4.1.1 Functions) — `defn` display uses qualified type names, not `<closure>`

- **Current annotations**: `[Tested
  tests/repl_experience::defn_reports_type_and_name]` (line 263);
  related MUST NOT at line 259.
- **Spec text**: "A function definition MUST NOT display `<closure>`
  — the user defined a *named* function, not an anonymous closure.
  `<closure>` is reserved for anonymous function *values*."
- **Positive path covered**: `defn` produces `:Type name` in the
  universal format.
- **Negative assertion**: The display string contains neither the
  literal `<closure>` nor an unqualified type-position `Int`/`Bool`
  (spec §1.2 Fully-qualified names — "Output must NOT contain
  unqualified names where qualified names are required" per `qa.md`
  Negative Test Guidance).
- **Authoring cost**: **S**. Run `(defn f [x] x)` in REPL, assert
  output does NOT contain `<closure>` and does NOT contain bare ` Int`
  (with word boundaries around `Int` to avoid matching
  `primitives/Int`).
- **Priority**: **MEDIUM**. Display-format regression guard. The
  `<closure>` branch is a distinct code path from the anonymous-fn
  one, and a regression (e.g., a defn accidentally routed through the
  anonymous-value formatter) would be caught only here.
- **Proposed test**:
  `tests/repl_experience::defn_reports_type_and_name_neg_no_closure_marker`.

---

### 5. `repl/spec.md §4.1.1` (Functions bare-name lookup) — universal format compliance

- **Current annotation**: `[Tested
  tests/e2e::e2e_s4_1_bare_symbol_lookup]` (line 594 and §4.1.1)
- **Spec text**: "Entering a bare symbol name at the REPL MUST produce
  output following the universal format (§1.1). … No valid name MUST
  produce an opaque error."
- **Positive path covered**: Bare name yields `:Type name ;
  classification` line.
- **Negative assertion**: Two clauses. (a) The output does NOT
  contain the literal string `opaque error` or a generic error
  prefix for a defined symbol. (b) For a bare primitive after Slice
  1's fix, the output does NOT resemble the pre-fix signature (e.g.,
  does NOT say "unknown" or "not found" or "error:").
- **Authoring cost**: **S**. Define a symbol; assert bare-name output
  has no error markers. Optionally extend to the Slice 1 fix shape
  (bare `add-i64` response).
- **Priority**: **MEDIUM–HIGH**. This is the neg-coverage companion
  to Slice 1's positive fix. The positive test proves
  `add-i64` yields the expected line; the neg proves no error marker
  leaks into stdout.
- **Proposed test**:
  `tests/e2e::e2e_s4_1_bare_symbol_lookup_neg_no_error_markers`.

---

### 6. `repl/spec.md §8 (approximately) / §2.1.4 of CLI` — `--run`/`--link` mutual exclusion

- **Current annotation**: none in the grep (the MUST row at line 63
  is unannotated) — included here because it's an easy promotion to
  `[Tested+Neg]` by adding a positive `--run --link` rejection test.
- **Spec text**: "`--run` and `--link` MUST NOT be used together. If
  both are present, the binary MUST print an error to stderr and exit
  with status code 1."
- **Positive assertion**: With both flags, exit code is 1 and stderr
  contains an error message naming the conflict.
- **Negative assertion**: stdout is empty (no partial run output); no
  output file is produced (no linked binary named after the entry).
- **Authoring cost**: **S**. Single subprocess E2E. NB: this would
  land as a new `[Tested+Neg]` row, not a promotion — include only if
  Wave 2 has budget for 5 items rather than 3.
- **Priority**: **MEDIUM**. Good CLI regression guard but a fresh
  annotation rather than a promotion. **Tentative: include if budget
  allows; drop if Wave 2 is tight.**
- **Proposed test**:
  `tests/e2e::e2e_cli_run_and_link_rejected`.

---

### 7. `repl/spec.md §2.3` — Blank lines silent re-prompt

- **Current annotation**: `[Tested
  tests/repl_experience::empty_input_is_silent]` (line 355)
- **Spec text**: "Blank lines (empty or whitespace-only) MUST silently
  re-prompt with no output. The REPL MUST NOT produce an error,
  evaluation result, or any visible output — it simply presents the
  next prompt."
- **Positive path covered**: Empty input does not crash; prompt
  returns.
- **Negative assertion**: No evaluation result line is emitted (no
  `:Type value` output for the empty input); no error marker; no
  spurious `nil`/`()` output. Effectively: between the two prompts,
  stdout is empty.
- **Authoring cost**: **S**. Feed `\n\n  \n` stdin; assert the
  between-prompts stdout bytes are empty.
- **Priority**: **MEDIUM**. Clean regression guard; moderate value.
- **Proposed test**:
  `tests/repl_experience::empty_input_is_silent_neg_no_output_between_prompts`.

---

## Out of shortlist (considered, declined)

- **`spec/04-expressions.md §4.1.1` Integer Literals**
  (`[Tested tests/ring0::hello, …]`) — declined. The negative
  assertion ("non-integer tokens are not parsed as integers") is
  already covered by parse-error tests at the grammar layer; no
  per-rule neg test adds value.
- **`repl/spec.md §1.2 display table rows`** (`:primitives/Int 3`
  etc.) — declined. These rows are display formats; the neg assertion
  ("output does NOT contain bare `Int`") is better consolidated under
  candidate #4 (defn display) rather than split per type row.
- **`repl/spec.md §3.1 slash command table rows`** (`/help`, `/sig`,
  `/type`, …) — declined per row. Each is a positive "the command
  produces X" requirement; the MUST NOT surface (unknown commands
  error) is already covered by existing error tests. Promoting 17 per-row
  entries inflates annotation count without changing coverage.
- **`repl/spec.md §6.1 First Five Minutes`** — declined. It's a
  narrative requirement; the sub-steps are covered by other tests.
  Promoting the rollup does not install a new regression guard.
- **`repl/spec.md §7.1 Startup Time` (performance)** — declined. Neg
  ("startup MUST NOT exceed 500 ms") is already the positive
  assertion's contrapositive; no separate neg test adds value.

## Recommendation

**Wave 2 target set of 3 promotions** (the minimum-viable set):

1. Candidate **#1** — errors-on-stdout / stderr-empty (highest-value
   regression guard; aligns with `qa.md` priority examples).
2. Candidate **#2** — error recovery does not leave half-installed
   symbols (aligns with Sprint 59/60 defect class; installs a guard
   for "dual-path persistence collapse").
3. Candidate **#3** — `/imports` on fresh session does not leak
   primitives (aligns with Slice 1's positive fix; exact
   module-boundary shape `qa.md` recommends).

**Stretch targets** (if Wave 2 has budget):

4. Candidate **#4** — defn display has no `<closure>` marker.
5. Candidate **#5** — bare-symbol lookup has no error marker.

Candidates #6 and #7 are fresh annotations / moderate value — defer
unless /review requests broader coverage.

## Wave 5 landed (2026-04-22, Sprint 61 Slice 5 H)

All 3 recommended candidates landed; annotations promoted from `[Tested]`
to `[Tested+Neg]` in `repl/spec.md`.

| # | Candidate | Test | Status |
|---|---|---|---|
| 1 | errors-on-stdout / stderr-empty | `tests/e2e::e2e_s5_1_errors_on_stdout_neg_stderr_empty` | PASS |
| 2 | error-recovery, no half-installed defn | `tests/repl_experience::type_error_does_not_corrupt_state_neg_failed_defn_absent` | PASS |
| 3 | `/imports` fresh-session no-primitives-leak | `tests/e2e::e2e_s3_4_imports_empty_neg_no_primitives_leak` | PASS |

Stretch candidates (#4, #5): not authored Wave 5 — at /qa discretion,
budget was consumed by helper consolidation (K) and repro-handoff
migration (I). Candidates #4, #5, #6, #7 remain pending for S62 or a
later sprint.

Annotation updates landed in `repl/spec.md`:
- §5.1 line 816 — `[Tested]` → `[Tested+Neg ..., ..._neg_stderr_empty]`
- §5.2 line 825 — `[Tested]` → `[Tested+Neg tests/repl_experience::type_error_does_not_corrupt_definitions, tests/repl_experience::type_error_does_not_corrupt_state_neg_failed_defn_absent]`
- §3.4 line 502 — `[Tested]` → `[Tested+Neg ..., ..._neg_no_primitives_leak]`
- §3.1 `/imports` row (line 392) — `[Tested]` → `[Tested+Neg ...]` (row-level)

## Authoring protocol (Wave 2)

For each chosen candidate:

1. Author the test in the file indicated under "Proposed test".
2. Add the `// spec: repl/spec.md §N.M` comment per
   `CLAUDE.md §"Requirements/Test Traceability"`.
3. Update the spec annotation from `[Tested tests/foo::bar]` to
   `[Tested+Neg tests/foo::bar, tests/foo::bar_neg_…]` — `/qa` owns
   the spec-side annotation edit (the spec files remain `/repl` /
   `/spec` owned, but the `[Tested ...]` annotation is a test-side
   cross-reference that `/qa` writes per `CLAUDE.md` convention).
4. Run the test twice: once with the positive test, once with the
   implementation's error branch simulated, to verify the neg
   assertion actually triggers on the wrong outcome.
