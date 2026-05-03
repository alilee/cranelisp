# Wave 3.5 Audit — Spec Traceability + Code Review

Sprint 64 Phase 5, Wave 3.5 (audit-and-cleanup pass between Wave 3 and Wave 4).

User-surfaced concern: `/reset` test asserted on a feature not in `repl/spec.md §3.1` Command Inventory. Concern generalised: other invented assertions may have slipped through Waves 1–3.

## Scope

Seven test files (Waves 1–3 outputs):

- `tests/cache.rs` (24 e2e tests)
- `tests/spec_11_stdlib.rs` (54 tests)
- `tests/build_confidence.rs` (4 smoke + 11 mode-equivalence = 15 tests)
- `tests/repl_introspection.rs` (39 tests)
- `tests/repl_lifecycle.rs` (29 tests pre-audit; 27 post-audit)
- `tests/repl_negative.rs` (28 tests)
- `tests/spec_10_io.rs` (26 tests)

Total: 213 tests audited (pre-audit). 211 post-audit (after deleting two `/reset` invented tests).

## Part A — Spec-traceability audit

### Per-file outcomes

| File | Total | PASS | MISSING-ANN | STALE-ANN | MIS-CITED | OVER-SPEC | INVENTED |
|---|---:|---:|---:|---:|---:|---:|---:|
| cache.rs | 24 | 24 | 0 | 0 | 0 | 0 | 0 |
| spec_11_stdlib.rs | 54 | 48 | 0 | 0 | 6 | 0 | 0 |
| build_confidence.rs | 15 | 15 | 0 | 0 | 0 | 0 | 0 |
| repl_introspection.rs | 39 | 32 | 0 | 0 | 7 | 0 | 0 |
| repl_lifecycle.rs | 29 → 27 | 12 → 27 | 0 | 0 | 15 → 0 | 0 | 2 (deleted) |
| repl_negative.rs | 28 | 24 | 0 | 0 | 4 | 0 | 0 |
| spec_10_io.rs | 26 | 16 | 0 | 0 | 10 | 0 | 0 |
| **Total** | **213 → 211** | **171 → 211** | **0** | **0** | **42 → 0** | **0** | **2 (deleted)** |

Annotations corrected during this wave; final state: every retained test is PASS.

### Findings actioned

#### 1. INVENTED tests — DELETED

Two tests in `tests/repl_lifecycle.rs` asserted on `/reset` semantics that the spec does not promise:

- `reset_clears_user_defns` — asserted that `/reset` clears user definitions.
- `reset_session_continues` — asserted session remains alive across `/reset`.

`/reset` is **NOT** in `repl/spec.md §3.1 Command Inventory`. The 21 commands listed are: `/help`, `/sig`, `/doc`, `/type`, `/info`, `/source`, `/sexp`, `/ast`, `/clif`, `/disasm`, `/list`, `/time`, `/expand`, `/mod`, `/imports`, `/exports`, `/mem`, `/run-tests`, `/run-all-tests`, `/sh`, `/quit`. No `/reset`.

**Action**: Both tests deleted. FIXME 0123 deleted. Ledger entry deleted.

#### 2. MIS-CITED — `repl/spec.md §1.6` and `§1.7` (do not exist)

`repl/spec.md` numbers Display Format subsections §1.1–§1.5; there is no §1.6 or §1.7. Tests cited these for "REPL session evaluation" and "redefinition" semantics:

- `§1.6` references → re-cited to `repl/spec.md §15.2` (Session Restore — covers eval-cycle persistence) or to `spec/05-definitions.md §5.1` (recursive defn).
- `§1.7` references (5 tests) → re-cited to `repl/spec.md §15.6` (Redefinition).

#### 3. MIS-CITED — `repl/spec.md §3.5` for `/type`

`§3.5` is `/exports`. `/type` is listed in the `§3.1` Command Inventory; there is no per-command subsection for it. Re-cited to `§3.1`.

#### 4. MIS-CITED — `repl/spec.md §3.2` for `/doc`

`§3.2` is the `/help` Output specification. `/doc` is listed in `§3.1` inventory but has no per-command subsection. Re-cited to `§3.1`.

#### 5. MIS-CITED — `repl/spec.md §11.1` for defmacro shape errors

`§11.1` is `/expand`. Defmacro shape errors are language-level errors, covered by `spec/09-macros.md §9.9 (Macro Errors)`. Re-cited.

#### 6. MIS-CITED — `repl/spec.md §1.1` for "REPL emits banner"

`§1.1` is the Universal Output Format. Startup banner is `§6.2 (Startup Banner)` and EOF behaviour is `§0.1 (REPL Mode)`. Re-cited.

#### 7. MIS-CITED — `repl/spec.md §1.5` for "blank line silent"

`§1.5` is Value Display. Blank-line / comment-only-input handling is `§2.3 (Empty and Comment-Only Input)`. Re-cited.

#### 8. MIS-CITED — `spec/06-adt.md` (file does not exist)

Six tests in `spec_11_stdlib.rs` cited `spec/06-adt.md §6.1` for Option/Result constructor behaviour. There is no `spec/06-adt.md`; ADT definition syntax lives in `spec/05-definitions.md §5.2 (deftype)` and pattern-match in `spec/06-pattern-matching.md §6.1`. Re-cited.

#### 9. MIS-CITED — `spec/10-io.md §10.10` for "main returns Pure / exit code"

`§10.10` is "Platform ABI Contract". Entry-point exit-code rules are `§10.6.1 (Exit Code)`. Re-cited (4 tests).

#### 10. MIS-CITED — `spec/10-io.md §10.3.5` (does not exist)

Three tests cited `§10.3.5` for the internal `Bind` constructor's user-invisibility. No §10.3.5 exists; the property is documented in `§10.1 (IO Type — Runtime Representation)`. Re-cited.

#### 11. MIS-CITED — `spec/10-io.md §10.4` for IO type inference / branch consistency

`§10.4` is "Expression Sequencing (Example: do Macro)". Effect propagation is `§10.7.1`; branch consistency is `§10.7.2`; deferred execution is `§10.8`. Re-cited (8 tests in spec_10_io.rs).

### No INVENTED beyond `/reset`

The `/reset` case was the only invented assertion across all 213 tests audited. Every other failing-pattern test traces to a real spec section (after annotation corrections).

## Part B — FIXME spec-validity verdict

### FIXME 0121 — `--run` does not discover `(mod ...)` declarations: **RETAIN**

`spec/08-modules.md §8.2.1 (Public Submodule Declaration)` and `§8.10 (Module Compilation Order)` make `(mod handler)` a normative form usable in any module. `repl/spec.md §0.2 (Run Mode)` requires `--run` to "compile the module graph rooted at the resolved entry module". A module graph that includes `(mod ...)` declarations on the entry module is in scope. The integration helper accepts the form; the `--run` driver does not. Genuine binary-surface defect; FIXME stands.

### FIXME 0122 — `--link` alignment-too-small linker error: **RETAIN**

`repl/spec.md §0.2.1 (Link Mode)` requires `--link` to "compile the module graph rooted at the resolved entry module and produce a linkable object file." `design/backend/executable-generation.md §3 (End-to-End Flow)` and §5 (Linker Invocation) establish that the produced .o files MUST link cleanly. Programs that REPL/`--run` accept (with mode-equivalence subset coverage proving they're valid through the canonical surfaces) MUST also link via `--link` per the single-pipeline principle (Decisions 22, 25, 41). The four affected programs (ADT/match, defmacro, Pure IO) compile on REPL/`--run` but fail under `--link`. Genuine codegen defect on the AOT path; FIXME stands.

### FIXME 0123 — `/reset` not implemented: **DELETED**

`/reset` is not in `repl/spec.md §3.1` inventory. The implementation behaviour ("command not yet available in v4 REPL") is correct: there is no spec'd behaviour for `/reset` to deviate from. FIXME deleted; tests deleted; ledger entry retired.

### New FIXMEs filed

None.

## Part C — Code review of the test edifice

### Organisation — APPROVE WITH ONE NOTE

File boundaries align cleanly with spec sections / functional clusters:

- `cache.rs` — `design/backend/module-caching.md` properties.
- `spec_10_io.rs` — `spec/10-io.md` (named after the spec file).
- `spec_11_stdlib.rs` — stdlib conformance (named after spec file).
- `repl_{introspection,lifecycle,negative}.rs` — three logical slices of REPL surface.
- `build_confidence.rs` — release-gate smoke + mode-equivalence subset.

Naming is consistent (`spec_NN_<topic>.rs`, `repl_<role>.rs`, `cache.rs`, `build_confidence.rs`). Helpers use idiomatic shape (`fn repl(lines)`, `fn repl_prims(lines)` per file as needed).

**Note (Suggestion)**: The three `repl_*.rs` files duplicate `fn repl()` / `fn repl_prims()` helpers verbatim (lines 31–41 in each of `repl_introspection.rs`, `repl_lifecycle.rs`, `repl_negative.rs`). Three near-identical 8-line copies. Candidate for `tests/helpers/repl.rs` or extension of `helpers/e2e.rs` with `Cranelisp::repl_with_prims()` shortcut. **Defer to S65** — not blocking.

### Maintainability — three issues, all minor

1. **Section comment headers cite spec sections in free-form prose** ("`§1.6`", "`§3`"). When the underlying citation is wrong, the section header propagates the error. Wave 3.5 fixed all 42 mis-cites at the per-test level; the section-header citations are now consistent with per-test citations. **Future suggestion**: drop section-header citations entirely; the per-test `// spec:` comment is the load-bearing trace.

2. **Some assertions do contains-checks that are wider than ideal.** Example: `repl_lifecycle::type_error_preserves_prior_defs` asserts `out.stdout.contains(":primitives/Int 42")` after a type error. A REPL that printed `:primitives/Int 42` for a different test case in the same session would also pass — but in piped REPL mode the input is one shot, so this concern is purely theoretical. **Defer**.

3. **`spec_11_stdlib.rs` ADT tests use match-expression witnesses to disambiguate top-level type variables**, which is the right approach for REPL canonical (per Wave 2.5 PLAN.md decision) but produces tests that look more complex than they are (`(match (Some 7) [(Some x) (= x 7) None false])` to test "`Some 7` constructs"). **No action** — this is the correct Wave 2.5 shape; documenting the rationale once at the top of the file would help readability. **Suggestion**.

### Duplication — flagged

| Location | Pattern | Action |
|---|---|---|
| `repl_{introspection,lifecycle,negative}.rs` lines 31–41 | `fn repl(lines)` + `fn repl_prims(lines)` 8-line stubs ×3 | Suggestion: factor to `tests/helpers/repl.rs` or add to `Cranelisp` builder. **Defer to S65**. |
| `cache.rs` `fn project(files)` (40-44) | Helper specific to cache.rs; not duplicated elsewhere. | OK — local helper for clarity. |
| `spec_11_stdlib.rs` `assert_repl_eval_contains` + `assert_repl_lines_contain` (35-64) | Local helpers; not duplicated. | OK. |

No assertion-level duplication across files (i.e., the same `(stdin, expected)` pair) beyond what is intentional (regression guards repeating in different contexts — e.g., `display_int_result` lives in both `repl_introspection.rs` and `repl_lifecycle.rs` because they're testing different surfaces of the same property).

### Individual test cleanliness — APPROVE

Tests average ~6 lines, single behaviour per test, clear arrange-act-assert. No incidental complexity from harness limitations observed. Minimal program shapes (e.g., `(defn main [] 42)`). Test names describe behaviour not implementation.

Outliers:

- `repl_lifecycle::redefinition_propagates_through_callers` (lines 174–187) — asserts both `:primitives/Int 20` AND `:primitives/Int 10` are in the same stdout, with a manual `&&` rather than a single `assert_stdout_contains`. The shape is correct (need to assert both). Could factor to `assert_stdout_contains_all(&[...])` on `CrOutput`. **Suggestion**.

- `repl_lifecycle::many_sequential_evals` (lines 334–352) — builds 20-form input dynamically, then prints last-5-lines on failure. The build-then-tail pattern is well-suited to fold the failure-printing into a helper. **Suggestion**.

### Harness quality — APPROVE

`tests/helpers/e2e.rs` (1070 LOC) is coherent: builder → invocation → output, with clear separation of concerns. No internal-state leaks. Builder methods are consistent (each `fn` returns `Self`). The mode-equivalence helper (Wave 2.5) cleanly extends without intrusion. `CrError` enum captures all failure modes pre-output.

`tests/helpers/regex.rs` (64 LOC) is minimal: 4 named regexes + 2 mask helpers. The `mod compiler` namespace makes the surface easy to grow.

One concern: `CrOutput::run_again()` consumes the `_td` field (lines 731–747); calling it twice would panic with "TempDir already consumed". The error message is clear but the API doesn't enforce single-call statically. **Defer** — currently no caller would naturally hit this.

## Part D — Corrections actioned

| Commit | Files touched | Intent |
|---|---|---|
| 1 | `tests/repl_lifecycle.rs`, `tests/plan/ledger.md`, `design/arch/fixmes/0123-int-reset-not-implemented.md` (deleted) | Retract `/reset` invented assertion: delete two tests, retire ledger entry, delete FIXME 0123. |
| 2 | `tests/repl_lifecycle.rs`, `tests/repl_introspection.rs`, `tests/repl_negative.rs`, `tests/spec_10_io.rs`, `tests/spec_11_stdlib.rs` | Spec-traceability annotation corrections (42 mis-cites). |
| 3 | `tests/plan/wave-3.5-audit.md` (new) | Wave 3.5 audit findings record. |

(Commits land at sprint discretion; staged changes verified `cargo check --tests` clean.)

## Recommended actions for `/sprint` before Wave 4

### Required (blocker)

None.

### Recommended (Important)

- **Add a `// spec:` annotation linter or pre-commit check**: scan `tests/*.rs` for tests citing `repl/spec.md §X.Y` or `spec/NN-*.md §X.Y` and verify the section heading exists in the cited file. The 42 mis-cites Wave 3.5 found would have been caught at landing time. Authoring this lint as a `tests/plan/` Python script is a one-evening task; can land in S65. **File as FIXME against `/qa`**.

- **Annotate Wave-4+ outputs with `// spec:` verification at landing time**: add a row to the per-batch closing checklist in `tests/plan/PLAN.md` requiring the author (`/qa`) to grep the cited spec section before committing. Manual until the linter lands.

### Suggested (defer to S65 or later)

- Factor `fn repl()` / `fn repl_prims()` to a shared helper used by all three `repl_*.rs` files (8 LOC × 3 → 1 helper).
- Add `assert_stdout_contains_all(&[...])` convenience method on `CrOutput`.
- Drop spec-section citations from section-comment headers; rely on per-test annotations.

## Wave 3.5 gate verification

| Criterion | Yes/No |
|---|:---:|
| Every test in 7 new e2e files audited; outcome recorded | YES |
| Invented tests deleted; spec annotations added/fixed where possible | YES |
| FIXMEs 0121, 0122 verified (each retained or retracted with rationale) | YES |
| FIXME 0123 deleted | YES |
| Code-review findings recorded | YES |
| `cargo check --tests` clean | YES |
| `tests/plan/ledger.md` integrity restored | YES |

## Final note for `/sprint`

The `/reset` regression illustrates that **landing-time spec verification is not optional** when authoring large test batches. Wave 3 ported 5,429 LOC + 285 source tests across REPL surfaces and produced 96 e2e tests in three files; one slipped through with an invented assertion. The probability of authoring something that "looks like spec" but isn't is high enough that batch-level audits are the wrong granularity — the audit needs to fire per-test at landing time. The recommended `/qa`-targeted linter (above) is the durable mitigation. Until it lands, the `tests/plan/PLAN.md` per-batch checklist should explicitly include "grep each cited section in spec".

A second observation: the user-surfaced concern was the right level of skepticism. Two `/reset` tests that look reasonable (the assertions are well-formed; the FIXME is well-written) survived /qa landing, /sprint waves-2-vs-3 review, and a Wave 2 → 2.5 pivot. The single guard that caught it was a user reading the FIXME. **Wave 4+ work should bake user-surfaceable assertions into the audit at landing**, e.g., per-test `// spec:` cited and grep-verified, with the link rendered in the commit message for trivial post-hoc verification.

The Wave 3.5 audit confirms the rest of Waves 1–3 is sound. No further INVENTED assertions found; FIXMEs 0121 and 0122 are real defects.
