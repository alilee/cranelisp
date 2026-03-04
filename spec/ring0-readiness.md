# Ring 0 Spec Readiness

Validation of spec completeness for Ring 0 acceptance criteria, with oracle verification and gap analysis.

**Date**: 2026-03-04
**Skill**: `/spec`
**Sprint**: 0, Task 2

## Acceptance Criteria Mapping

| # | Criterion (display per `repl/spec.md`) | Spec Section(s) | Status | Notes |
|---|---|---|---|---|
| 1 | `(+ 1 2)` → `:primitives/Int 3` | 04-expressions §4.6 (application), 07-traits §7.5 (operators as trait methods), appendix-a (inline primitives `add-i64`) | OK | `+` is a stdlib function (see §7.7 FIXME). In Ring 0 it is hard-wired as a builtin; REPL display shows its conceptual stdlib home. |
| 2 | `(defn id [x] x)` → `:(Fn [a] a) user/id` | 05-definitions §5.1 (defn), 03-types §3.4 (type schemes), 03-types §3.5 (Algorithm W, two-pass, generalization) | OK | Let-polymorphism produces the universally quantified scheme. Display uses `:Type qualified-name` format per `repl/spec.md`. |
| 3 | `(if true 1 2)` → `:primitives/Int 1` | 04-expressions §4.4 (if), 03-types §3.5.3 (if inference rule) | OK | Both-branches-required, condition-must-be-Bool, branches-must-unify all specified with examples. |
| 4 | `(let [x 5] (+ x 1))` → `:primitives/Int 6` | 04-expressions §4.3 (let), 03-types §3.5.3 (let inference rule) | OK | Sequential binding, left-to-right evaluation, body-in-extended-env all specified. |
| 5 | `(deftype Color Red Green Blue)` + `(match Color.Red [Color.Red 1 Color.Green 2 Color.Blue 3])` → `:primitives/Int 1` | 05-definitions §5.2.3 (enum), 06-pattern-matching §§6.1-6.5 (match syntax, semantics, exhaustiveness), 12-runtime §12.1.4 (nullary constructor representation), 01-lexical §1.4.4 (dotted symbols) | OK | Enum definition, nullary constructor patterns, exhaustiveness checking, bare-tag runtime representation all fully specified. No heap allocation for nullary constructors. `Type.Constructor` dot syntax per §1.4.4. |
| 6 | `(defn fact [n] (if (= n 0) 1 (* n (fact (- n 1)))))` runs correctly | 12-runtime §12.5 (tail call optimization), 03-types §3.5.4 (worked factorial example), 05-definitions §5.13.1 (forward references and recursion) | OK | Roadmap criterion updated: this formulation is NOT tail-recursive (the `*` wraps the recursive call). Criterion now says "runs correctly" and notes that TCO is exercised by accumulator-style functions. Spec §12.5 is correct. |
| 7 | Batch and REPL produce identical results (shared `compile_unit()` pipeline) | 02-grammar §§2.1 (batch and interactive modes), 12-runtime §12.6 (entry point) | OK | Roadmap clarified: "identical results" means the `compile_unit()` pipeline is shared via `CompileMode` enum. True batch mode with `main :: () -> IO _` defers to Ring 4. No spec change needed. |
| 8 | ~50 integration tests green | (Implementation-level) | N/A | Not a spec criterion. No spec gap. |
| 9 | REPL experience tests pass: discoverability, value+type feedback | `repl/spec.md` (normative REPL experience spec) | OK | REPL experience specification now exists as `repl/spec.md`, owned by `/repl`. Covers display format, slash commands, self-documentation, error presentation, discoverability, and performance targets. |
| 10 | `cargo clippy` clean, no `unwrap()` in pipeline code | (Implementation-level) | N/A | Not a spec criterion. No spec gap. |

## Oracle Verification

All examples run against the sketch compiler (REPL mode) at commit `de6f2aa`. Oracle output uses the sketch's `value :: Type` format. Reimplementation expected output uses the `:Type value` format per `repl/spec.md`.

| # | Example | Reimpl Expected | Oracle Output | Semantic Match |
|---|---|---|---|---|
| 1 | `(+ 1 2)` | `:primitives/Int 3` | `3 :: Int` | yes |
| 2 | `(defn id [x] x)` | `:(Fn [a] a) user/id` | `id :: (Fn [a] a)` | yes |
| 3 | `(if true 1 2)` | `:primitives/Int 1` | `1 :: Int` | yes |
| 4 | `(let [x 5] (+ x 1))` | `:primitives/Int 6` | `6 :: Int` | yes |
| 5 | `(deftype Color Red Green Blue)` then `(match Color.Red [Color.Red 1 Color.Green 2 Color.Blue 3])` | `:primitives/Int 1` | `1 :: Int` | yes |
| 6 | `(defn fact [n] (if (= n 0) 1 (* n (fact (- n 1)))))` then `(fact 10)` | `:primitives/Int 3628800` | `3628800 :: Int` | yes |
| 7 | `(defn id [x] x)` then `(id 42)` then `(id true)` | `:primitives/Int 42`, `:primitives/Bool true` | `42 :: Int`, `true :: Bool` | yes |
| 8 | `true` | `:primitives/Bool true` | `true :: Bool` | yes |
| 9 | `3.14` | `:primitives/Float 3.14` | `3.14 :: Float` | yes |
| 10 | `(fact 20)` | `:primitives/Int 2432902008176640000` | `2432902008176640000 :: Int` | yes |

Note: Oracle and reimplementation differ in display format only. Semantic results (value and type) match. Operator display format (`+`, `=`, `*` etc.) deferred — their stdlib home and type display depend on the §7.7 FIXME resolution.

## Gaps and Ambiguities

### Gap 1: Factorial criterion says "with TCO" but the function is not tail-recursive — RESOLVED

- **Resolution**: Roadmap criterion updated to say "runs correctly" and notes that TCO is exercised by accumulator-style formulations. The spec (§12.5) is correct.

### Gap 2: Batch mode requires IO, which Ring 0 excludes — RESOLVED

- **Resolution**: Roadmap clarified that "batch and REPL produce identical results" means the `compile_unit()` pipeline is shared via `CompileMode` enum. True batch mode with `main :: () -> IO _` defers to Ring 4 when IO arrives. No spec change needed.

### Gap 3: No spec section for core REPL display format — RESOLVED

- **Resolution**: REPL experience specification created as `repl/spec.md`, owned by `/repl`. Covers display format (`:Type value` with fully-qualified names), prompt behavior, slash commands, self-documentation contract, error presentation, discoverability, and performance targets. This is separate from the language spec — the language spec defines semantics, the REPL spec defines user experience.

### Gap 4: Roadmap match syntax does not match spec — RESOLVED

- **Resolution**: Roadmap corrected from `(match Red (Red 1) (Green 2) (Blue 3))` to `(match Red [Red 1 Green 2 Blue 3])`. Ring 1 match syntax also corrected.

### Gap 5: Ring 0 trait infrastructure scope is implicit — RESOLVED

- **Resolution**: `/arch` decided to hard-wire arithmetic/comparison operators (`+`, `-`, `*`, `/`, `=`, `<`, `>`, `<=`, `>=`, `not`) as builtins in Ring 0, deferring full trait dispatch to Ring 2. Roadmap `/typecheck` deliverables updated to make this explicit. The `ring0-interfaces.md` documents these as `ResolvedCall::BuiltinFn` entries.

## Summary

- **Spec completeness**: The spec is sufficient for implementing all Ring 0 features. Every language construct needed (literals, let, if, defn, deftype, match, function application, type inference, and builtin operators) has normative coverage with testable examples.
- **Gaps found**: 5 total — all resolved:
  - Gap 1 (factorial TCO wording): roadmap corrected
  - Gap 2 (batch mode IO): roadmap clarified — shared pipeline, IO batch defers to Ring 4
  - Gap 3 (REPL display format): `repl/spec.md` created as normative REPL experience spec
  - Gap 4 (match syntax): roadmap corrected to bracket syntax
  - Gap 5 (trait scope): roadmap explicitly states builtins in Ring 0, traits in Ring 2
- **Concurrency model updated**: `par-let` removed from spec (§4.12 deleted); lenient evaluation (§12.4.3) upgraded to MUST; auto IO scheduling (§10.12) upgraded to MUST.
- **Oracle alignment**: All 10 oracle tests match expected output. The spec examples accurately describe the language behavior.

## Next skills

- `/frontend` — Ring 0 reader and AST builder can proceed; spec sections 01-02 are complete; interface newtypes finalized
- `/typecheck` — Ring 0 inference can proceed; operators are builtins (not traits) in Ring 0; spec sections 03, 06 are complete
- `/backend` — Ring 0 codegen can proceed; spec section 12 is complete for scalar types and enums; `CompileMode` has 3 variants (Interactive, Batch, Release)
- `/qa` — Ring 0 test plan can proceed; all gaps resolved; REPL experience spec available at `repl/spec.md`
- `/repl` — REPL experience spec created at `repl/spec.md`; Ring 0 experience tests can be planned
