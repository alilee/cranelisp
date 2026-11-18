# Appendix D: Open Requirement Questions

Owner: `spec`. The user decides open normative questions; proposals are
non-normative.

The S123-Q1–Q11 user rulings of
2026-11-15 are recorded in their normative homes: runtime §12.4.3 and §12.7,
IO §10.10.1, modules §8.9.3, and REPL §0.5.6, §0.8, §14.9 and §16.
The decision source is [Sprint 123, Phase 3 user rulings](../sprints/archive/sprint-123.md#user-rulings-on-the-phase-3-decisions-2026-11-15).

S123-Q12 is retired: the [W3 user ruling, 2026-11-16](../sprints/archive/sprint-123.md#user-rulings-in-w3-2026-11-16)
removes the recreation consent requirement. The current rule is recorded in
[REPL §14.9](../repl/spec/14-file-watching.md#149-backing-file-appearance-and-deletion).

## S124-Q1: Representation claims after the value-flattening retirement

**Closed — user ruling, 2026-11-16**, recorded as “S124-Q1 ruled” in
[Sprint 124 Notes](../sprints/SPRINT.md#user-rulings-on-the-phase-2-decisions-2026-11-16).
[REPL §1.5](../repl/spec/01-display-format.md#15-value-display) drops the claim
that a single-constructor, single-scalar-field ADT is stored flattened and keeps
its constructor-form, recursive, no-sentinel and no-crash display guarantees as
ordinary requirements. Language [§12.1.1](12-runtime.md#1211-scalar-types)
no longer describes flattening or stack placement as current backend
capabilities, following their retirement in S124 scope item 4.

## S124-Q2: May a macro rest parameter be a bracket pattern?

**Closed — user ruling, 2026-11-17**, candidate A, recorded as “S124-Q2 to Q6
ruled” in [Sprint 124 Notes](../sprints/SPRINT.md#user-rulings-on-the-phase-2-decisions-2026-11-16).
[§9.2.1](09-macros.md#921-syntax) requires a symbol after the macro rest marker
and rejects `[& [a b]]`. Fixed bracket parameters and rest capture inside a
bracket pattern remain permitted.

## S124-Q3: Where within a defmacro must a return mismatch point?

**Closed — user ruling, 2026-11-17**, candidate A, recorded as “S124-Q2 to Q6
ruled” in [Sprint 124 Notes](../sprints/SPRINT.md#user-rulings-on-the-phase-2-decisions-2026-11-16).
[§9.9.1](09-macros.md#991-return-type-mismatch) locates a return-type mismatch
at the offending clause body within the defining `defmacro` form.

## S124-Q4: Export mount and import alias sharing a spelling

**Closed — user ruling, 2026-11-17**, candidate B and the definite no-op
companion ruling, recorded as “S124-Q2 to Q6 ruled” in
[Sprint 124 Notes](../sprints/SPRINT.md#user-rulings-on-the-phase-2-decisions-2026-11-16).
[§8.4.4](08-modules.md#844-module-mounting-on-export) and its
[§8.6.4](08-modules.md#864-module-scope-candidate-registration) reference
allow an import alias and export mount sharing a spelling to form one public
route when their canonical targets agree; different targets are rejected in
either declaration order. The unaliased empty export `(export [m []])` is
accepted as a no-op, loading nothing; the aliased mount-only form still mounts.

## S124-Q5: In-place function redefinition gains a later macro dependency

**Closed — user ruling, 2026-11-17**, candidate A with its ordering policy,
recorded as “S124-Q2 to Q6 ruled” in
[Sprint 124 Notes](../sprints/SPRINT.md#user-rulings-on-the-phase-2-decisions-2026-11-16).
[REPL §15.4 rule 2](../repl/spec/15-session-persistence.md#154-regeneration-integrity)
moves a redefined function after a macro it newly depends on when the macro
follows the function's original position. The authorship-intent explanation
carries the same exception. Language
[§9.3.4](09-macros.md#934-macro-availability-and-definition-order)'s
source-ordered macro availability remains unchanged.

## S124-Q6: Must a save completed by /sh be reported before its next prompt?

**Closed — user ruling, 2026-11-17**, candidate A, recorded as “S124-Q2 to Q6
ruled” in [Sprint 124 Notes](../sprints/SPRINT.md#user-rulings-on-the-phase-2-decisions-2026-11-16).
[REPL §14.2](../repl/spec/14-file-watching.md#142-eager-recompilation)
requires a watched save completed by a turn's own `/sh` to be rebuilt and its
result reported before that turn's next prompt, regardless of filesystem
notification delivery. Design owns how recognition is ensured.

## S124-Q7: Does impl re-entry at a different type count as polymorphic recursion?

**Closed — user re-ruling, 2026-11-17, B**, superseding the same-day A ruling.
[§3.10](03-types.md#310-rank-1-hindley-milner) treats a trait dispatch from an
implementation's body to that same implementation at another instantiation as
ordinary dispatch, whether direct, through a constrained helper function, or
through another implementation. The monomorphic-recursion rule for functions
is unchanged.

**Depth and reporting follow-up — user rulings, 2026-11-17.** §3.10 records
an instantiation depth limit of at least 64, with a type error for a chain
exceeding that limit. A growing re-entry is accepted when declared; the error
is reported when an instance is demanded, in the REPL on the turn that first
demands it.

## S124-Q8: What location must a “no main” refusal report?

**Closed — user ruling, 2026-11-17**, candidate B, recorded as “S124-Q8
ruled B” in [Sprint 124 Notes](../sprints/SPRINT.md#user-rulings-on-the-phase-2-decisions-2026-11-16).
[REPL §5.5](../repl/spec/05-error-presentation.md#55-compiler-stage-diagnostics-name-user-facing-subjects)
requires a missing-`main` refusal in `--run` or `--link` to name the existing
entry file and the missing `main` without a form span, as an explicit exception
to its form-span rule. [REPL §5.1](../repl/spec/05-error-presentation.md#51-error-format)
references that exception to its source-location requirement. Refusals about
an existing `main` definition retain the form-span requirement.

## S124-Q9: Does a trait method named main define the program's main?

**Closed — user ruling, 2026-11-17, no (candidate A).**
[§10.6](10-io.md#106-entry-point) requires an ordinary function definition.
A trait method named `main` does not define the program's `main`, so the
“no `main`” refusal stands. The same reading retains refusal of the multi-arity
`(defn main ([] …) ([x] …))`, despite its zero-argument variant; the user was
told that consequence and requested no different treatment.
