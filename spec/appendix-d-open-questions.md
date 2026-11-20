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

## S124-Q10: What does /type report for a non-value form?

**Partly recorded — user ruling, 2026-11-20:** “I think refuse or just
`defn`”, in the [Phase 6b checkpoint](../sprints/SPRINT.md#user-rulings-on-the-phase-2-decisions-2026-11-16).
[REPL §3.1](../repl/spec/03-slash-commands.md#31-command-inventory) records
refusal of a form with no value type and retains the earlier rule that `defn`
reports its function type without defining anything. The existing prohibition
on evaluating a non-pure form is unchanged.

**Open problem.** “Or just `defn`” does not unambiguously settle whether
`defn` is the only accepted definition form, or whether any definition form
with a value type is accepted. For example, §9.6 illustrates a `def` macro
expanding into a function and a macro; the ruling does not say whether a query
on such a definition is refused or has a report. The recorded refusal of
no-value forms does not choose that boundary.

**Options / tradeoffs.** Restrict definition queries to `defn`: the accepted
surface is explicit, but macro-defined definition syntax may be refused.
Accept other value-bearing definitions: preserves §3.1's broader definition
wording, but needs a rule for which type a multi-definition expansion reports.
The user must settle this boundary before Q10 can close.

## S124-Q11: Must multi-parameter collection traits be expressible now?

**Open problem — audit R7.** Opened
[Appendix C §C.2.4](appendix-c-nfr.md#c24-collection-extensibility-s24), which
says “Multi-parameter traits … MUST be expressible”, and
[§7.12.1](07-traits.md#7121-current-restrictions), which says “No
multi-parameter type classes.” Appendix C is normative; these requirements
conflict. Its “Activation: Ring 2” does not supply a current scheduling rule
under the retired ring axis. §7.12.2's future-extension entry concerns
multi-parameter HKT and does not itself settle the container/element example.

**Options / tradeoffs.** Require multi-parameter collection traits now and
revise §7.12.1: preserves C.2.4's obligation but widens the required language
surface, needing syntax and typing decisions. Retain the single-parameter
restriction and move C.2.4's multi-parameter clause to future intent: keeps the
current restricted surface but removes its present expressibility guarantee.
Explicitly defer the obligation to a user-named milestone: retains the desired
outcome but requires a current applicability boundary. No option is selected.

## S124-Q12: Does unquote-splicing require a library-provided sconcat?

**Open problem — ACT-1095.** Opened
[§11.4](11-stdlib.md#114-writing-a-standard-library),
[§9.7.0](09-macros.md#970-visibility), and the filing's source targets
`crates/cranelisp-frontend/src/quasiquote.rs` (`make_sconcat`),
`stdlib/core/syntax.cl`, and `stdlib/plan-stdlib.md` §6.5. Non-normative §11.4
says a library using `~@` must provide `core.syntax/sconcat`; normative §9.7.0
also locates `sconcat` in `core.syntax` and says it is re-exported through the
prelude because quasiquote-generated code uses it. The expander instead emits
`macros/sconcat`; `core.syntax` defines no such function. Implementation
behavior cannot settle the normative text. §9.4.2 defines splicing's result
but does not identify who supplies concatenation.

**Options / tradeoffs.** Make splicing independent of any standard library
and remove the library dependency from §9.7.0 and §11.4: permits empty-library
use and agrees with the observed implementation, but requires approval to
change the macro chapter. Retain a library-supplied dependency: preserves that
wording but requires the compiler and library to meet it and limits splicing
without a library. The user must decide the dependency; any mandated helper
path also needs confirmation. ACT-1095 remains unresolved pending that ruling.

## S124-Q13: What are a trace root's name, parameters and children?

**Open problem — ACT-1094's spec question.** Opened
[§4.12.2](04-expressions.md#4122-semantics),
[§4.12.4](04-expressions.md#4124-the-trace-adt), and
[§4.12.8](04-expressions.md#4128-examples). §4.12.2 leaves `root_name` and
`root_params` unspecified. §4.12.4 describes the name as the fully qualified
name of the traced function. §4.12.8 shows `(trace (fact 5))` returning a root
named `user/fact` with parameters `5` and recursive calls as children; the
composed-call example likewise starts at the called function. QA reports a
synthetic `::trace::` root with no parameters and the called function as its
child. The examples do not settle the root for an arbitrary expression, such
as `(trace 42)`. The root's formatted-result obligation is already explicit
and is independent of this question.

**Options / tradeoffs.** Always use a synthetic expression root with no
parameters and all recorded calls beneath it: gives every expression one
shape, but requires changing the examples and specifying the synthetic name.
Use the called function as root for a direct-call expression, with a separate
rule for other expressions: preserves the direct-call examples but gives
consumers different shapes. The user must choose the root naming, parameters
and tree shape; no example is changed pending that ruling.

## S124-Q14: Can a project file be a child of a library-resolved parent?

**Open problem — ACT-1096's spec question.** Opened
[§8.1.1](08-modules.md#811-naming-rules),
[§8.2.5](08-modules.md#825-file-resolution), and
[§8.11.2](08-modules.md#8112-module-resolution-search-order).
§8.1.1 says “A file `foo/bar.cl` defines module `foo.bar` (a submodule of
`foo`).” §8.2.5 requires a declared child's file at
`{parent_dir}/{stem}/{name}.cl` only, so a declaration in `lib/m.cl` loads
`lib/m/t.cl`; a project file cannot replace that declared child via a new
search. §8.11.2 permits project modules to shadow library modules. These rules
do not settle how a separate `{project_root}/m/t.cl` participates when `m`
itself resolves to `lib/m.cl`, including a collision with its declared `m.t`.

**Options / tradeoffs.** Permit an independently resolved project `m.t`:
preserves path-derived identity and project shadowing, but needs an identity
and collision rule when the library already declares `m.t`. Reject the mixed
hierarchy: gives one parent source tree, but needs the error trigger specified
(file presence or attempted use). Ignore the project child while the parent
resolves to the library: keeps the library subtree together, but limits
project shadowing. No option changes §8.2.5's already-settled declared path.

## S124-Q15: When is an undefined name in a default method reported?

**Open problem — ACT-1097's unclassified lead.** Opened
[§7.1](07-traits.md#71-trait-definition) and
[§7.1.5](07-traits.md#715-default-method-implementations).
§7.1.5 says “The default body is not type-checked once for the trait; it is
instantiated per impl” and an overriding impl “never instantiates the template”.
It also stores defaults as raw S-expressions and type-checks a synthesized
method when an impl omits an override. This settles per-impl type checking
and constraint discharge, but does not explicitly settle an earlier check
for undefined names. QA's example is `(deftrait T (f [self] (nosuch self)))`
with no implementing `impl`: must the declaration itself be refused?

**Options / tradeoffs.** Resolve default-body names at the trait declaration:
reports a missing function early, but rejects an unused template even when
every impl would override it; it must remain distinct from the per-impl type
check. Defer the undefined-name error until an impl instantiates the default:
permits unused or overridden templates, but reports mistakes later. The user
must decide the reporting point; the existing per-impl typing rule is unchanged.
