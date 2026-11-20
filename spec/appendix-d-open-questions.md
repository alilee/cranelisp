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

**Closed — user ruling, 2026-11-20.** The user's message, verbatim:

> I think it should error - "definition form has no type"

[REPL §3.1](../repl/spec/03-slash-commands.md#31-command-inventory) records
the error requirement for a definition form, retaining no evaluation and no
session definition. The provisional keyword answer is removed.

“Definition form” is already identified by [language §5](05-definitions.md),
whose opening states its scope as the top-level definition forms;
[§5.14](05-definitions.md#514-summary-of-top-level-forms) summarizes them.
Which forms belong to that class is therefore not an open remainder of Q10.
The diagnostic phrase is treated as illustrative wording, not an exact-output
requirement: [REPL §5.1](../repl/spec/05-error-presentation.md#51-error-format)
requires a human-readable message but prescribes no exact wording for this
error, and the ruling is not presented as a display-format transcript.

## S124-Q11: Must multi-parameter collection traits be expressible now?

**Closed — user ruling, 2026-11-21.** The user's message, verbatim:

> this is a future direction, but we need to stabilise what we have so far
> before we expand. let's consolidate the documentation on no-multi for now,
> so it is consistent.

[§7.12.1](07-traits.md#7121-current-restrictions) stands: traits take a single
type parameter (or single type constructor for HKT).
[Appendix C §C.2.4](appendix-c-nfr.md#c24-collection-extensibility-uncovered-s124--was-s24)
removes the present multi-parameter expressibility obligation and retired-ring
activation line; multi-parameter collection traits are a non-normative future
direction, also recorded in [§7.12.2](07-traits.md#7122-future-extensions).
The ruling is recorded in [Sprint 124 Notes](../sprints/SPRINT.md#notes).

## S124-Q12: Does unquote-splicing require a library-provided sconcat?

**Closed — user ruling, 2026-11-21**, recorded in
[Sprint 124 Notes](../sprints/SPRINT.md#notes):

> agreed - all language features should be self-sustaining and there should
> be builtins or primitives for any required helpers.

[§9.7.0](09-macros.md#970-visibility) and
[§11.4](11-stdlib.md#114-writing-a-standard-library) remove the library
requirement for unquote-splicing and state that the compiler provides its
concatenation. The general principle is recorded in
[§8.8.3](08-modules.md#883-empty-prelude).
ACT-1095 is resolved. Its claim was verified by opening §11.4, §9.7.0,
`crates/cranelisp-frontend/src/quasiquote.rs` (`make_sconcat`),
`stdlib/core/syntax.cl`, and `stdlib/plan-stdlib.md` §6.5: the expander emits
`macros/sconcat`, while `core.syntax` defines no `sconcat`.

**Open remainder — S124-Q12-R1: user-callable concatenation helper.** The
macro chapter's existing visibility rules cover library helpers and qualified
compiler-seeded constructors; they do not decide whether the concatenation
helper used by `~@` is itself a name users may call. Neither a callable name
nor its public visibility is settled by this ruling.

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

## S124-Q16: Core/library classification and stage-two specification revision

**Open — stage two waits on `arch` determinations and user confirmation.**
The user ruling of 2026-11-21, recorded in
[Sprint 124 Notes](../sprints/SPRINT.md#notes), is stated normatively once in
[§8.8.3](08-modules.md#883-empty-prelude). This inventory records the passages
that need reconciliation with that rule; it does not change their requirements
or decide implementability. `arch` determines the unresolved technical questions
below; the completed classification returns to the user before `spec` rewrites
any inventoried passage. Stage two then removes the specification's reliance on
the prelude and separates language obligations from library descriptions and
examples according to the confirmed classification.

### Inventory

This is a non-normative inventory of `spec/`, `repl/spec.md` and `repl/spec/`
at the S124 stage-one checkpoint. Rows group related spellings with the same
dependency and decision; the section column identifies definitions and dependent
passages, including examples. It includes dependencies already supplied by the
compiler where bare-name examples or conflicting prose still assume the prelude.
References to module search paths or to introspection of whatever names happen
to be imported are not, by themselves, dependencies on particular library content.

**Library** records an explicit library designation in existing normative text
or the user's `cond` example. **Language** records explicit compiler provision
in existing normative text or Q12. **Needs determination** leaves conflicting
or undecided ownership open and states the technical question for `arch`.
These labels do not add requirements or promote non-normative reference text
into authority. Section numbers in the table refer to language chapters unless
prefixed REPL, A, B or C; the chapter map is in the [specification index](index.md).

| ID | Construct | Sections carrying or relying on it | What the passages rest on | Classification / precise outstanding question |
|---|---|---|---|---|
| CL01 | `const`, `const-` | §2.2, §2.6; §5.1 binder rules, §5.6, §5.14; §9.2.2, §9.5, §9.10.1; REPL §11 | Prelude macro; `quote-sexp`; zero-argument `defmacro`; bare operators in examples | **Library** — §5.6 explicitly says prelude macro, not special form. |
| CL02 | `def`, `def-` | §2.2, §2.6; §5.1 binder rules, §5.7, §5.14; §9.2.2, §9.6, §9.10.2, §9.12; REPL §11 | Prelude macro; `make-def-name`, `quote-sexp`, Sexp constructors, `begin`, generated function/macro pair | **Library** — §5.7 explicitly says prelude macro, not special form. |
| CL03 | `derive`, `derive-Eq`, `derive-Ord`, `derive-Display` | §7.13.1–§7.13.5 | Prelude macro and per-trait helper macros; `Eq`, `Ord`, `Display` and their methods | **Library** — §7.13 explicitly says prelude macro, not special form. |
| CL04 | `Num`, `Eq`, `Ord`, `Display`; arithmetic/comparison operators and `show` | §3.6–§3.7 examples; §7.1, §7.3, §7.6–§7.8, §7.13; §9.10; §12.9; B; REPL §1.1, §4.1, §17.19.2 | Library trait declarations and primitive-type impls according to §7.7, but the same subsection also calls them compiler-seeded infrastructure; bare operators and `show` throughout examples | **Needs determination** — which of these declarations, impls and methods require compiler provision, and which are expressible entirely in the specified language? §7.7 gives conflicting accounts. |
| CL05 | `Functor`, `fmap` | §3.7; §7.2, §7.7.5, §7.8; B introduction | User/library higher-kinded trait and collection implementations | **Needs determination** — is the illustrated `Functor` declaration and each described `fmap` implementation expressible entirely in the specified type system? §7.7 labels them library content but is expressly non-normative. |
| CL06 | `pure` | §3.2.3; §10.2, §10.3 examples, §10.5–§10.8; §12.4; B.12–B.13 | Ordinary wrapper around `Pure`; prelude supplies the bare name | **Library** — §10.2 explicitly says ordinary library function and gives its definition. |
| CL07 | `bind` | §3.2.3; §9.10.5; §10.3–§10.5, §10.8, §10.12; §12.4; B introduction | §3.2.3 says library-definable; §10.3 requires an inline primitive constructing an internal `Bind` node | **Needs determination** — is `bind` expressible in the type system as specified, including its two result types and continuation, or does it require a built-in? The user's recollection is conditional, not a ruling on this fact. |
| CL08 | `do` | §5.1.1; §9.10.4; §10.4, §10.5.3; §12.4–§12.5; B | Prelude macro and `do-build`; §9.10.4 shows nested `let`, §10.4 shows nested `bind` | **Library** — §10.4 explicitly says library macro, not language requirement. The two expansion accounts remain for stage two. |
| CL09 | `bind!` sugar | §9.10.5; §10.5, §10.12; §12.4; B.4, B.13 | Prelude macro, `bind!-fold`, `bind` and `fn`; §10.12 additionally requires compiler analysis of its chains | **Library** — §10.5 explicitly says library macro, not language requirement. The scheduling dependency is separately inventoried in CL10. |
| CL10 | Automatic scheduling, resource ordering and launch rules expressed over `bind!` / `do` chains | §10.12.1–§10.12.10; §12.4.1, §12.4.3–§12.4.4, §12.5; C.3.2 | Language obligations name library sugar as the analysis/sequencing surface | **Needs determination** — can all specified scheduling, source ordering, discarded-result and cancellation behavior be expressed over the core IO composition after user/library expansion, or is compiler recognition of some sugar required? |
| CL11 | `cond` | §9.10.8; B introduction | Prelude macro, `cond-fold`; nested `if` expansion | **Library** — the user's explicit example in the 2026-11-21 ruling. |
| CL12 | `case` | §9.10.9 | Prelude macro, `case-fold`, Sexp constructors; library equality `=` | **Library** — §9.10 identifies it as a prelude macro. |
| CL13 | `when`, `unless` | §9.10.12; B.6 | Prelude macros; `if` and `Option` constructors `Some` / `None` | **Library** — §9.10 identifies them as prelude macros. |
| CL14 | `->`, `->>` | §9.2.2, §9.10.6–§9.10.7; B.8 | Prelude macros; `thread-first-fold`, `thread-last-fold`; library functions in sample pipelines | **Library** — §9.10 identifies them as prelude macros. |
| CL15 | `list` | §9.10.3, §9.10.7; B introduction; REPL §3.7 | Prelude macro; `sfold`, `sreverse`; library `List`, `Cons`, `Nil` | **Library** — §9.10 identifies it as a prelude macro. |
| CL16 | `vec` macro (distinct from bracket literal) | §2.3.9; §9.10.10; B introduction | Prelude macro producing `SexpBracket` | **Library** — §2.3.9 explicitly excludes `vec` from core syntax and reserved names. |
| CL17 | `str` | §9.10.11; B introduction | Prelude macro, `str-fold`; `show` and `str-concat` | **Library** — §9.10 identifies it as a prelude macro. |
| CL18 | `sfold`, `sreverse`, `sempty?` | §9.7.0–§9.7.4, §9.10.3 | Optional `core.syntax` helper functions or local equivalents | **Library** — §9.7 explicitly designates optional library helpers. |
| CL19 | User-callable `sconcat` | §9.7.3; Q12-R1 | Library helper description beside compiler-provided splice concatenation | **Needs determination** — can the documented general `(SList a)` concatenation be supplied entirely by user/library code, separately from the compiler helper? Public callability of the compiler helper remains the user's Q12-R1 question. |
| CL20 | `slist` | §9.7.5, §9.10.3; B.6 | Convenience macro over compiler-seeded `SCons` / `SNil`; absent from §9.7.0's named helper list | **Needs determination** — can the full described `slist` convenience macro be supplied entirely by user/library code, or does it require any compiler-only facility? |
| CL21 | Named macro-building helpers | §9.2.2, §9.10.2–§9.10.11 | `make-def-name`, `do-build`, `bind!-fold`, `thread-first-fold`, `thread-last-fold`, `cond-fold`, `case-fold`, `str-fold` are used but not defined there | **Needs determination** — can each helper required by these sample definitions be implemented using the specified macro/type system and primitives? Identify any missing language facility without making the helpers language requirements. |
| CL22 | `List`, `Cons`, `Nil` | §3.2.2, §3.7 examples; §5–§7 examples; §9.10.3; §12.4.4, §12.9.3; B; REPL §1.5, §3.7, §9 | User-visible list ADT, prelude constructors and display examples | **Library** — §9.1.1 distinguishes the user/library `List` from compiler `SList`; §9.10.3 describes its library macro. |
| CL23 | `Seq`, `SeqCons`, `SeqNil` and lazy-tail behavior | §4.11; §7.7.5; §12.4.2; B introduction; REPL §1.5, §9 | Library thunk-based lazy sequence ADT, also named by runtime and display requirements | **Library** — §4.11 explicitly calls `Seq` a library-level construct. |
| CL24 | Collection/pipeline helpers `map`, `filter`, `reduce`, `inc`, `vec-map`, `vec-reduce`, `map-list`, `seq-map`, `filter-list`, `vec-filter`, `fold-list`, `count`, `get`, `conj`, `assoc`, `first`, `rest`, `second`, `head`, `to-list`, `take`, `lazy-take`, `lazy-drop`, `range-from`, `iterate`, `repeat` | B.5, B.8–B.9; §7.7.5, §7.12.2; §9.10.6–§9.10.7; §11.4a; A.3 | Library functions/trait methods, concrete-family wrappers and prospective naming reservations | **Needs determination** — are all the collection operations used by these examples expressible with the specified type system and primitives? The library labels in §7.7, §11.4a and A.3 are non-normative; future trait design remains future. |
| CL25 | `Option`, `Some`, `None` | §3.2.2 examples; §7.13; §9.10.12; §10.12.8; §12.4.4, §12.7.3, §12.7.6; A.3; B; REPL §16 | Prelude/user ADT in examples, but checked primitives, timeout and test protocols require it; REPL §16.3 calls it a primitives bootstrap type | **Language** — REPL §16.3 explicitly retains primitive bootstrap `Option`. Bare-name provisioning and user-defined examples still need reconciliation. |
| CL26 | `Result`, `Ok`, `Err`; `Pair`, `first`, `second` | §3.2.5–§3.2.6; §12.7.7; A.2–A.3; B.3; REPL §16 | Compiler-seeded ADTs versus user definitions and bare field/constructor examples | **Language** — §3.2.5–§3.2.6 explicitly seed them in `primitives`; user examples must not be mistaken for required library definitions. |
| CL27 | Bare primitive names, including scalar types, `parse-int`, `str-concat`, Vec and arithmetic primitives | §2–§10 examples; §9.11.2; §12 examples; A; B; REPL examples | Prelude re-exports or explicit imports are needed for bare names, although qualified primitive paths are independent | **Language** — §3.1 and §8.9.1 explicitly provide qualified access without imports. This row records scope assumptions, not a new required primitive catalog. |
| CL28 | Quasiquote / unquote-splicing and concatenation | §9.4, §9.7.0; §11.4; Q12 | Compiler-seeded `macros` constructors and compiler-provided concatenation; prior library-helper dependency removed by Q12 | **Language** — Q12 and §9.7.0 explicitly require library-independent splicing. No determination of a user-callable helper follows. |
| CL29 | `quote-sexp`, Sexp / SList constructors | §8.9.2; §9.1, §9.5, §9.11.1; B.6 | Compiler provision, but bare constructor and helper names in samples require imports; qualified expansion references are already specified | **Language** — §8.9.2 and §9.1 explicitly provide compiler-seeded macro data; §9.11.1 identifies the primitive. |
| CL30 | `trace-show-tree` | §4.12.8; §11.5 | `core.trace` display helpers over the compiler-seeded `Trace` ADT | **Library** — §4.12.8 explicitly identifies this as a stdlib display function; §11.5 describes it. The trace form itself is language-provided. |
| CL31 | `timeout` | §10.12.8–§10.12.10; §12.4.4; C.3.2 | A documented stdlib derivation from `race`, `sleep` and `Option`, while §12.4.4 calls it part of the language IO model | **Needs determination** — is the complete required timeout behavior implementable by a user/library derivation with the specified typing and cancellation, and which underlying facilities must be primitive? |
| CL32 | `race`, `select`, `sleep` | §10.12.8–§10.12.10; §12.4.4; C.3.2 | Runtime IO nodes and timer/first-completion support; ordinary-function signatures do not establish user implementability | **Needs determination** — which of these functions can user/library code express using the specified core IO facilities, and which require compiler/runtime provision? |
| CL33 | `discover-here`, `format-test-run`, `failures-only`, `test-passed?` | A.3; REPL §16.3, §16.5 | Optional testing library sugar and presentation functions over compiler discovery | **Library** — REPL §16 expressly makes these conveniences optional. |
| CL34 | Library-based complete programs and transcripts | B.1–B.13; REPL §1, §3–§4, §8, §11, §17.19.2 | B explicitly assumes the reference prelude; other examples use bare operators, macros, `show`, constructors or fixed library module paths without establishing them locally | **Needs determination** — are the samples' required operations all expressible with the facilities classified above? Identify any additional compiler-only dependency; the user then confirms how stage two presents self-contained examples. |
| CL35 | Prelude contents in `/mod` turn environments | REPL §3.9; language §8.8.1–§8.8.3, §8.9.1 | Parity contract lists bare operators, `show` and `Int` as in-scope through the prelude | **Needs determination** — does turn/file environment parity require any particular prelude content, or can the listed cases be expressed solely in terms of the names actually imported? No change to the parity obligation is made here. |
| CL36 | Alternative collections and prospective channels | C.2.2, C.2.4, C.4.4; §7.12.2; §11.4a | Prospective `Hash` / collection traits, `PersistentVec`, `PersistentMap`, `Deque`, channels and runtime extern support | **Needs determination** — which library capabilities stated by these existing extensibility requirements are expressible with the present type system and primitives, and which require additional core facilities? Preserve their existing future status. |
| CL37 | Clojure-named bit helpers `bit-shift-left`, `bit-shift-right`, `bit-test`, `bit-set`, `bit-clear` | A.3 bitwise integer operations | Non-normative reference describes standard-library wrappers over bit primitives | **Needs determination** — are all the named wrappers expressible using the specified integer and bitwise facilities? The reference's library designation alone is not a normative classification. |
| CL38 | `trace-show`, `trace-call-string` | §11.5; REPL §17.19.2 (`trace-show`) | Additional library formatting helpers described only by reference guidance or search examples | **Needs determination** — are these formatting functions expressible entirely by user/library code over the specified trace ADT and string primitives? Their reference descriptions do not independently decide normative ownership. |

### Stage-two handoff

`arch` returns determinations for CL04–CL05, CL07, CL10, CL19–CL21, CL24 and
CL31–CL38.
The user confirms the resulting classification, including any reconciliation of
conflicting normative carriers. `spec` then revises the inventoried passages;
`qa` reassesses evidence for changed obligations and `test` follows the affected
spec backlinks. This is one open stage-two item, not authorization to rewrite
the chapters or implement compiler consequences now.
