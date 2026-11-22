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
[Appendix C §C.2.4](appendix-c-nfr.md#c24-collection-extensibility)
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

**Closed remainder — S124-Q12-R1, user ruling, 2026-11-22.** Put to
the user: `macros/sconcat` is a public primitive at the type it has today,
`(Fn [(SList Sexp) (SList Sexp)] (SList Sexp))`; §9.7.3 replaces its general
signature with that type, and a library may offer a general concatenation
under its own name. Answer, verbatim:

> agreed retain as public primitive

[§9.7.3](09-macros.md#973-sconcat) records the public primitive and type.
The coordinator withdrew the SHOULD/MUST question about §8.8.3; the user's
own wording there stands.

## S124-Q13: What are a trace root's name, parameters and children?

**Closed — user ruling, 2026-11-22.** Put to the user: a trace always
has a synthetic root, named `::trace::`, with no parameters and every recorded
call beneath it; the examples in §4.12.7 and §4.12.8 change. The follow-up was
“A confirmed, and `::trace::` as the root's name?” Answer, verbatim:

> 2 A

[§4.12.2](04-expressions.md#4122-semantics) and
[§4.12.4](04-expressions.md#4124-the-trace-adt) record the root and field
meaning; §4.12.7–§4.12.8 show that shape.

## S124-Q14: Can a project file be a child of a library-resolved parent?

**Closed — user ruling, 2026-11-21**, recorded as “User ruling on
S124-Q14” in [Sprint 124 Notes](../sprints/SPRINT.md#notes). The user's
answer, verbatim:

> A - m/t.cl is not indexed, because it cannot be addressed from an FQ name.

The option put as A was: when `m` resolves to `lib/m.cl`, a project file
`{project_root}/m/t.cl` is not part of the program — it is not loaded, and
its presence alone is not an error.
[§8.11.2](08-modules.md#8112-module-resolution-search-order) records that
rule. [§8.2.5](08-modules.md#825-file-resolution)'s declared-child path
rule is unchanged. No normative remainder is identified.

## S124-Q15: When is an undefined name in a default method reported?

**Closed — user ruling, 2026-11-22.** Put as A: an undefined name in
a default method body is reported when an `impl` inherits the default, not
at the `deftrait`. Answer, verbatim:

> 1 A

[§7.1.5](07-traits.md#715-default-method-implementations) records the
reporting point; an overriding impl does not instantiate the default.

## S124-Q16: Core/library classification and stage-two specification revision

**Closed — classification confirmed and stage-two prose revised, 2026-11-22.**
The rule is stated normatively in [§8.8.3](08-modules.md#883-empty-prelude).
The user confirmed the classification and authorized the inventoried rewrite
in [Sprint 124 Notes](../sprints/SPRINT.md#notes), “S124-Q16 classification
confirmed”: “confirm the spec rewrite”. Technical determinations came from
`arch`'s core/library boundary assessment; the specific user rulings below
override its earlier undecided points. This closes the specification revision,
not compiler migrations, evidence allocation or future capability delivery.

### Inventory

This is a non-normative inventory of `spec/`, `repl/spec.md` and `repl/spec/`
originating at the S124 stage-one checkpoint, with the confirmed classification below. Rows group related spellings with the same
dependency and decision; the section column identifies definitions and dependent
passages, including examples. The section and dependency columns preserve the stage-one
problem inventory; the classification column records its confirmed disposition.
References to module search paths or to introspection of whatever names happen
to be imported are not, by themselves, dependencies on particular library content.

**Library** means expressible by user/library code; its descriptions and
library-specific example results are non-normative. **Language** means
compiler provision independent of libraries. Section numbers refer to language
chapters unless prefixed REPL, A, B or C; see the [chapter map](index.md).
Examples use the [explicit scope convention](index.md#example-scope) and
[REPL environment convention](../repl/spec/index.md#example-environments).

| ID | Construct | Sections carrying or relying on it | Stage-one dependency | Confirmed classification |
|---|---|---|---|---|
| CL01 | `const`, `const-` | §2.2, §2.6; §5.1 binder rules, §5.6, §5.14; §9.2.2, §9.5, §9.10.1; REPL §11 | Prelude macro; `quote-sexp`; zero-argument `defmacro`; bare operators in examples | **Library** — optional macro, illustrated non-normatively in §5.6 and §9.10.1. |
| CL02 | `def`, `def-` | §2.2, §2.6; §5.1 binder rules, §5.7, §5.14; §9.2.2, §9.6, §9.10.2, §9.12; REPL §11 | Prelude macro; `make-def-name`, `quote-sexp`, Sexp constructors, `begin`, generated function/macro pair | **Library** — optional macro, illustrated non-normatively in §5.7 and §9.10.2. |
| CL03 | `derive`, `derive-Eq`, `derive-Ord`, `derive-Display` | §7.13.1–§7.13.5 | Prelude macro and per-trait helper macros; `Eq`, `Ord`, `Display` and their methods | **Library** — optional macro and helper macros; §7.13 is a non-normative illustration. |
| CL04 | `Num`, `Eq`, `Ord`, `Display`; arithmetic/comparison operators and `show` | §3.6–§3.7 examples; §7.1, §7.3, §7.6–§7.8, §7.13; §9.10; §12.9; B; REPL §1.1, §4.1, §17.19.2 | Library trait declarations and primitive-type impls according to §7.7, but the same subsection also calls them compiler-seeded infrastructure; bare operators and `show` throughout examples | **Library** — ordinary traits, implementations and methods; canonical compiler rendering is independent of `Display`. |
| CL05 | `Functor`, `fmap` | §3.7; §7.2, §7.7.5, §7.8; B introduction | User/library higher-kinded trait and collection implementations | **Library** — single-parameter HKT declaration and ADT implementations, including a thunk-based `Seq`. |
| CL06 | `pure` | §3.2.3; §10.1–§10.2, §10.3 examples, §10.5–§10.8; §12.4; B.12–B.13 | Public interface to opaque built-in IO; no language constructor | **Language** — user ruling, 2026-11-22: `primitives/pure` is the public function; the constructor is private. |
| CL07 | `bind` | §3.2.3; §9.10.5; §10.3–§10.5, §10.8, §10.12; §12.4; B introduction | Primitive IO composition in §10.3; the opaque-IO ruling removes §3.2.3's former library-definition claim | **Language** — `primitives/bind`; opaque IO composition cannot be implemented as a user ADT or by running a platform effect in user code. |
| CL08 | `do` | §5.1.1; §9.10.4; §10.4, §10.5.3; §12.4–§12.5; B | Prelude macro and `do-build`; §9.10.4 shows nested `let`, §10.4 shows nested `bind` | **Library** — §10.4 and §9.10.4 illustrate IO sequencing over `primitives/bind`; nested `let` is pure-expression sequencing. |
| CL09 | `bind!` sugar | §9.10.5; §10.5, §10.12; §12.4; B.4, B.13 | Prelude macro, `bind!-fold`, `bind` and `fn`; §10.12 additionally requires compiler analysis of its chains | **Library** — §10.5 explicitly says library macro, not language requirement. Core scheduling is independently specified under CL10. |
| CL10 | Automatic scheduling, resource ordering and launch rules expressed over `bind!` / `do` chains | §10.12.1–§10.12.10; §12.4.1, §12.4.3–§12.4.4, §12.5; C.3.2 | Language obligations name library sugar as the analysis/sequencing surface | **Language over core composition** — analyze expanded `primitives/bind` chains; no sugar recognition is required. |
| CL11 | `cond` | §9.10.8; B introduction | Prelude macro, `cond-fold`; nested `if` expansion | **Library** — the user's explicit example in the 2026-11-21 ruling. |
| CL12 | `case` | §9.10.9 | Prelude macro, `case-fold`, Sexp constructors; library equality `=` | **Library** — §9.10 identifies it as a prelude macro. |
| CL13 | `when`, `unless` | §9.10.12; B.6 | Prelude macros; `if` and `Option` constructors `Some` / `None` | **Library** — §9.10 identifies them as prelude macros. |
| CL14 | `->`, `->>` | §9.2.2, §9.10.6–§9.10.7; B.8 | Prelude macros; `thread-first-fold`, `thread-last-fold`; library functions in sample pipelines | **Library** — §9.10 identifies them as prelude macros. |
| CL15 | `list` | §9.10.3, §9.10.7; B introduction; REPL §3.7 | Prelude macro; `sfold`, `sreverse`; library `List`, `Cons`, `Nil` | **Library** — §9.10 identifies it as a prelude macro. |
| CL16 | `vec` macro (distinct from bracket literal) | §2.3.9; §9.10.10; B introduction | Prelude macro producing `SexpBracket` | **Library** — §2.3.9 explicitly excludes `vec` from core syntax and reserved names. |
| CL17 | `str` | §9.10.11; B introduction | Prelude macro, `str-fold`; `show` and `str-concat` | **Library** — §9.10 identifies it as a prelude macro. |
| CL18 | `sfold`, `sreverse`, `sempty?` | §9.7.0–§9.7.4, §9.10.3 | Optional `core.syntax` helper functions or local equivalents | **Library** — §9.7 explicitly designates optional library helpers. |
| CL19 | User-callable `macros/sconcat` | §9.7.3; Q12-R1 | Public primitive at `(Fn [(SList Sexp) (SList Sexp)] (SList Sexp))` | **Language** — Q12-R1 user ruling, 2026-11-22. A library may supply general concatenation under its own name. |
| CL20 | `slist` | §9.7.5, §9.10.3; B.6 | Convenience macro over compiler-seeded `SCons` / `SNil`; absent from §9.7.0's named helper list | **Library** — variadic macros can emit qualified `macros/SCons` / `macros/SNil`. |
| CL21 | Named macro-building helpers | §9.2.2, §9.10.2–§9.10.11 | `make-def-name`, `do-build`, `bind!-fold`, `thread-first-fold`, `thread-last-fold`, `cond-fold`, `case-fold`, `str-fold` are used but not defined there | **Library** — Sexp transformations in dependency modules or recursive macro clauses; no missing primitive. |
| CL22 | `List`, `Cons`, `Nil` | §3.2.2, §3.7 examples; §5–§7 examples; §9.10.3; §12.4.4, §12.9.3; B; REPL §1.5, §3.7, §9 | User-visible list ADT, prelude constructors and display examples | **Library** — §9.1.1 distinguishes the user/library `List` from compiler `SList`; §9.10.3 describes its library macro. |
| CL23 | `Seq`, `SeqCons`, `SeqNil` and lazy-tail behavior | §4.11; §7.7.5; §12.4.2; B introduction; REPL §1.5, §9 | Library thunk-based lazy sequence ADT, also named by runtime and display requirements | **Library** — §4.11 explicitly calls `Seq` a library-level construct. |
| CL24 | Collection/pipeline helpers `map`, `filter`, `reduce`, `inc`, `vec-map`, `vec-reduce`, `map-list`, `seq-map`, `filter-list`, `vec-filter`, `fold-list`, `count`, `get`, `conj`, `assoc`, `first`, `rest`, `second`, `head`, `to-list`, `take`, `lazy-take`, `lazy-drop`, `range-from`, `iterate`, `repeat` | B.5, B.8–B.9; §7.7.5, §7.12.2; §9.10.6–§9.10.7; §11.4a; A.3 | Library functions/trait methods, concrete-family wrappers and prospective naming reservations | **Library** — concrete-family helpers and single-parameter collection traits; general keyed-family `get` / `assoc` requiring a second trait parameter remain future. |
| CL25 | `Option`, `Some`, `None` | §3.2.2 examples; §7.13; §9.10.12; §10.12.8; §12.4.4, §12.7.3, §12.7.6; A.3; B; REPL §16 | Prelude/user ADT in examples, but checked primitives, timeout and test protocols require it; REPL §16.3 calls it a primitives bootstrap type | **Language** — REPL §16.3 explicitly retains primitive bootstrap `Option`. §3.2.2 distinguishes primitive provisioning from local example declarations. |
| CL26 | `Result`, `Ok`, `Err`; `Pair`, `first`, `second` | §3.2.5–§3.2.6; §12.7.7; A.2–A.3; B.3; REPL §16 | Compiler-seeded ADTs versus user definitions and bare field/constructor examples | **Language** — §3.2.5–§3.2.6 explicitly seed them in `primitives`; user examples must not be mistaken for required library definitions. |
| CL27 | Bare primitive names, including scalar types, `parse-int`, `str-concat`, Vec and arithmetic primitives | §2–§10 examples; §9.11.2; §12 examples; A; B; REPL examples | Prelude re-exports or explicit imports are needed for bare names, although qualified primitive paths are independent | **Language** — §3.1 and §8.9.1 explicitly provide qualified access without imports. This row records scope assumptions, not a new required primitive catalog. |
| CL28 | Quasiquote / unquote-splicing and concatenation | §9.4, §9.7.0; §11.4; Q12 | Compiler-seeded `macros` constructors and compiler-provided concatenation; prior library-helper dependency removed by Q12 | **Language** — Q12 and §9.7.0 explicitly require library-independent splicing. CL19 records the separately ruled public helper. |
| CL29 | `quote-sexp`, Sexp / SList constructors | §8.9.2; §9.1, §9.5, §9.11.1; B.6 | Compiler provision, but bare constructor and helper names in samples require imports; qualified expansion references are already specified | **Language** — §8.9.2 and §9.1 explicitly provide compiler-seeded macro data; §9.11.1 identifies the primitive. |
| CL30 | `trace-show-tree` | §4.12.8; §11.5 | `core.trace` display helpers over the compiler-seeded `Trace` ADT | **Library** — §4.12.8 explicitly identifies this as a stdlib display function; §11.5 describes it. The trace form itself is language-provided. |
| CL31 | `timeout` | §10.12.8–§10.12.10; §12.4.4; C.3.2 | A documented stdlib derivation from `race`, `sleep` and `Option`, while §12.4.4 calls it part of the language IO model | **Library** — select between an effect mapped to `primitives/Some` and a timer mapped to `primitives/None`, using core IO operations. |
| CL32 | `race`, `select`, `sleep` | §10.12.8–§10.12.10; §12.4.4; C.3.2 | IO first-completion composition and timer support | **Library** for `race`, `(primitives/select [a b])`, by the user ruling of 2026-11-22; removal of today's built-in is carried. **Language** for `primitives/select` and `primitives/sleep`. |
| CL33 | `discover-here`, `format-test-run`, `failures-only`, `test-passed?` | A.3; REPL §16.3, §16.5 | Optional testing library sugar and presentation functions over compiler discovery | **Library** — REPL §16 expressly makes these conveniences optional. |
| CL34 | Library-based complete programs and transcripts | B.1–B.13; REPL §1, §3–§4, §8, §11, §17.19.2 | B explicitly assumes the reference prelude; other examples use bare operators, macros, `show`, constructors or fixed library module paths without establishing them locally | **Library illustrations** — no additional compiler-only dependency identified; reference-library programs are explicitly non-normative and import their environment. Runtime verification belongs to `qa` / `test`. |
| CL35 | Prelude contents in `/mod` turn environments | REPL §3.9; language §8.8.1–§8.8.3, §8.9.1 | Parity contract lists bare operators, `show` and `Int` as in-scope through the prelude | **Content-independent parity** — turns use the file's actual imports, including whatever an unsuppressed prelude supplies; no required prelude names. |
| CL36 | Alternative collections and prospective channels | C.2.2, C.2.4, C.4.4; §7.12.2; §11.4a | Prospective `Hash` / collection traits, `PersistentVec`, `PersistentMap`, `Deque`, channels and runtime extern support | **Mixed, with future status retained** — ADT collections and a `Hash` declaration are library-expressible; String/Float hashing needs additional primitives, channels need runtime/platform effects, and extern-backed types need their extern support. No new present facility is required. |
| CL37 | Clojure-named bit helpers `bit-shift-left`, `bit-shift-right`, `bit-test`, `bit-set`, `bit-clear` | A.3 bitwise integer operations | Non-normative reference describes standard-library wrappers over bit primitives | **Library** — wrappers over integer and bitwise primitives. |
| CL38 | `trace-show`, `trace-call-string` | §11.5; REPL §17.19.2 (`trace-show`) | Additional library formatting helpers described only by reference guidance or search examples | **Library** — formatting over `Trace` and string primitives. |

### Stage-two disposition and handoff

The confirmed rewrite separates optional library descriptions (§5.6–§5.7,
§7.7, §7.13, §9.7's library helpers, §9.10, §10.4–§10.5 and Appendix B)
from language obligations. Scheduling and cancellation are stated over core IO
composition (§10.12, §12.4–§12.5, C.3.2); REPL parity depends on actual imports
(REPL §3.9). Primitive and macro-data examples have explicit scope conventions;
local ADTs are distinguished from seeded ADTs. No normative question remains
from this inventory. C.2/C.4's future capability obligations are retained,
without asserting that absent hashing or channel facilities exist today.

`qa` must reassess the changed claims and invalidated coverage tags, including
claims moved to non-normative examples. `test` then follows affected backlinks;
this pass runs no programs and asserts no new coverage. Compiler consequences
and migrations remain with their owners through `sprint`; closure here neither
accepts a defect nor authorizes a further delivery phase.

### Closed rulings of 2026-11-22 affecting the inventory

The authority for these rulings and Q12-R1, Q13, Q15, Q17 and Q18 is
[Sprint 124 Notes](../sprints/SPRINT.md#notes), from “User ruling on `race`”
through “S124-Q16 classification confirmed”. The latter confirms the resulting
classification and authorizes the stage-two rewrite.

**`race`.** Put to the user: classify `race` as library now, since it is
`(select [a b])`, and carry removal of the built-in as filed work outside
S124. Answer, verbatim:

> agreed carry

CL32 and [§10.12.8](10-io.md#10128-structured-control-combinators--race--select--timeout)
record the library classification; today's built-in provision and its carried
removal remain distinguished in CL32.

**Opaque `IO`.** Put as A: IO is an opaque built-in type; the language has
`(IO a)` and no constructors for it. Values are made by `pure`, `bind`,
`select`, `sleep` and platform operations and consumed only by the runtime;
user code cannot match on IO. Node kinds, layout and the disposer are
implementation detail and leave the specification. B was a sum type with
private constructors. Answer, verbatim:

> A

On the spelling of `pure`, the user's words were:

> the constructor is conceptually a module private thing. the public interface
> is the `pure` function

[§10.1](10-io.md#101-io-type) owns opacity and the public operations;
[§10.2](10-io.md#102-pure) owns `primitives/pure`. CL06 reflects the ruling.
Constructor definitions and runtime node details are removed from their
other specification carriers; this does not implement the compiler migration.

**Display markers.** Put to the user: an IO value nested inside a displayed
value shows as `#io`; `<closure>` becomes `#closure`. Both markers are
display-only and rejected by the reader. Answer, verbatim:

> #io and #closure confirmed.

[§12.9.1](12-runtime.md#1291-format-by-type) owns the canonical markers;
[REPL §1.2 and §1.5](../repl/spec/01-display-format.md#12-expression-results)
apply them to expression results and recursive display.


## S124-Q17: What result does a skipped trace form record?

**Closed — user ruling, 2026-11-22.** Put to the user: use
`::untraced::` as the name, and choose result A (the body's displayed value,
as for any root) or B (an empty result string). Answer, verbatim:

> 3 A

The user had asked, verbatim:

> is it `::untraced::`?

The coordinator reads “3 A” as adopting that name; this is recorded as the
coordinator's reading, stated back to the user, rather than an additional
verbatim naming answer. The name has one normative definition in
[§4.12.6](04-expressions.md#4126-concurrency), alongside the unrecorded
root's result rule.

## S124-Q18: May a trace form be entered inside a skipped form on the same thread?

**Closed — user ruling, 2026-11-22.** Put as A: a trace form entered
inside a skipped form on the same thread raises no error and is itself
skipped. Answer, verbatim:

> 4 A

[§4.12.5](04-expressions.md#4125-nested-trace) records that exception to
the same-thread active-tracing error; [§4.12.6](04-expressions.md#4126-concurrency)
owns the unrecorded root's shape and result.

## S124-Q19: May a pure function return an IO value?

**Open — put to the user on 2026-11-22; no answer recorded.**

**Problem.** [§3.2.3](03-types.md#323-io-type) states “Pure functions MUST NOT
return `IO`.” [§10.2](10-io.md#102-pure) specifies `primitives/pure` as a
function returning `(IO a)` without performing a side effect, and
[§10.3.1](10-io.md#1031-semantics) says calling `bind` performs no effect.
The return-type prohibition and effect-free construction therefore need a
consistent account of purity. The requirement in §3.2.3 remains unchanged
pending the user's ruling.

**Options and tradeoffs.**

- **A — the wording put to the user:** replace “Pure functions MUST NOT return
  `IO`” with “Pure functions MUST NOT perform effects”. This distinguishes
  constructing an IO value from executing its effects and permits the
  effect-free construction described in §10.2 and §10.3.1. Related purity and
  effect-tracking prose would need checking against that distinction.
- **B — retain the return-type prohibition:** reserve “pure function” for
  functions returning non-IO values, and describe effect-free IO construction
  separately. This preserves §3.2.3 but requires consistent terminology for
  functions that construct IO values without performing effects.

The user decides which meaning and wording govern; neither option is a ruling.
