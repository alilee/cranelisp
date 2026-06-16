---
number: 0378
target: /spec
filed_by: /dev
filed_at: 2026-06-16
sprint_filed: 84
refers_to: spec/03-types.md §3.11, repl/spec.md §1.5, tests/regression.rs::mono_ambiguous_unconstrained_top_level_var_rejected_neg, tests/regression.rs::mono_ambiguous_neg_does_not_reach_codegen, tests/repl_introspection.rs::display_empty_vec_value, tests/repl_introspection.rs::prelude_option_none_value_display_neg_definition_metadata
status: open
---

# §3.11 ambiguity enforcement conflicts with self-documenting-REPL display; named-defn scope unclear; test-fn-as-root not covered by mono-from-roots

## Issue

Implementing the S84 0374 structural slot gate (`slot ⟺ is_concrete()`) surfaced
three coupled questions the spec + REPL contract do not jointly resolve. The
slot gate + the `(Box a)`-HOF monomorphisation + the monomorphic-self-recursion
support all landed and are green (the Wave-0 box-SIGSEGV guards flipped). The
**0373(ii) ambiguity check is wired-but-dormant** (`find_ambiguous_top_level_form`
in `crates/cranelisp-typecheck/src/program.rs`, called but not raising) because
enabling it regresses pre-existing tests that assert spec-contradictory
behaviour.

### 1. §3.11 ambiguity rejection vs. self-documenting-REPL display (the blocker)

Spec §3.11 (`spec/03-types.md`) mandates: a REPL-input cluster whose finalised
type is `(Option a)` / `(Vec a)` with `a` unconstrained "evaluated as a complete
unit, is ambiguous" and **MUST be rejected** with a type error (no defaulting).

But two pre-existing REPL tests assert the OPPOSITE — that a bare `None` / `[]`
at the REPL **DISPLAYS** its polymorphic type per the self-documenting-REPL
principle:
- `tests/repl_introspection.rs::prelude_option_none_value_display_neg_definition_metadata`
  — bare `None` MUST display `:(…/Option a) Option.None`.
- `tests/repl_introspection.rs::display_empty_vec_value` — empty `[]` MUST
  display the `Vec` type prefix + `[]` value.

Enabling the §3.11 check (even narrowed to top-level-VALUE `__expr` forms) makes
both fail RED — they assert behaviour §3.11 now forbids. Meanwhile the Wave-0
guard `mono_ambiguous_unconstrained_top_level_var_rejected_neg` asserts the
rejection. **A bare top-level `None` cannot simultaneously be rejected
(§3.11 + Wave-0 guard) AND displayed (the two old REPL tests).**

**Question for /spec + /repl:** Does §3.11 apply to a bare top-level value at the
REPL (reject), or does the self-documenting-REPL display of a polymorphic value
take precedence there (display)? If §3.11 wins, `display_empty_vec_value` +
`prelude_option_none_value_display_neg_definition_metadata` are spec-superseded
and must be updated by /repl + /qa (and the ambiguity check enabled in one line —
remove the `let _ambiguous =` dormancy and raise the `TypeError`). If the REPL
display wins, the Wave-0 ambiguity guards are over-strict and §3.11's REPL clause
needs softening.

### 2. Named-defn ambiguity scope (`mono_ambiguous_neg_does_not_reach_codegen`)

The Wave-0 guard `mono_ambiguous_neg_does_not_reach_codegen` asserts that a NAMED
defn `(defn ambig [] None)` (type `(Fn [] (Option a))`, `a` result-only) is an
ambiguity error. But §3.11's worked example is a top-level *expression* evaluated
as a unit, not a definition. Under rank-1 HM (§3.10) a never-used polymorphic
defn is sound and *dead for codegen*, not ambiguous — `(defn ambig [] None)` is
structurally identical to a legitimate `(defn empty [] [])` library function.
The slot gate keeps such result-only-var defns `Concrete`-with-a-slot (they are
not monomorphisable from a call site — see issue 3), so they never reach codegen
ambiguously regardless.

**Question for /spec + /qa:** Is a named, never-concretely-used polymorphic defn
ambiguous (reject) or sound-but-dead (admit)? If admit, the guard's expectation
needs revising by /qa. If reject, the typecheck check must extend to named defns
with result-only free vars — which would also reject `empty`/`pure`-style
library functions, so this needs an explicit carve-out rule in §3.11.

### 3. Test functions as monomorphisation roots (cross-crate, int)

The slot gate makes a def whose type vars are reachable only from parameters
slot-less `Polymorphic` (monomorphisable from a call site). A def whose vars are
RESULT-ONLY (`test-one : (Fn [] (Option a))`) is kept `Concrete`-with-a-slot by
the S84 refinement (`fn_type_is_monomorphisable_from_params`) precisely so test
discovery (`src/session_v4.rs::discover_test_names`, which reads
`callable_got_slot()`) still finds it. This refinement was necessary to avoid
regressing `run_tests_*` / `d45_baseline_trivial`. It is a pragmatic guard, not a
principled statement: a `test-*` fn is an ENTRY POINT (like `main`), and entry
points should be monomorphisation ROOTS that force a concrete instance at their
single reachable use, the same way the program entry does. The current handling
(keep result-only-var defns `Concrete`) is correct for the SIGSEGV invariant
(their vars never reach an ADT-field RC site) but does not make them genuine
mono roots.

**Question for /arch + /int:** Should test functions (and other discovery-driven
entry points) be registered as explicit monomorphisation roots (forcing a
concrete `(Option String)` instance), rather than relying on the result-only-var
`Concrete`-retention guard? This would let the slot gate be unconditional
(`slot ⟺ is_concrete()` with no `monomorphisable-from-params` carve-out) without
stranding test fns. Out of Wave-1 (typecheck) scope; flagged for the broader
mono-from-roots completion.

> **ISSUE 3 — ARCH-RESOLVED-DESIGN (S84 Wave 1b, /arch, 2026-06-16).** YES: test
> functions become explicit monomorphisation roots; the carve-out
> (`fn_type_is_monomorphisable_from_params`, `program.rs:181`) retires and the
> slot gate is unconditional `slot ⟺ is_concrete()`. Full design at **BC §2**
> ("The slot gate is TOTAL" + the mono-root rule + the discovery-seam paragraphs),
> **`interfaces.md` §"Callability is structural"** ("gate is TOTAL — test fns are
> mono roots"), and **`sprints/SPRINT.md` §"Cluster A re-shape" → "Wave 1b"**.
> Summary: the root carries the discovery contract's expected entry type
> `(Fn [] (Option String))` and mints a concrete `Concrete{slot}` instance from
> the polymorphic original; only the degenerate `(defn test-x [] None)` shape needs
> it (a well-formed test body already pins `(Option String)` and is already
> `Concrete`). NO `cranelisp-types` change, NO `public-api.txt` move, NO cache bump
> — `UserFnState::Polymorphic` (FIXME 0377) already supplies the slot-less state.
> The seam is mechanism-only (typecheck registers the root; int's names-only
> `discover_test_names` reader resolves the concrete instance — byte-identical if
> the instance registers under the bare name). Implementation handed to the
> Wave-1b /dev relay (typecheck: delete the carve-out + register roots; int:
> point the reader at the concrete instance). **Leave this file for /sprint to
> verify-and-remove at wave close** — issues 1+2 are /spec's (in parallel; their
> portion may be uncommitted).

## Proposed resolution

1. **/spec** rules on issues 1 + 2 (REPL ambiguity-vs-display precedence; named-
   defn ambiguity scope). The cleanest reading consistent with rank-1 HM: §3.11
   applies to top-level VALUE expressions (reject a bare `None`/`[]` at the
   REPL); a named polymorphic defn is sound (admit). If so, /repl + /qa update
   the two display tests, /qa revises `mono_ambiguous_neg_does_not_reach_codegen`,
   and /dev enables the dormant `__expr` ambiguity check (one-line: raise instead
   of `let _ambiguous =`).
2. **/arch + /int** consider test-fns-as-mono-roots (issue 3) for the mono-from-
   roots completion, which would retire the `monomorphisable-from-params` carve-
   out in the slot gate.

## Operational implication / Context

The S84 0374 deliverable that LANDED (clean, zero regressions): the structural
slot gate (`UserFnState::Polymorphic` for param-var defs), the `(Box a)`-field-
through-HOF + direct-concrete-call + fn-value-argument monomorphisation, the
monomorphic-self-recursion dispatch, and the cache 5→6 bump. The two Wave-0 box-
SIGSEGV guards (`mono_tier2_generic_adt_field_through_hof_no_crash`,
`mono_tier2_all_modes_concreteness_equivalence`) flipped GREEN. The 0373(ii)
ambiguity check is implemented but dormant pending this arbitration; its two
Wave-0 guards (`mono_ambiguous_unconstrained_top_level_var_rejected_neg`,
`mono_ambiguous_neg_does_not_reach_codegen`) carry RED until issue 1/2 is ruled.
