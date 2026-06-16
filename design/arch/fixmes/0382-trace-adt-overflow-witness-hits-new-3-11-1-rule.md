---
number: 0382
target: /qa
filed_by: /dev
filed_at: 2026-06-16
sprint_filed: 84
refers_to: tests/trace.rs::trace_adt_value_render_overflows_defect, spec/03-types.md §3.11.1, design/typecheck/monomorphisation.md §4
status: open
---

# `trace_adt_value_render_overflows_defect` now correctly hits the position-complete §3.11.1 rule — pin `mk`'s result type

## Issue

The S84 Wave 2 belt-and-braces change landed the POSITION-COMPLETE §3.11.1
ambiguity check (`cranelisp-typecheck::program::find_ambiguous_value_position`),
which rejects a genuinely-unpinned `Mixed`-shaped ADT-with-free-var value reaching
a codegen value position THROUGH a polymorphic boundary. The e2e test
`tests/trace.rs::trace_adt_value_render_overflows_defect` now fails at typecheck:

```clojure
(import [primitives [Trace TraceCall]])
(deftype (Option a) None (Some [:a val]))
(defn mk [] None)                                  ; mk : (Fn [] (Option a)), a free
(match (trace (mk)) [(TraceCall n p r c ns) r])    ; (mk) : (Option a), a UNPINNED
```

→ `error: type error at 14..18: ambiguous type; add an annotation to pin the type
of the polymorphic value bound in `__expr``.

This is the **correct** §3.11.1 verdict, NOT an over-fire: `(mk)` returns an
unpinned `(Option a)` (the `match` scrutinises only the `TraceCall` tag of the
trace wrapper, and nothing pins `Option`'s `a`). It is structurally identical to
the QA acceptance guard `regression::mono_ambiguous_match_scrutinee_rejected_neg`
(`(match (identity None) …)` — a `Mixed`-ADT-with-free-var value through a fn,
which the same rule rejects). The difference from the admitted `(is-some None)`
idiom (a DIRECT `None` constructor reference, whose representation is pinned by the
syntactic constructor — the check skips those via
`expr_is_direct_constructor_value`) is that `(mk)` flows the value THROUGH the
`mk` fn boundary, so its actual constructor is not statically the syntactic value.

## Proposed resolution

Update the test to pin `mk`'s result type so the value is no longer ambiguous —
e.g. annotate `mk`'s return (`(defn mk [] :(Option Int) None)`) or the `__expr`,
matching how a real program would resolve the ambiguity. The test's intent (a
trace-ADT-render overflow witness) is preserved with a concrete `Option`
instantiation. The assertion (`:primitives/String` rendered) is unaffected by the
annotation.

Alternatively, if the trace-render overflow witness needs a polymorphic value
specifically, restructure so the `Option`'s element type is pinned by a use (e.g.
`(get-or-default (mk) 0)`), keeping the value concrete at codegen.

## Operational implication / Context

- This is the ONLY net e2e regression from the S84 Wave 2 §3.11.1
  position-completion (`every_example_runs_with_documented_exit`'s
  `11-destructuring.cl` `(is-some None)` is admitted — direct-constructor skip;
  `repl_cross_cluster_duplicate_field_accessor_is_ambiguous` is a PRE-EXISTING red
  unrelated to this change, confirmed by stash-baseline).
- The 4 §3.11.1 acceptance guards
  (`mono_ambiguous_{match_scrutinee,call_arg,ctor_field,if_branch}_rejected_neg`)
  flipped GREEN; `mono_vec_free_var_value_admitted_pos` + the `let`-position guard
  + the 0344 fold canary stay GREEN.
- Until this test is updated it is a known red attributable to the now-correct
  §3.11.1 rule — a behaviour-tightening, not a defect.
