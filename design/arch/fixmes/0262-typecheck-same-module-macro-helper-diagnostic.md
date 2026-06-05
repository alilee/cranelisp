---
number: 0262
target: /typecheck
filed_by: /dev (int)
filed_at: 2026-06-05
sprint_filed: 76
refers_to: crates/cranelisp-typecheck/src/checker.rs (body resolution "undefined variable" error), design/arch/macro-availability-model.md §0.8, tests/s76_macro_availability.rs::macro_clause_calls_same_module_defn_helper_rejected_neg
status: open
---

# Macro-clause body referencing a same-module non-macro def needs the §0.8 diagnostic

## Issue

The LOCKED macro-availability decision (`macro-availability-model.md` §0.8)
requires that a `defmacro` clause body referencing a **same-module non-macro
definition** at expansion time be rejected with a **clear diagnostic** that
names the offending symbol and points the author at the dependency-module rule
— e.g. *"macro expansion may not reference same-module non-macro definition
`helper`; define it in a dependency module."*

As-built, this shape IS rejected (good — the program does not compile), but the
diagnostic is the generic typecheck body-resolution error:

```
type error at 81..87: undefined variable: helper
```

(from `tests/s76_macro_availability.rs::macro_clause_calls_same_module_defn_helper_rejected_neg`,
the M3 acceptance case). The test asserts the message contains `helper` (✓) AND
one of `dependency` / `same-module` (✗) — so it fails on the message, not on the
rejection.

The "undefined variable" error originates in **typecheck's body resolution**
(int does not author it — int's `JitMacroExpander` never executes, because the
clause fails to typecheck). int has routed recognition through
`cranelisp_types::resolve_macro_head` and execution through the single
`JitMacroExpander`; the macro-availability *semantics* (a same-module non-macro
def is not resolvable from a defmacro clause body) already hold. Only the
**message** needs enriching, and the message is typecheck-owned.

## Proposed resolution

When typecheck resolves a name inside a `defmacro` clause body (it knows it is
checking a synthesised macro-clause defn — the `__macro_{name}_clause_{idx}`
shape, or a flag threaded from the clause-compile entry) and the name is absent
from the expansion-visible scope, surface the §0.8 diagnostic instead of the
bare "undefined variable": name the symbol and direct it to a dependency module.

`/design (typecheck)` decides the mechanism (a clause-body context flag on the
resolution call, or a post-hoc message rewrite when the failing resolution is
inside a macro-clause defn). int does not author typecheck error messages.

## Operational implication / Context

This is the last gap on the M3 (`macro_clause_calls_same_module_defn_helper_rejected_neg`)
acceptance case — the rejection is correct; only the message is generic.
`macro_clause_reads_same_module_def_value_rejected_neg` (the `def`/`const`
sibling) already PASSES, so the asymmetry is purely message-shape on the
`defn`-helper path. Low-risk, message-only change.
