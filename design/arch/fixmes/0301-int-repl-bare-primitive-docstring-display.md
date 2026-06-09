---
number: 0301
target: /int
filed_by: /qa
filed_at: 2026-06-09
sprint_filed: 77
refers_to: tests/repl_introspection.rs::bare_primitive_add_i64_at_prompt_displays_type_and_fqn (FAILING), repl/spec.md §1.1, sprints/SPRINT.md §"W8 / W-Repl" (RT10), tests/plan/ledger.md (RT10)
status: open
---

# REPL bare-primitive display missing `; primitive - <docstring>` (universal format §1.1)

## Issue

Typing a bare primitive name at the REPL prompt MUST produce the universal
self-documentation line `:Type name ; classification - <docstring>` per
repl/spec.md §1.1. The classification token (`; primitive`) is present, but the
` - <docstring>` tail is missing:

```
user> add-i64
:(Fn [primitives/Int primitives/Int] primitives/Int) primitives/add-i64 ; primitive
```

Expected (per §1.1 universal format, asserted by the test): the line must carry
`; primitive - <docstring>` — the classification followed by ` - ` and the
primitive's docstring. The type prefix and FQN (`primitives/add-i64`) are
correct; only the docstring tail is absent.

## Proposed resolution

When formatting a bare primitive at the prompt, append ` - <docstring>` after
the `; primitive` classification token, sourcing the docstring from the
primitive's metadata (the same docstring `/doc add-i64` would surface). Align
the bare-value display path with the universal `:Type name ; classification -
<doc>` format used elsewhere.

## Operational implication / Context

S77 W-Repl (RT10). Owner: /dev int. Single failing test
(`bare_primitive_add_i64_at_prompt_displays_type_and_fqn`) is the durable record
+ regression guard. Display-only gap, no semantics affected.
