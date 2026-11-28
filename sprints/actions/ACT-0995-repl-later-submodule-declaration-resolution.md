---
id: ACT-0995
title: Refuse a later REPL child-module declaration that makes an earlier import ambiguous
status: open
priority: required
from: sprint
to: design
sprint: 126
filed_at: 2026-09-27
refers_to:
  - spec/08-modules.md
  - spec/appendix-d-open-questions.md
  - tests/plan/s125-evidence-delta.md
  - design/int/int.md
  - src/process_form/form_dispatch.rs
---

## Request

Implement the user's S125-Q10 ruling (2026-11-27): "(mod q) after (import [q])
should be an error ambiguous import." The requirement is
[§8.11.2.1](../../spec/08-modules.md#81121-bare-name-precedence-current-module-relative-submodule-wins),
"Later REPL declaration after an import".

Example: root `q` defines `(defn g [] 99)` and child `user.q` defines
`(defn g [] 11)`. In module `user`, `(import [q [g]])`, `(defn h [] (g))`, then
`(mod q)`: the `(mod q)` turn is refused as an ambiguous import, and `(g)` and
`(h)` keep answering from root `q`.

Route: `design` on `src/` (replacing `design/int/int.md`'s REPL-turn-order
residual), then `qa` settles the cell
([S125 delta §26.2](../../tests/plan/s125-evidence-delta.md)), `test` writes it,
`dev` on `src/` implements.

The refusal changes neither the session nor the backing source and retains no
proposed child declaration; no form addresses a root `q` that a child captures
(S125-Q10-R1, "1 agreed", same section). Verified 2026-11-27:
`record_submodule_on_symbol_table` in `src/process_form/form_dispatch.rs`
appends to the live table directly, so the refusal must precede or undo that
append.

## Completion evidence

The §26.2 cell GREEN for both import forms, with prior calls unchanged, no
retained child declaration and the backing source unchanged; its control
(`(mod q)` with no earlier import is accepted); a unit test at the refusal
seam; the §8.11.2.1 band updated by `qa`.
