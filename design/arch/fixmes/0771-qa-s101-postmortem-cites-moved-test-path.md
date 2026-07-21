---
number: 0771
target: /qa
filed_by: /dev
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/plan/s101-coverage-postmortem.md §2.1 (cites
  `program::tests::callees_*`) — the path moved in the S115 W4 FIXME-0722 split
status: open
---

# `tests/plan/s101-coverage-postmortem.md` §2.1 cites a test path the 0722 split moved

## Issue

The FIXME-0722 `program/tests.rs` split (S115 W4) rehomed every pooled test to a
sibling of the production submodule it exercises. Two external documents cited
the old `program::tests::` paths; `crates/cranelisp-typecheck/CLAUDE.md` is
`/dev`-owned and was updated in the same change-set, but
`tests/plan/s101-coverage-postmortem.md` §2.1 is `/qa`'s.

New paths:

| Old | New |
|---|---|
| `program::tests::callees_*` | `program::callees::tests::callees_*` |
| `program::tests::cross_module_imported_constrained_fn_monomorphises_in_defining_scope` | `program::mono_collect::tests::cross_module_imported_constrained_fn_monomorphises_in_defining_scope` |

The full home table is in `crates/cranelisp-typecheck/CLAUDE.md` §Testing.

## Proposed resolution

`/qa` updates the §2.1 citation. No behaviour change — the 18 `callees_*` cells
are byte-identical and all 213 pooled tests were preserved exactly through the
split (798 → 798 crate tests across the move).

## Context

The design (`design/typecheck/program-decomposition.md` §3) offered a
`#[cfg(test)] pub(crate) use` alias to avoid this cross-skill churn; an alias was
NOT taken, because it would re-create the very indirection the split removes (a
name that resolves to a file other than the one it names). A one-line citation
update is the cheaper honest fix.
