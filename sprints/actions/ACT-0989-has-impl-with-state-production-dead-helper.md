---
id: ACT-0989
title: Disposition `has_impl_with_state`, a typecheck helper with no production caller whose deletion tracker no longer exists
status: open
priority: advisory
from: arch
to: design
sprint: 122
filed_at: 2026-09-24
refers_to:
  - crates/cranelisp-typecheck/src/checker.rs
  - design/typecheck/typed-resolution-carrier.md
---

## Request

The S114 helper-classification sweep
(`design/typecheck/typed-resolution-carrier.md` §14.4, bare-name camps row)
classified `CheckEnv::has_impl_with_state`
(`crates/cranelisp-typecheck/src/checker.rs`) as "the dead-code template —
classified for deletion by the 0590/keyed-consumer arc, tracked there". FIXME
0590 was closed as a zombie in S114 and no filing carries the deletion.

Verified at source 2026-09-24: the only callers are
`crates/cranelisp-typecheck/src/checker/tests.rs` and
`crates/cranelisp-typecheck/src/checker/test_support.rs`; the remaining
production mentions are rustdoc and comments in `checker.rs`,
`traits/dispatch.rs` and `traits/monomorphise.rs`.

`design` (typecheck) decides, in the typecheck master or the checker rustdoc:
delete the helper and re-point the unit cells at the live predicate
(`ModuleReadView::has_impl`), or retain it as test support with that status
stated. This action records the orphaned obligation; it does not pre-empt the
choice.

Filed while retiring the S114 arch carrier migration document (recoverable
from Git history at checkpoint 777ed404), whose residual-audit section routed
this item to the helper sweep.

## Completion evidence

The helper is deleted or its retained purpose is stated at source; the S114
sweep row's "tracked there" claim no longer points at a closed filing.
