---
number: 0513
target: /typecheck
filed_by: /dev
filed_at: 2026-07-04
sprint_filed: 102
refers_to: crates/cranelisp-typecheck/src/checker.rs §"lookup" (the qualified-name arm, ~lines 1188-1226), spec/08-modules.md §8.6.4
status: open
---

# Qualified-name resolution surfaces the phantom `<current>.<qualifier>` child gap even when the absolute module is loaded but the member is missing

## Issue

`Checker::lookup` (`crates/cranelisp-typecheck/src/checker.rs`, the
`name.find('/')` arm) resolves a qualified reference `mod/sym` by probing TWO
candidates:

1. **child-of-current-module** — `child_path = format!("{}.{}", current_module,
   module_part)` (e.g. `user.primitives` for a reference `primitives/nosuchfn`
   made from module `user`), then `resolve_qualified(child_path, sym)`;
2. **absolute** — `resolve_qualified(module_part, sym)`.

When the absolute module IS loaded but the MEMBER is absent,
`resolve_qualified` returns `Ok((None, None))` — a genuine not-found with **no
gap** (checker.rs:1765-1769, the `TypeNotFound`/`SymbolNotFound` arms). The
child probe, however, hit an UNLOADED module `user.primitives` and produced a
`ResolutionGap::SymbolTypechecked(user.primitives/nosuchfn)`. The gap-selection
tail (`match abs { Ok((_, Some(g))) => Some(g), _ => match child { … } }`)
therefore surfaces the **phantom child gap**.

Downstream (int's `finalize_cluster` → `drive_module_dep`) then hunts a
non-existent `user.primitives` submodule and — before this sprint's int-side
mitigation — reported
`module 'user.primitives' referenced by 'user.primitives/...' not found` at
`0..0`: a phantom module, a `'...'` placeholder, and a bogus span.

## Interim mitigation already landed (int-side, S102 Wave 10a)

`src/process_form.rs::phantom_member_diagnostic` intercepts this exact gap shape
at the int seam and reports the honest
`module 'primitives' has no member 'nosuchfn'` with the real reference span
(FIXME 0490 resolved; guard
`tests/display_exact.rs::qualified_ref_missing_member_diagnostic_names_real_module`).
It fires only when the gap module is a single-component child
`<current>.<qualifier>` and `<qualifier>` names a REAL loaded module.

## Proposed resolution

Make `lookup`'s qualified arm prefer the **absolute-module reality** over the
phantom child probe: when the absolute-path candidate resolves the module but
not the member (a loaded module, member-absent — no gap), that is a definitive
member-not-found and MUST NOT be masked by the child probe's gap. Either
(a) surface a member-not-found `TypeError` naming the real module + member at
the var's span (which `infer_var` has in hand) directly from `lookup`, or
(b) suppress the child gap when the absolute module is loaded, so no misleading
gap escapes typecheck. Once typecheck no longer synthesises the phantom child
gap for this shape, the int-side `phantom_member_diagnostic` mitigation becomes
redundant and can be removed (it is deliberately narrow and side-effect-free, so
it can also stay as a belt-and-suspenders guard until this lands).

## Operational implication / Context

The order-independence and messaging of qualified member-miss diagnostics is a
typecheck-resolution concern (spec/08-modules.md §8.6.4 adjacency). The int
mitigation cures the user-facing message but leaves the root mis-ordering in
`checker::lookup`; a future qualified-name path that does not flow through
`finalize_cluster`'s gap seam would re-expose it.
