---
number: 0212
target: /design (primitives)
filed_by: /sprint
filed_at: 2026-05-17
sprint_filed: 68
refers_to: design/arch/facades/primitives.md §"Public surface" (#[used] discipline), design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md §"Consequences", crates/cranelisp-primitives/src/{ring0,bool,int,float,marshal,string,vec}.rs
status: open
---

# `#[used]` discipline contract gap on demoted primitive extern fns

## Issue

Sprint 68 Wave 4 demoted ~45 `pub extern "C" fn` items in `cranelisp-primitives` to `pub(crate) extern "C" fn`. The facade (`primitives.md` §"Public surface") and Decision 0048 §"Consequences" explicitly prescribe `#[used]` attributes on these items to prevent DCE in `--link` mode staticlib production.

**Wave 4 added `#[unsafe(export_name = "...")]` but did NOT add `#[used]`** on the 45 fns. Wave 6 `/review (primitives)` flagged this as an Important contract gap.

In practice, the `extern_shims()` static-init function in `cranelisp-primitives/src/lib.rs` references every fn ptr via `m.insert("str-eq", string::str_eq as *const u8)` etc. — this static-data reference keeps the fns alive against DCE. So the linker behaviour is correct; the contract is what's drifted.

## Proposed resolution

Two options:

1. **Fix the source** — `/dev (primitives)` adds `#[used]` to each of the 45 `pub(crate) extern "C" fn` items. ~45 single-line additions. Belt-and-suspenders with `extern_shims()`. Faithful to current facade.

2. **Amend the facade** — `/design (primitives)` revises `facades/primitives.md` to drop the `#[used]` mention and explicitly name `extern_shims()`'s static-init reference as the canonical DCE-prevention mechanism. Decision 0048 §"Consequences" gets a parallel amendment.

Either resolution is acceptable. Option 2 is mechanically simpler and aligns the contract with the actual mechanism. Option 1 adds explicit belt-and-suspenders that future readers may find clearer.

## Operational implication / Context

Not blocking — `extern_shims()` provides the DCE protection in practice. Wave 6 /review verified all 10 S68 tests pass and `--link` mode works end-to-end. The gap is documentation/source contract clarity, not runtime correctness.
