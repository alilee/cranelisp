---
number: 0897
target: /dev
filed_by: /review
filed_at: 2026-07-26
sprint_filed: 118
refers_to: src/result_owner.rs::fresh_jit_target (:530-537) + OwnedProgramResult::finalize (:241-244)
status: open
---

# Fresh-JIT glue address is not validated non-null before the transmute

## Severity

Blocker

## Issue

`OwnedProgramResult::finalize` transmutes `target.address` to
`extern "C" fn(i64)` and calls it — the change-set's one unsafe block. The
unsafe-audit rule for JIT function-pointer casts (`.claude/commands/review.md`
§Unsafe code audit) requires validating that the pointer is **non-null**, and
those rules are absolute (no exception severity).

The cache-hit adapter honours this: `resolve_cached` rejects a null resolution
(`src/result_owner.rs:556`). The fresh-JIT adapter does not: `fresh_jit_target`
distinguishes only `None` from `Some(address)` (`:530-535`) and passes any
`Some(0)` straight into `GlueTarget::new`, which also admits zero. The
`// SAFETY:` comment asserts finalized provenance via backend's projection, but
nothing at the safe construction boundary makes that structural (Principle 18 —
enforce invariants structurally). A zero `jit_address` row — however it arose —
would be called.

Found by the delegated Codex reviewer (codex-cli 0.145.0); verified at source
by the adjudicator.

## Proposed resolution

Reject `address == 0` in `fresh_jit_target` with the same hard-integration-
error shape as the existing three polarities (mirroring `resolve_cached`'s
null check), so the validation lives at the safe boundary that feeds the sole
unsafe block. A unit row for the zero-address polarity joins the §6 row-2 set
(`design/int/result-owner.md`). Alternatively (or additionally) make
`GlueTarget::new` itself refuse zero — one chokepoint covering both adapters.

## Context

S118 W4 change-set (`fc3375f9..3ffab566`), review gate. The fix is small and
mechanical; the Blocker classification follows from the unsafe-audit rules
being absolute, not from an observed defect — backend currently projects only
finalized non-null addresses.
