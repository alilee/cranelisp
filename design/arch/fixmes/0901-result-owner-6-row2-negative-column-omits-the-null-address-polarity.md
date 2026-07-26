---
number: 0901
target: /design
filed_by: /dev
filed_at: 2026-07-26
sprint_filed: 118
refers_to: design/int/result-owner.md §6 (unit-test matrix, row 2 "fresh-JIT target resolution")
status: open
---

# §6 row-2's negative column omits the null-address polarity

## Issue

FIXME 0897 (resolved this wave) added a **fourth** hard-error polarity to
`fresh_jit_target`: a row whose finalized `jit_address` is `Some(0)` is now a
located hard error, matching `resolve_cached`'s existing `is_null` check. The
committed unit row is `src/result_owner.rs::tests::
fresh_jit_zero_address_is_a_hard_error`.

§6's row-2 negative column still enumerates only three: "absent key;
`jit_address: None`; symbol/key mismatch; raw address stored without its
guard". §8's I1 exit likewise says "the **three** hard-error polarities". A
reader reconciling the design against the source now counts four in the code
and three in the matrix.

The design is `/design`-owned, so `/dev` did not edit it. The source-side
statement is current (`fresh_jit_target`'s rustdoc names all four and cites
0897; the `finalize` SAFETY comment cites the now-guaranteed non-null).

## Proposed resolution

Add "null (`Some(0)`) address" to §6 row 2's negative column and re-count §8
I1's "three hard-error polarities" to four. No semantic change — the polarity
is the fresh-JIT twin of a check §3.2 already required of the cache adapter.

Optionally record the tier-3 backstop: `GlueTarget::new` carries a
`debug_assert_ne!(address, 0, …)` as a debug-tier **detector** for a future
third adapter that forgets to validate at its own boundary. It is not a gate
(no release fallback, no polarity to invert) — each adapter still owns its own
located diagnostic.

## Context

S118 W4 FIXME-resolution pass. Doc-truthfulness only; no behaviour is in
question.
