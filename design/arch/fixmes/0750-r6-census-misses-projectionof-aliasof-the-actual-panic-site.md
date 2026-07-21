---
number: 0750
target: /dev
filed_by: /review (cranelisp-backend, S115 W3)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-backend/src/cache/serialize.rs (R6 census rustdoc + deserialise_meta_with_build_id); crates/cranelisp-typecheck/src/ownership/transfer.rs:690-750; design/arch/safety-invariants.md §4 R6
status: open
---

# R6 row 3 validates the ONE `ResultMode` index variant that is already safe, and misses the two that are not — including the actual panic site

## Severity
Important — the R6 deliverable's own maintenance rule ("no persisted index may
escape a row") is violated inside the change-set that states it, and the escaping
index is the one that panics on disk content.

## Issue

The landed arm is:

```rust
if let Some(summary) = entry.mode_summary()
    && let cranelisp_types::ResultMode::MayAliasOf(k) = summary.result
```

`ResultMode` has THREE index-carrying variants — `ProjectionOf(usize)`,
`AliasOf(usize)`, `MayAliasOf(usize)` — all persisted through the same
`ModeSummary.result` field, all read positionally against the same arg vector.
The census row and the arm cover only `MayAliasOf`.

**The polarity is exactly inverted from the stated hazard.** The census row
justifies itself as *"`k ≥ arity` → `arg_origins[k]` OOB read at the consume
seam"*. At the consume seam (`ownership/transfer.rs`):

- `MayAliasOf(k)` → `arg_origins.get(k).cloned().unwrap_or(Origin::Fresh)` — a
  CHECKED read; no OOB is possible. The validated variant needs no validation.
- `AliasOf(k)` → `arg_origins.get(k)…` — also checked.
- `ProjectionOf(k)` → checked for `arg_origins`, **but line ~731 then does
  `if let MonoExpr::Apply { span: container_span, .. } = &args[k]` — a DIRECT
  INDEX.** An out-of-range `k` from a corrupt/tampered `.meta.json` panics there.

So the one genuine panic-on-disk-content path in this family is the unvalidated
variant, and the census's justification for the row it did land is factually
wrong about the code it cites.

This is the coverage-by-definition-variants class (standing `/qa` category): an
operation that must behave uniformly across a variant family got an arm for one
member, and the other members grew a divergent (here: unchecked) consumer.

## Proposed resolution

`/dev`(backend): widen the arm to all three index-carrying variants —

```rust
&& let ResultMode::ProjectionOf(k) | ResultMode::AliasOf(k) | ResultMode::MayAliasOf(k)
     = summary.result
```

— and correct the census row's hazard text to name `transfer.rs`'s `&args[k]`
as the panic site (the `arg_origins` reads are checked). Extend the existing
`cache/serialize/tests.rs` corruption cell to a per-variant matrix so a future
fourth variant cannot escape.

Note for `/qa` / the typecheck triad separately: `&args[k]` is a raw index over
an externally-derived summary index. Even with cache validation in place, that
site should read through `args.get(k)` — validation at one boundary is not a
licence for an unchecked read at the consumer (Principle 25, narrowing carries
its check). That half is cross-crate and is NOT part of this backend fix.

## Context

Filed by `/review`(backend) during the S115 W3 change-set review; verified by
reading both the landed arm and `crates/cranelisp-typecheck/src/ownership/transfer.rs:690-750`.
The three ⊤-on-absence accessors (`param_mode`/`param_flow`/`spark_op`) are
correctly outside the census — they cannot OOB by representation, which is the
right reason to omit a row.
