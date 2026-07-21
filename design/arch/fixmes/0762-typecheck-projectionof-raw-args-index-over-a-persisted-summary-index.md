---
number: 0762
target: /arch
filed_by: /dev (cranelisp-backend, S115 W3b)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-typecheck/src/ownership/transfer.rs (the `ResultMode::ProjectionOf` arm's `&args[k]`); design/arch/safety-invariants.md §4 R6 + Principle 25
status: open
---

# `ProjectionOf(k)` raw-indexes `args[k]` — an externally-derived index read unchecked at the consumer, one boundary past its validation

## Severity

Important — a panic on disk content is now unreachable via the cache path
(W3b closed that boundary), but the read itself still violates Principle 25 and
the register's own remedy language. Not a Blocker: with the R6 arm in place
there is no known reachable path.

## Issue

`/review` filed FIXME 0750 against the backend half of this: the R6 cache-load
census validated `ResultMode::MayAliasOf(k)` — the ONE index-carrying variant
whose consumers all read through a checked `arg_origins.get(k)…unwrap_or(Fresh)`
— and omitted `ProjectionOf`/`AliasOf`. The genuine panic-on-disk-content site
in the family belongs to the omitted variant: the `ProjectionOf` arm at the
consume seam does

```rust
if let MonoExpr::Apply { span: container_span, .. } = &args[k]
```

— a **raw index** over an index that arrived from a persisted `ModeSummary`.

W3b landed the backend half: the validation arm now covers all three variants
via an exhaustive `result_mode_param_index` (a new variant is a compile error,
not a silent census escape), and the census rustdoc names `&args[k]` as the
actual hazard rather than the checked `arg_origins` reads it wrongly cited.

**The consumer-side half is cross-crate and was NOT touched** — `/dev` was
narrow-deployed to `cranelisp-backend` and may not edit typecheck source. 0750's
own "Note for `/qa` / the typecheck triad" says the same, and 0750 is now
resolved+deleted, so the note needs its own home or it is lost.

## Proposed resolution

Route to the typecheck triad: read through `args.get(k)` (declining the
projection-provenance refinement on a miss is monotone-sound — it widens toward
the conservative point). Principle 25: **validation at one boundary is not a
licence for an unchecked read at the consumer.** The R6 arm makes the cache path
safe; it does not make the index trustworthy in general, and a future producer
bug or a second (unvalidated) transport would land straight on the raw index.

`/arch` may prefer to fold this into the `safety-invariants.md` §4 R6 row's
remedy language rather than open a separate work item — the register row is the
natural home for "the boundary is validated AND the consumer is checked".

## Instrumentation (METHOD §2.2)

**(b) — the instrument existed but was blind.** The R6 census IS the standing
instrument for this class, and it was **prose in a rustdoc table**: nothing
mechanically related the table's rows to the persisted-index families, so a
family could be described, mis-attributed, and partially covered all at once —
which is exactly what happened. The backend correction rode the fix
(`result_mode_param_index`, exhaustive). The generalisation worth ruling on:
**every §4 register row whose subject is a closed sum should be enforced by an
exhaustive match somewhere, not only described** — otherwise the register
documents an invariant that the code is free to drift from silently.

## Context

Filed by `/dev`(backend) at S115 W3b while resolving FIXME 0750, to preserve
0750's cross-crate half before deleting it.
