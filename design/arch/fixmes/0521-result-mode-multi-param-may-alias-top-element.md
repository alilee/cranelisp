---
number: 0521
target: /arch
filed_by: /dev
filed_at: 2026-07-04
sprint_filed: 102
refers_to: crates/cranelisp-types/src/ownership.rs (ResultMode), design/typecheck/ownership-inference.md §13.6(c), design/arch/ownership-inference.md §3.3
status: open
---

# `ResultMode` needs a ⊤ element to name "may alias MULTIPLE distinct params"

## Issue

FIXME 0520 (result-mode partial-param-return cure, landed S102 in
`cranelisp-typecheck`) fixed the pass5 join so a param returned through a partial
control-flow path no longer collapses to `ResultMode::Fresh` (the UAF-permitting
elision value). The fix uses the existing 3-element lattice
`{Fresh, ProjectionOf(usize), AliasOf(usize)}`.

That lattice is **complete for the single-param case** (the 0520 repro and all its
enumerated siblings: partial-`if`, tail-recursion base, partial-`match`, nested
control flow, let-alias, projection-return). It is **incomplete for the
multiple-distinct-param case** — `(if c v w)` where `v` and `w` are DIFFERENT
params both reaching the result. The lattice cannot express "may alias param 0 OR
param 1"; `AliasOf(0)` and `AliasOf(1)` each name a single index.

0520 chose the sound conservative representative: **`AliasOf(lowest reaching
index)`**. This is:

- **sound for the live borrow-elision consumer** (`return_is_fresh_by_summary`,
  `cranelisp-backend/src/compiler/fn_compiler.rs`), which reads only the BINARY
  `result == Fresh` — any not-`Fresh` value keeps the return protect;
- **strictly more sound than the pre-0520 `Fresh`** (which elided protect on a
  possibly-returned param — a latent UAF for the multi-param shape too);
- **imprecise for a hypothetical future index-specific consumer.** The analysis's
  own `walk_apply` composition (`transfer.rs`) maps `AliasOf(k)` →
  `arg_origins[k]`; a multi-param callee summarised as `AliasOf(0)` under-reports
  when a caller passes a fresh value at position 0 but a param at position 1
  (`(pick fresh p)`): the caller composes `Fresh`, and if that caller's body is a
  direct `Apply` it would elide its own protect. Increment I has NO such
  index-specific composition consumer live (the only live reader is the binary
  gate, and a multi-param body is an `if`/`match` — never a direct `Apply` —
  so its own codegen never trusts `result`), so this is a latent
  precision/soundness residual, not a live defect.

## Proposed resolution

Add a distinct ⊤ element to `ResultMode` — e.g. `MayAliasParam` / `AliasOfAny`
(index-free, meaning "not `Fresh`, aliases some param, index unknown"). The
typecheck join maps the multi-distinct-param / mixed-kind case to it instead of
the lowest-index representative; `walk_apply` composition treats it as
unconditionally not-`Fresh` (never resolving to a single arg). This closes the
`(pick fresh p)` composition hole fully. It is a `cranelisp-types` carrier change
(new enum variant + `#[serde(default)]`-safe if `Fresh` stays the default) and a
`CACHE_SCHEMA_VERSION` bump in the same change-set. Because it only ever widens a
value away from `Fresh`, it is monotone-sound and additive to reverse.

## Operational implication / Context

Not required by increment I (no index-specific `ResultMode` consumer exists yet).
Recommended to co-land with the first backend consumer that reads the `AliasOf`
INDEX (rather than the binary `Fresh` test) — part 12/16 borrow-elision keyed off
the specific param, per `design/backend/ownership-codegen.md`. Until then the
0520 lowest-index representative is sound for every live consumer; this FIXME is
the durable record so the residual is not re-derived from scratch next increment.
