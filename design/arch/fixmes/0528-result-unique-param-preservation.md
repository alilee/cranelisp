---
number: 0528
target: /design
filed_by: /dev
filed_at: 2026-07-06
sprint_filed: 103
refers_to: design/typecheck/ownership-inference.md §7.2 (result_unique chaining), design/backend/ownership-codegen.md §6.4/§14.3 (II-G2 chaining metric)
status: open
---

# `result_unique` does not model uniqueness-PRESERVATION (unique-in ⇒ unique-out), so the `(map inc (map dec v))` chaining proof never holds

## Issue

The increment-II backend half (II-B2 reuse tokens, `cranelisp-backend`) is landed and
consumes the write-path facts correctly:

- `reuse_hit` / `reuse_miss` are live runtime tallies at the COW arms (`vec_codegen.rs`);
- the static-uniqueness check-elision reads `unique_static` off the **fresh-producing**
  Vec node (`node_unique_static`) and elides the dynamic `rc == 1` probe when the proof
  holds (verified: `(vec-set [10 20 30] 0 99)` takes the proof-elided in-place arm,
  value-correct, `reuse_hit=1 reuse_miss=0`).

Three of the four II-B2 flip tests are GREEN with this. The fourth,
`tests/ownership_reuse.rs::chaining_toggle_off_allocates_intermediate`, **remains RED**,
and the cause is entirely on the typecheck side — no backend mechanism can flip it.

**Empirical root cause** (probed 2026-07-06 on the `CHAIN_SRC` fixture — the fused
`(mapf inc (mapf dec v))` pipeline with an in-place `map-go`):

- The ONLY `unique_static = Some(true)` site fact typecheck emits for the fixture is on
  the `[]` empty-vec literal inside `(build [] 0 64)` — a fresh literal that already
  transfers, so it changes no allocation.
- `mapf` / `map-go` get **`result_unique = false`**, so the inner call `(mapf dec v)`
  is NOT classified `is_direct_fresh`, gets no `unique_static`, and the chaining proof
  never propagates.
- Consequently the two `map-go` first-iteration `vec-set`s each COW-**copy** (the
  `(vec-len v)` argument forces a Decision-24 consuming inc on `v` before the `map-go`
  call, so `v` is rc==2 inside `map-go`), IDENTICALLY with the analysis on and off.
  Result: `allocs = 6` and `reuse_hit=190 reuse_miss=2` on BOTH polarities ⇒ the test's
  `on < off` never holds.

`result_unique` is computed intraprocedurally from the body's return SHAPE
(`uniqueness.rs::is_fresh_unique_value`): a returned bound `Var` counts only if it is in
`fresh_bindings` (a directly-fresh RHS). A **param** returned unchanged — `map-go`'s base
case `(if (eq-i64 i n) v …)` returns the param `v` — is never `fresh`, so
`result_unique = false`. But `map-go` is semantically **uniqueness-PRESERVING**: given a
unique `v` it returns either `v` unchanged or the in-place-mutated `v` — always the same
unique root. The analysis models "result is a fresh allocation" but not "result preserves
the uniqueness of a unique param", which is exactly the property the `(map f (map g v))`
fusion (the design's own II-G2 witness, §6.4 / §14.3) rests on.

## Proposed resolution

Extend the CS-3 uniqueness stratum so `result_unique` can be proved via
**param-uniqueness preservation**, not only fresh-allocation:

- a callable whose result is a param `p` (returned directly, or through an in-place
  COW/reuse op like `vec-set`/`vec-push` that returns the same root) is `result_unique`
  **conditional on `p` being passed unique** — i.e. a "unique-in ⇒ unique-out" summary
  bit (or a param-index the result aliases, combined with the caller minting
  `unique_static` when it passes a proven-unique arg to that param);
- with that, `(mapf dec v)` chains `unique_static = Some(true)` to `mapf`'s result, the
  outer `(mapf inc …)` composes, and — the load-bearing half — the `map-go` `vec-set`
  consuming-use sites carry `unique_static = Some(true)` so the backend's already-landed
  check-elision fires there (currently it only fires for fresh-node Vec args, per the
  §6.4 HARD requirement — reading off the consuming-use `Var` is forbidden and dead).

Whether the fact lands on the `vec-set` **consuming-use node** (§6.4's stated carrier)
or via a caller-side transfer keyed on a preserved-uniqueness summary is `/design`
(typecheck)'s call; the backend consumes `unique_static` off the fresh-producing /
consuming Apply node either way (`node_unique_static` already matches `Apply`).

## Operational implication / Context

- `chaining_toggle_off_allocates_intermediate` is on the S103 Wave-3b MUST-flip list but
  is **not flippable by backend work alone** — it is a joint /backend + /typecheck (B1/B2)
  deliverable, as the test's own doc-comment states ("once `result_unique` chaining +
  reuse tokens land"). The backend half is complete; the `result_unique` chaining for
  uniqueness-preserving (map-shaped) callables is the missing precondition.
- The other three II-B2 flips + h3 are GREEN this wave.
- No spec change; this is an analysis-precision extension (monotone-sound — absent the
  new proof, everything degrades to the dynamic rc==1 token, exactly as today).
