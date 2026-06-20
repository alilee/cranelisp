---
number: 0402
target: /spec
filed_by: /stdlib
filed_at: 2026-06-17
sprint_filed: 86
refers_to: spec/07-traits.md §7.1 (traits), spec/11-stdlib.md §"collections" / §"seq", stdlib/plan-stdlib.md §3.3, §"Phase H"
status: open
---

# Reserve `first`/`rest`/`get`/`count`/`map`/`filter` for future trait-dispatched (Functor/Foldable) unified forms

## Issue

Sprint 86 Phase 6b is curating the stdlib bare-name surface (hide raw
primitives, add Clojure-aligned wrappers). Several of the names that the
Clojure idiom most wants — `first`, `rest`, `get`, `count`, `map`,
`filter`, `reduce` — are exactly the names a future trait-dispatched
collection abstraction (Functor / Foldable / a `Seqable`-style trait,
landing in **Phase H**) will want to own as the *single, overload-unified*
entry point across `List` / `Vec` / `Seq`.

If `/stdlib` binds these bare names now to *one concrete family* (e.g.
`first` = list-`first` only, or `get` = `vec-get` only), the S86 rename
will collide with the Phase-H trait method of the same name. We need the
naming decision pinned by `/spec` so the curation and the future trait
dispatch do not fight.

Two specific coexistence questions:

1. **`first`/`rest` — list vs pair.** `collections/pair.cl` already
   defines `first`/`second` as pair accessors (the canonical tuple
   destructure, and `collections/list` exposes `head-of`/`tail-of`).
   Clojure uses `first`/`rest` for *sequences*, and `key`/`val` (or
   nth-style) for pair-like entries. If list `head-of`/`tail-of` are
   renamed to `first`/`rest` (the S86 alignment ask), they must coexist
   with pair-`first`. Today they live in different modules
   (`collections.pair/first` vs `collections.list/first`), so FQ keeps
   them distinct, but a prelude that re-exports *both* bare `first` names
   would collide (spec §8.6.4 — two distinct immediate sources).

2. **`get`/`count`/`map`/`filter`/`reduce` — concrete vs trait-dispatched.**
   These are currently per-family (`vec-get`, `vec-map`, `vec-filter`,
   `vec-reduce`, `map-list`, `filter-list`, `seq-map`, …). Phase H intends
   a trait-dispatched unified `map`/`filter`/`reduce`/`get`/`count` over a
   collection trait. S86 must NOT bind these bare names to a single
   concrete family now, or the Phase-H trait method cannot reuse the name.

## Proposed resolution

`/spec` to record (in `spec/11-stdlib.md` and/or `spec/07-traits.md`) the
following reservations so S86 curation is forward-compatible with Phase H:

- **RESERVE** `map`, `filter`, `reduce`, `count`, `get` as **future
  trait-dispatched method names** (Functor/Foldable/collection trait,
  Phase H). S86 does **NOT** bind these as bare prelude names to any
  concrete family. The concrete families keep their disambiguated names
  (`vec-map`, `map-list`, `seq-map`, …) for this sprint. (S86 *will*
  curate Vec `count`/`get`/`conj`/`assoc` inside `collections/vec.cl` as
  module-local curated wrappers — but does **NOT** re-export bare `get`/
  `count` through the prelude; they are reachable as `collections.vec/get`
  etc. until the Phase-H trait owns the bare name.)

- **`first`/`rest`** — confirm the intended bare-name owner. `/stdlib`'s
  S86 working decision (pending your ruling): rename list `head-of`/
  `tail-of` → `first`/`rest` *within `collections/list.cl`*, and keep
  pair `first`/`second` where they are, but **do NOT re-export either
  `first` through the prelude as a bare name** until Phase H decides which
  abstraction owns bare `first`. Both remain reachable FQ
  (`collections.list/first`, `collections.pair/first`). This avoids the
  §8.6.4 collision and leaves the bare name free for the Phase-H seq
  trait. Please confirm or override.

## Operational implication / Context

This pins `/stdlib`'s S86 renames so they don't have to be re-done at
Phase H. The concrete decision `/stdlib` is encoding this sprint, pending
your confirmation: **rename `head-of`/`tail-of` → `first`/`rest` in the
list module; keep these and the curated Vec verbs reachable FQ /
module-qualified only; do not promote `first`/`rest`/`get`/`count`/`map`/
`filter`/`reduce` to bare prelude names.** The bare prelude surface this
sprint stays operators + core types + macros + IO + (module-qualified)
curated collection verbs. If `/spec` rules differently, `/stdlib` adjusts
the re-export set in a follow-up.
