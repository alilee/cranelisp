---
number: 0416
target: /arch
filed_by: /port
filed_at: 2026-06-20
sprint_filed: 87
refers_to: spec/appendix-a-builtins.md §A.3 (primitive functions), spec/11-stdlib.md, exemplar/grid.cl §"Bitmask operations" (lines 71-126), exemplar/CLAUDE.md §"Design Decisions" ("No bitwise primitives")
status: open
---

# Bitwise intrinsics (`bit-and`/`bit-or`/`bit-xor`/`bit-not`/`shl`/`shr`/`popcount`) for bitmask domains

## Issue

The Sudoku exemplar represents each cell's candidate set as a 9-bit integer
mask (bits 0-8 ↔ digits 1-9) — the natural, allocation-free representation. But
Cranelisp has **no bitwise primitives**, so `exemplar/grid.cl` (lines 71-126)
hand-rolls the entire bit layer in arithmetic:

- `pow2 n` — repeated multiplication to synthesise `1 << n`
- `bit-set? mask d` — `(= (rem-i64 (/ mask (pow2 (- d 1))) 2) 1)` to synthesise
  `(mask >> (d-1)) & 1`
- `bit-clear` / `bit-set` — conditional `- / +` of `(pow2 (d-1))` to synthesise
  `& ~(1<<n)` / `| (1<<n)`
- `bit-count` (popcount) — a 9-iteration recursive scan
- `bit-lowest` — a 9-iteration recursive scan for the lowest set bit

This is the single largest source of "contorted to fit the language" code in
the exemplar: ~55 lines simulating five one-instruction CPU operations. It is
**not stdlib-composable** — you cannot write an efficient (or even correct, for
the general case) `bit-and` from `+ - * /`; the arithmetic identities only hold
because the masks are known-small (≤ 9 bits) and non-overlapping in the ways the
code uses them. A real bitmask/flags/hashing/checksum domain cannot rely on
those constraints.

This is a recurring application-domain need (flags, sets-as-masks, bit-packed
state, hashing, RNG), not a Sudoku quirk.

## Proposed resolution

Add bitwise integer intrinsics to the primitive surface (Ring 0 / appendix-a),
and a thin curated stdlib wrapper layer (`num/bits.cl`) over them:

| Primitive | Signature | Notes |
|---|---|---|
| `bit-and` | `(Fn [Int Int] Int)` | |
| `bit-or`  | `(Fn [Int Int] Int)` | |
| `bit-xor` | `(Fn [Int Int] Int)` | |
| `bit-not` | `(Fn [Int] Int)` | two's-complement on the Int width |
| `shl`     | `(Fn [Int Int] Int)` | logical/arith left shift |
| `shr`     | `(Fn [Int Int] Int)` | (decide arithmetic vs logical — spec) |
| `popcount`| `(Fn [Int] Int)` | optional; expressible from the above + a loop, but a single CLIF `popcnt` is cheap |

Cranelift exposes all of these directly (`band`, `bor`, `bxor`, `bnot`, `ishl`,
`ushr`/`sshr`, `popcnt`), so codegen is a near-trivial 1:1 lowering. The work is:
(1) `/spec` decides Int width semantics + signed-shift behaviour and adds the
appendix-a rows; (2) `/backend` lowers each to its CLIF op; (3) `/stdlib` curates
a `num/bits.cl` with Clojure-aligned names (`bit-and`, `bit-or`, …, `bit-test`,
`bit-set`, `bit-clear`) over the primitives.

## Operational implication / Context

- Routes to the **Stage-B audit backlog / Wave-2 /arch synthesis** as the
  highest-impact COMPILER gap surfaced by the exemplar adequacy review (S87
  Stage C.1). It gates on `/spec` (semantics) + `/backend` (lowering), so it is
  NOT in-sprint `/stdlib` (C.2) work.
- Once it lands, `grid.cl`'s `pow2`/`bit-*` block collapses from ~55 lines to
  direct intrinsic calls (or `num.bits/*` imports), and the "No bitwise
  primitives" Design Decision in `exemplar/CLAUDE.md` is retired.
- No failing test exists for this (it is a missing-feature gap, not a defect),
  so a FIXME is the correct record per `memory/feedback_no_fixme_with_failing_test`.
