---
number: 0498
target: /dev
filed_by: /qa
filed_at: 2026-07-03
sprint_filed: 101
refers_to: crates/cranelisp-types/src/marshal.rs, crates/cranelisp-primitives/src/marshal.rs, crates/cranelisp-types/src/{check.rs,newtype.rs,ast.rs,got.rs,scheduling.rs}, tests/plan/coverage-audit-s101.md §3.4
status: open
---

# Types: drift-guard test for the marshal byte-sync contract + minimal cover for the zero-test logic modules

**Crate**: cranelisp-types (`/dev` narrow).

## Issue

From the S101 coverage audit (`tests/plan/coverage-audit-s101.md` §3.4):

1. **`marshal.rs` (75 LOC, ZERO tests)** — its rustdoc states it must stay
   byte-synced with `cranelisp-primitives/src/marshal.rs` and with constructor
   order in typecheck `builtins.rs`: a drift-prone cross-crate constant table
   with **no drift-guard test**. This is exactly the "guarding comment substituted
   for a guard" shape that produced the S101 `kept_jits` finding
   (`s101-coverage-postmortem.md` §1.2) — a true statement that rots silently.
2. Zero-test logic modules: `check.rs` (259 LOC), `newtype.rs` (253) — logic, not
   pure data; `ast.rs` (831 — largest untested module, lower risk as data
   structures), `sexp.rs` (159), `macro_expander.rs` (137).
3. Happy-path-only strategy modules: `got.rs` (5 tests, 0 neg),
   `scheduling.rs` (8, 0 neg).

## Proposed resolution

1. A drift-guard test asserting the marshal tables/tags in cranelisp-types and
   cranelisp-primitives are identical (shared constants via dev-dependency, or a
   checksum/table-equality test — whichever the crate topology permits without a
   new production dependency edge). If the sync contract with `builtins.rs` ctor
   order can be asserted mechanically, add that arm too.
2. Minimal complexity/negative cover for `check.rs` and `newtype.rs`; negative
   arms for `got.rs` and `scheduling.rs`.

## Operational implication / Context

Small, self-contained; can ride any S102 types-touching change-set (0476's DefKind
two-armed discriminator lands in this crate at increment I's first change-sets —
the natural carrier).
