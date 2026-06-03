---
number: 0253
target: /design
filed_by: /review (backend)
filed_at: 2026-06-03
sprint_filed: 76
refers_to: design/backend/jit-setup-boundary.md §1.4 (the `Jit::new()` no-arg row)
status: open
---

# `jit-setup-boundary.md §1.4` says keep `Jit::new()` (no-arg) `pub`; impl gave the `new` name to the boundary constructor

## Severity

Suggestion

## Issue

§1.4 "What it retires / narrows" carries this row:

> | `Jit::new()` (no args) | **Keep `pub`** — `Jit::new()` (empty symbol set) is the
> genuine zero-arg path some backend unit tests use; harmless. Re-expressible as
> `Jit::new(&empty_tables)` but the no-arg ergonomic is worth keeping `pub`.
> *(/design call: keep; revisit if baseline review objects.)* |

The S76 W1 implementation did NOT keep a zero-arg `pub fn new()`. The boundary
constructor took the `new` name as a generic
`Jit::new<C, L>(symbol_tables: &SymbolTables<C, L>)` — Rust cannot have both a
zero-arg `new()` and a generic `new<C,L>(..)` under the same identifier, so the
zero-arg form was necessarily displaced. The backend `public-api.txt` diff
removes `Jit::new() -> Result<Self, …>` alongside `new_with_symbols`/`new_with_isa`.

This is harmless and arguably better: the backend tests that the §1.4 row
cited as "the genuine zero-arg path" in fact call `Jit::new_with_symbols(&[])`
(kept `pub(crate)`, in-crate/test-reachable), NOT a zero-arg `new()`. So the
zero-arg `new()` had no live consumer, and the boundary deserves the canonical
`new` name. The implementation already documents the disposition in the
`lib.rs` crate-root `//!` ("non-boundary constructors `new_with_symbols`/`new_with_isa`
are `pub(crate)` — internal/test only").

## Proposed resolution

Update §1.4: strike (or amend) the `Jit::new()` "Keep `pub`" row to record the
landed disposition — the `new` identifier is the boundary constructor
`Jit::new<C, L>(symbol_tables)`; the zero-arg path is re-expressed as
`Jit::new(&empty_tables)` where genuinely needed; backend tests use the
`pub(crate)` `new_with_symbols(&[])`. The "revisit if baseline review objects"
escape hatch in the row already anticipated this outcome.

## Operational implication / Context

No code change owed — the implementation is the desired end-state and matches
the §1.4 *intent* (`Jit::new(symbol_tables)` is THE construct boundary). This
is a doc-accuracy reconciliation so the next reader of `jit-setup-boundary.md`
is not misled into expecting a zero-arg `pub fn new()` in the baseline. Pairs
with FIXME 0252 (also a `jit-setup-boundary.md` doc-accuracy correction).
