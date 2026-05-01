---
number: 0002
target: /arch
filed_by: /arch
filed_at: 2026-04-25
sprint_filed: 63
refers_to: design/arch/facades/typecheck.md (Public surface, as-designed)
status: open
---

# Convenience re-exports of `cranelisp-types` items from consumer crates

## Issue

`crates/cranelisp-typecheck/src/lib.rs` currently re-exports a handful of types from `cranelisp-types` (e.g., `pub use cranelisp_types::{Symbol, FQSymbol, Type, ...}`) so that consumers depending on `cranelisp-typecheck` can write `use cranelisp_typecheck::Symbol` without also depending directly on `cranelisp-types`.

The facade convention says "Re-exports only — `lib.rs` contains no logic. It `pub use`s items from internal modules." But it does not say whether re-exports of *another crate's* items are encouraged, tolerated, or forbidden.

Two paths:

(a) **Demote convenience re-exports to `pub(crate)`.** Consumers depend on `cranelisp-types` directly when they need its items. Each crate's facade exposes only what *that crate* originates. The dependency graph reads more honestly; `cargo-public-api` diffs are smaller.

(b) **Sanction convenience re-exports under a stated rule.** "A consumer crate MAY re-export an item from `cranelisp-types` if it is the sole/primary entry point users have to that item, and the re-export is documented in the facade spec's Consumed surface section." Users of one specific crate get a one-stop import; the typed-item visibility surface grows but is intentional.

## Proposed resolution

`/arch` decides between (a) and (b), and updates `arch.md` §Facade convention or §Public-API discipline to state the rule. If (a), the M5 (`pub(crate)` downgrade) pass demotes existing convenience re-exports. If (b), the rule is documented once and held going forward.

## Context

Surfaced during S63 W2 facade-spec authoring for `cranelisp-typecheck`. Affects every crate that has grown re-exports of `cranelisp-types` items organically. The `facades/typecheck.md` drift table currently lists these as "to demote" pending arbitration.
