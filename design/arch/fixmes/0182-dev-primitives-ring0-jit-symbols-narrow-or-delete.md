---
number: 0182
target: /dev (primitives, int)
filed_by: /design (primitives)
filed_at: 2026-05-15
sprint_filed: 67
refers_to: design/arch/facades/primitives.md §"`ring0_jit_symbols()` — internal-but-exposed", crates/cranelisp-primitives/src/ring0.rs, crates/cranelisp-primitives/src/lib.rs §"pub use ring0::ring0_jit_symbols"
status: partially-resolved
sprint_partial: 67
partial_residue: backend still consumes ring0_jit_symbols + 21 other extern fns by direct Rust path (see FIXME 0191 expanded scope); both ring0_jit_symbols narrow AND the broader extern-fn demotion blocked on backend migration to PRIMITIVES_TABLE.
---

# Narrow `ring0_jit_symbols()` to `pub(crate)` (or delete) after FIXME 0159 lands

## Issue

`pub fn cranelisp_primitives::ring0::ring0_jit_symbols() -> Vec<(&'static str, *const u8)>` (re-exported at the crate root) is the **pre-FIXME-0159 mechanism** for `int`'s session-init code to seed JIT symbols. It is one of two `pub` items on the primitives crate today (the other 21 items being `#[export_name = "…"] pub(crate)`-target extern fns, demoted by FIXME 0159).

Once FIXME 0159 lands the `PRIMITIVES_TABLE: LazyLock<SymbolTable>` static, `ring0_jit_symbols()` is **superseded**: `int` reads symbol-name → fn-ptr pairs from `PRIMITIVES_TABLE`'s `ModuleEntry::Def` entries (via the per-module `GotTable`) instead of from the `Vec<(&'static str, *const u8)>` return value of this free fn. The facade's stated public surface for the post-FIXME-0159 state is **one item only** (`PRIMITIVES_TABLE`); `ring0_jit_symbols` is incompatible with that target.

## Proposed resolution

In the same change-set that lands FIXME 0159 (Wave 3 `/dev (primitives, int)`):

1. Migrate `int`'s consumer (search `src/` for `ring0_jit_symbols` — likely in session init / JIT-symbols seeding path) to read from `PRIMITIVES_TABLE` instead.
2. Narrow `ring0_jit_symbols` to `pub(crate)` in `crates/cranelisp-primitives/src/ring0.rs` AND remove the `pub use ring0::ring0_jit_symbols` re-export from `crates/cranelisp-primitives/src/lib.rs`. If no in-crate consumer remains after the int migration, delete the function entirely.
3. Regenerate `crates/cranelisp-primitives/public-api.txt` in the same commit per the baseline-diff discipline (`design/arch/CLAUDE.md §"Baseline-diff discipline"`). The post-Wave-3 baseline should show one pub item: `PRIMITIVES_TABLE`.

## Operational implication / Context

- Confirms the facade's stated post-FIXME-0159 target: one published Rust API item per `cranelisp-primitives`.
- Reduces the `cargo-public-api` baseline to its target one-line shape (per `facades/primitives.md §"Versioning policy"`).
- No JIT-symbol-name churn — symbol-table seeding path semantics are unchanged; only the Rust-API path through which `int` reads them changes.
- Caller-side coordination: the migration in `int` (consumer side) MUST land in the same change-set as the narrowing in `primitives` (definition side) or `int` will fail to compile. Wave 3 `/dev (primitives, int)` is a coordinated change per the sprint plan.
