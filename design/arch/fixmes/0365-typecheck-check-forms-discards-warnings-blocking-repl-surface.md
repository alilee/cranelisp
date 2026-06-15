---
number: 0365
target: /typecheck
filed_by: /dev
filed_at: 2026-06-15
sprint_filed: 83
refers_to: crates/cranelisp-typecheck/src/form.rs:306 (check_forms discards `_result = env.finalize_check_result(..)`), crates/cranelisp-typecheck/src/result.rs:20 (CheckResult.warnings), crates/cranelisp-typecheck/src/program.rs:1459 (deferred_accessor_collisions -> ShadowedName warning)
status: open
---

# `check_forms` discards its `CheckResult` (warnings) — int cannot surface typecheck `Warning`s in the REPL (blocks FIXME 0363 Gap B)

## Issue

FIXME 0363 Gap B asked int to "surface typecheck `Warning`s in the REPL eval
path" so the §5.2.6 accessor/binding collision guard
(`accessor_neg_synth_does_not_shadow_existing_binding`) can see the
`WarningKind::ShadowedName` diagnostic. The int receiving-end plumbing is now in
place (S83 W2, see Operational implication below) — but **no warning ever
reaches int**, because the typecheck facade discards it.

`cranelisp_typecheck::check_forms` (the sole cluster-typecheck entry, per
Decision 44's third amendment) is declared:

```rust
pub fn check_forms<C, L>(
    parsed: Vec<ParsedEntry>,
    ctx: &mut SymbolTableAccess<'_, C, L>,
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
    prelude_fallback: &PreludeFallback,
) -> Result<(), CheckError>
```

Internally (`form.rs:306`) it builds the full `CheckResult` — which carries
`warnings: Vec<Warning>` — and **explicitly discards it**:

```rust
let _result = env.finalize_check_result(..).map_err(..)?;
Ok(())   // CheckResult (with warnings) dropped on the floor
```

The `ShadowedName` warning for the accessor/binding collision IS produced
(`program.rs:1459`, drained from `state.deferred_accessor_collisions` into
`accumulator.warnings` → `CheckResult.warnings`), but the `Ok(())` return type
gives the int caller (`src/worker.rs::process_cluster_with_staging`) no way to
read it. There is also no warning accessor on `SymbolTableAccess` or on
`CheckState` (the latter is constructed *inside* `check_forms`, not the
int-passed `repl_check_state`), so warnings are unreachable through `ctx` after
the call. Confirmed empirically: NO typecheck warning (not `UnusedBinding`,
`UnreachableArm`, nor `ShadowedName`) has ever appeared in REPL output — the
warning-surfacing pipeline has been dead at this boundary since the Wave-3a-β
collapse.

## Proposed resolution

Surface the warnings across the `check_forms` boundary so the existing int
receiving end can display them. Either:

- **(A)** change `check_forms` to return the warnings on the success path —
  `Result<Vec<Warning>, CheckError>` (or `Result<CheckResult, CheckError>` if
  the `display` half is also wanted); OR
- **(B)** add a public drain accessor on `SymbolTableAccess` (e.g.
  `take_warnings(&mut self) -> Vec<Warning>`) that `check_forms` populates
  before returning `Ok(())`, which the int caller reads after the call.

This is a `cranelisp-typecheck` public-surface change (and may touch the
`cranelisp-types`/facade boundary — defer the return-shape choice to /typecheck
+ /arch). The int side (`check_program_compat` →
`process_cluster_with_staging`) will then thread the surfaced warnings out
through `finalize_cluster` onto `ProcessedCluster.warnings`, where the
already-landed S83 W2 plumbing carries them to `EvalResult::warnings` and
`format_eval_result` renders them as `; warning: <message>` lines.

## Operational implication / Context

S83 Phase 5 Wave 2. FIXME 0363 Gap A (codegen-batch the synthetic accessor
bodies) is landed and green —
`generated_field_accessor_resolves_as_free_callable` and
`accessor_is_first_class_value_passable` pass. Gap B's int receiving end is
landed:

- `src/eval.rs::process_form_cluster` now threads
  `processed.warnings()` into the `CheckResult` (was a hardcoded empty `Vec`);
- `src/repl.rs::format_eval_result` now renders each `EvalResult` warning as a
  `; warning: <message>` line ahead of the value/def display.

The ONLY remaining gap for
`accessor_neg_synth_does_not_shadow_existing_binding` is this typecheck-side
warning leak: `finalize_cluster` (`src/process_form.rs:1098`) builds
`ProcessedCluster::empty()` because `check_program_compat` (→ `check_forms`)
returns no warnings to fill it with. Once /typecheck surfaces them, int's
`finalize_cluster` fills `ProcessedCluster.warnings` from the surfaced set and
the guard flips green with no further int change beyond that one-line fill.
