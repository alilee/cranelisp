---
number: 0044
title: Cluster-atomic typecheck — split `check_form` into two pure passes; orchestrator owns staging
status: pre-implementation
filed: sprint 66 (Phase 5 Wave 3a structural-finding resolution)
canonical_location: design/arch/facades/typecheck.md §"check_form_signatures + check_form_body"; design/arch/facades/int.md §"process_cluster — the cluster-atomic orchestration loop"; design/arch/facades/types.md §"`ParsedEntry`"; design/arch/sequences/exec-flow-compilation.mmd, exec-flow-repl.mmd, concurrency-symbol-table-entry.mmd
amends: []
amended_by: []
retracts: []
reframes: [0038]
filed_by_fixme: 0166
---

# 0044 — Cluster-atomic typecheck via orchestrator-owned staging + two pure passes

## Statement

`cranelisp_typecheck::check_form` (the single per-form pure call introduced by FIXME 0160) splits into two pure passes:

```rust
pub fn check_form_signatures<C, L>(
    parsed: ParsedEntry,
    table: &View<'_, C, L>,                      // staging ∪ live composite read view
    symbol_tables: &SymbolTables<C, L>,
) -> Result<Vec<(Symbol, ModuleEntry<C>)>, CheckError>;

pub fn check_form_body<C, L>(
    parsed: ParsedEntry,
    table: &View<'_, C, L>,                      // staging ∪ live; cluster signatures visible
    symbol_tables: &SymbolTables<C, L>,
) -> Result<Vec<(Symbol, ModuleEntry<C>)>, CheckError>;
```

Both functions are pure (no `SymbolTable` writes — FIXME 0160 structural Option B holds for both). Pass 1 produces signature-only `ModuleEntry` shells (Algorithm W fresh return-type variables); Pass 2 body-checks against the unified (staging ∪ live) view with all cluster signatures visible.

The orchestrator (`int::process_cluster`) owns a transient `SymbolTable` ("staging") for the duration of one cluster's processing. It runs Pass 1 across every form in the cluster, then Pass 2 across every form, then commits the staging table atomically into the live `SymbolTable` on success. Any `Err` from either pass drops the staging table on the floor; the live table is unchanged.

A `View<'a, C, L>` is a thin newtype on `cranelisp-types` that holds two `&SymbolTable` references (staging + live) and routes lookups (staging-first, then live). It is constructed by the orchestrator and passed to both passes; it is the read-surface typecheck sees.

**Cluster boundaries**:

- A REPL input is a one-form cluster (per the parallel `/spec` resolution of FIXME 0165 — non-`begin`-grouped REPL inputs are processed as single-form clusters; cross-input forward references are NOT supported).
- A `(begin form₁ ... formN)` REPL input is the explicit multi-form cluster boundary — the orchestrator unwraps and processes the whole list as one cluster.
- Batch (file) compilation is one big cluster covering the file's non-structural forms (per spec §5.13.1's MAY-reference-freely rule at file scope).

## Rationale

The pre-S66 `check_form` was a single in-place mutator; FIXME 0160 purified it to a single-call pure function returning entries-to-insert, with the caller committing on `Ok`. Wave 3a's first contact with implementation surfaced a structural conflict: spec §5.13.1 mandates a two-pass typecheck (Pass 1 Registration; Pass 2 Checking) to support forward references / mutual recursion at top level. A single per-form pure `check_form` cannot satisfy this — when checking `(defn f [] (g 1))`'s body, `g`'s signature must already be in scope, but a per-form caller has no opportunity to register `g`'s signature first.

The cluster-atomic shape resolves the conflict without compromising purity:

- **Typecheck stays pure** (Principle 1 — Decoupling). Both passes return entries; neither mutates a `SymbolTable`. Typecheck does not know whether it is reading staging, live, or a unioned view.
- **Live `SymbolTable` invariant restored** (Principle 7 — Single source of truth). The pre-S66 invariant — "if it's in the live table, it's checked AND committed" — is restored. Staging is a separate, orchestrator-local, transient table that is never globally visible. There is no second authoritative store; staging dissolves on cluster commit (entries move to live) or on any failure (drops on the floor).
- **Cluster-atomic commit**. A failure mid-cluster leaves the live table byte-identical to its pre-cluster state. Mutual recursion / forward references work via Pass 1 sig-registration into staging followed by Pass 2 body-check that sees all cluster signatures.
- **Single REPL form is one-form cluster**; batch is one-big-cluster. The same `process_cluster` code path serves both — Principle 11 (Single pipeline mode parameters): a uniform pipeline parameterised by the orchestrator's cluster construction.
- **Spec coupling explicit**. `(begin ...)` gains a normative role as the REPL atomicity primitive — handled by the spec twin (FIXME 0165 → `/spec` extension of §5.13.2). The architectural commitment is: clusters are the unit of typecheck atomicity; the spec defines what counts as a cluster.

### Rejected alternatives

- **Single function with a `Pass` enum parameter** (`fn check_form(parsed, table, symbol_tables, pass: Pass) -> Result<...>`). Rejected: forces dispatch noise on every consumer; collapses two narrow surfaces into one wide one (Principle 2 — narrow interfaces); makes per-pass return-type evolution awkward (Pass 1 sig-shells vs Pass 2 body-checked entries with mono variants are conceivably distinct shapes in future evolution); makes per-pass test targeting clumsier. Two explicit functions is cleaner.
- **Staging lives on `SymbolTable`** (e.g., a `SymbolTable::with_staging()` mode). Rejected: violates Principle 7 — there would be two write surfaces on the canonical store, with the live invariant ("checked AND committed") qualified by mode. Orchestrator-owned staging keeps the live `SymbolTable` invariant un-qualified.
- **Single-pass per cluster with multi-pass internal**. Rejected: hides the spec-mandated two-pass structure inside typecheck and removes the orchestrator's atomic-commit hook point. The Pass 1 / Pass 2 boundary is where the orchestrator gets its chance to fail-and-drop or success-and-commit; making it implicit forfeits the structural seam.
- **`SymbolTableView` as a separate trait that `&SymbolTable` implements**. Rejected for now: adds a trait that has one production caller pattern (orchestrator passes a 2-level view); a thin newtype `View<'a, C, L>` with explicit construction is simpler. If future needs require N-level staging or alternate read shapes, a trait can be introduced then.

## Bounded-context shift

No BC moves. Typecheck's BC ("AST → typed AST + symbol tables; pure transform") tightens — both passes are pure. Int's BC ("pipeline orchestration") absorbs cluster construction and staging ownership as a refinement of the existing `process_form` retry-loop responsibility. The new function name `process_cluster` replaces `process_form` at the orchestrator entry; the old per-form retry loop becomes a one-form-cluster degenerate case of the new shape.

## Cross-references

- `design/arch/facades/typecheck.md` §"`check_form_signatures` + `check_form_body`" — the as-designed two-call surface
- `design/arch/facades/int.md` §"`process_cluster` — the cluster-atomic orchestration loop" — orchestrator shape, staging table, View::union, atomic commit
- `design/arch/facades/types.md` §"`ParsedEntry`" + §"`View`" — boundary types
- `design/arch/interfaces.md` §"`check_form` is pure" — narrative companion update describing the split
- `design/arch/sequences/exec-flow-compilation.mmd` — typecheck-phase loop body updated for two-pass cluster shape
- `design/arch/sequences/exec-flow-repl.mmd` — REPL eval path updated for one-form-cluster + `(begin)` cluster
- `design/arch/sequences/concurrency-symbol-table-entry.mmd` — concurrent worker view updated to reference the View read surface
- `design/arch/principles.md` — Principle 1 (Decoupling), Principle 2 (Narrow interfaces), Principle 7 (Single source of truth), Principle 11 (Single pipeline mode parameters) cited as rationale
- `design/arch/decisions/0038-sharedstate-formal-worker-shareable-subset.md` (legacy) — reframes its `check_form` shape commitment to the two-pass split
- `design/arch/fixmes/0165-spec-repl-non-macro-forward-refs-and-begin-clusters.md` — `/spec` twin: §5.13.2 extension to non-macro defns; `(begin)` as REPL cluster boundary
- `spec/05-definitions.md` §5.13.1 (file scope two-pass) and §5.13.2 (REPL) — the normative grounding

## Sequencing

This Decision unblocks Sprint 66 Wave 3a re-fire. Implementation cost (~+2 days vs the original Wave 3a triad estimate) sits within the sprint envelope per `sprints/SPRINT.md`. Sequencing:

1. `/arch` lands this Decision + facade + sequence updates (this commit).
2. `/spec` lands FIXME 0165 (§5.13.2 extension; `(begin)` cluster role).
3. Wave 3a triad re-fires:
   - Frontend: `build_form` per FIXME 0156 (unchanged from prior plan).
   - Typecheck: TWO pure passes (`check_form_signatures` + `check_form_body`).
   - Int: `process_cluster`; transient staging `SymbolTable`; `View<'_, C, L>` newtype; `(begin)` unwrapping.
4. Wave 1 gate test `tests/process_form_dispatch.rs` revises (forward-ref defns wrapped in `(begin)`; second test asserts cross-input forward-ref produces a clear error).

The `View<'_, C, L>` newtype is `/arch`-authored as a `cranelisp-types` addition (per "boundary types live in `cranelisp-types`"). The two-call typecheck surface is `/dev`-implemented per the facade.
