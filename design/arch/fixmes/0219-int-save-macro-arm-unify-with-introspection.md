---
number: 0219
target: /dev (int)
filed_by: /arch
filed_at: 2026-05-25
sprint_filed: 70
refers_to: src/save.rs §macro-regen-arm, design/arch/decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md, design/arch/bounded-contexts.md §int, design/arch/sequences/exec-flow-compilation.mmd
status: open
---

# Unify save.rs macro arm with Introspection (post-D41 symmetry)

## Issue

`src/save.rs` (lines 280-310 in the regeneration walk) carries an asymmetric
dual-path between ordinary `Def` entries and macros:

- **`UserFn` arm** (correct, D41-compliant): looks up the entry's FQSymbol in
  `introspection: &DashMap<FQSymbol, Introspection>` and reads `intro.sexp`
  for the regenerated form.
- **Macro arm** (pre-D41 leftover): reads `sexp` directly from a now-retired
  `ModuleEntry::Macro.sexp` field — and after S70 Phase 3 row #6 +
  variant-amendment cascade, the source field is gone (the `DefKind::Macro`
  variant has been reduced to `{ clauses_meta }` per Decision 41's canonical
  Introspection ruling; see the `DefKind::Macro` rustdoc in
  `crates/cranelisp-types/src/module.rs`).

The macro arm currently still references the retired sibling variant pattern
and will stop compiling once the row #6 cascade in `cranelisp-frontend` /
`cranelisp-typecheck` / consumer crates lands. The save.rs path must change
in step: macros, like every other `Def` variant, read their `sexp` from the
`Introspection` record keyed by FQSymbol.

## Proposed resolution

Collapse the two arms to one shape:

```rust
match entry {
    ModuleEntry::Def { kind, .. } => {
        // Predicate: include both UserFn and Macro for regeneration; skip
        // primitives, special forms, and synthetic constructors.
        let include = matches!(
            kind.as_ref(),
            DefKind::UserFn { .. } | DefKind::Macro { .. },
        );
        if !include { continue; }
        let fq = FQSymbol { module: module_path.clone(), symbol: name.clone() };
        if let Some(intro) = introspection.get(&fq)
            && let Some(ref sexp) = intro.sexp
        {
            items.push((name.to_string(), sexp.clone()));
        }
    }
    _ => {}
}
```

The `ModuleEntry::Macro` arm is deleted entirely. Macros surface through the
unified `ModuleEntry::Def` arm with `DefKind::Macro` predicate inclusion.

## Operational implication / Context

### Pre-D41 leftover

This dual-path was authored when macros lived in a separate
`ModuleEntry::Macro` variant carrying its own `sexp: Option<Sexp>` field —
the read-from-types-layer pattern matched the variant's data shape. With
S69 Submission 22's variant-retirement (macros became `ModuleEntry::Def`
entries with `kind: DefKind::Macro { clauses_meta, sexp, source }`) the
sexp continued to live on the Def variant, perpetuating the asymmetry.
With S70 Phase 3's variant-amendment (`DefKind::Macro { clauses_meta }` only
per Decision 41), the sexp moves to Introspection like every other Def's
sexp — the asymmetry collapses.

### Cache-hit residual gap

When a module loads from cache, `Introspection` is not rehydrated (it is
`#[derive(Default)]`, non-Serde, REPL-only per BC §int). REPL editing of a
cache-loaded module therefore cannot trigger `.cl` regeneration for symbols
whose Introspection entries are absent. **Serializing `Introspection` into
the cache is NOT the answer** — it mixes concerns (compiler cache vs.
introspection record), bloats the cache, and raises invalidation questions
(`source` text drifting from a touched file; `clif_ir` snapshotted from a
stale codegen build).

The future fix path is **lazy re-read of the backing source file on
demand**: when REPL editing needs source/sexp for a symbol that has no
Introspection entry, re-parse the file region that defined the symbol and
populate its Introspection. Tracked separately in
FIXME 0220 ("int cache-hit source rehydration on demand"). This save.rs
unification is independent — it solves the symmetry problem; the
cache-hit gap remains an architectural debt item, no different from the
pre-S70 state.

### Downstream link

This FIXME activates after:

1. The S70 Phase 3 row #6 cascade-plan lands (consumer crates migrated off
   `DefKind::Macro.sexp` / `DefKind::Macro.source`).
2. The `DefKind::Macro` variant in `crates/cranelisp-types/src/module.rs`
   has been reduced to `{ clauses_meta }` — already landed via S70 Phase 3
   (this FIXME's filing change-set).

Once both have landed, this save.rs arm-unification can run as a
self-contained int-crate edit. Coordinate with `/sprint` for sequencing
within the Phase 3 close walk.

### Skill scope

`src/save.rs` is `/dev (int)` territory — int owns the integration-layer
regeneration path. `/arch` files this FIXME; `/dev (int)` executes.
