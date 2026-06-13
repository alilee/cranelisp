---
number: 0298
target: /arch
filed_by: /sprint
filed_at: 2026-06-08
sprint_filed: 76
target_sprint: 77
refers_to: design/arch/facades/int.md, design/arch/bounded-contexts.md §6, design/arch/CLAUDE.md (facade table, line ~15), tests/facade_pif_rows.rs::shared_state_field_count_matches_facade_after_pif, src/main.rs, repl/spec.md
status: open
---

# int facade reframe (RATIFIED) + W-Retire as a doc-reorg (S77)

## Ratified understanding (user, 2026-06-08)

`int` is a **binary**, so the library-facade pattern (a boundary contract gated by
`public-api.txt`) was never the right fit for it. What int's "facade" actually
comprises, classified:

| Layer | Boundary? | Canonical home |
|---|---|---|
| **CLI** — the three modes (`--run`, `--link`, REPL) + options (`--no-color`, worker counts, target), parsed in `src/main.rs::parse_args` | **YES** — int's real outside-in contract | scattered in `spec/`; **no single CLI reference** (`user/` is empty); `main.rs` has no crate rustdoc |
| **REPL experience** | YES | `repl/spec.md` (settled) |
| **Language behaviour** | YES | `spec/` (settled) |
| **Cross-crate types** — `check_forms<C,L>` signature + the `cranelisp-types` values it operates on | YES | `cranelisp-types` + typecheck rustdoc (settled) |
| **`CompilerSession`, `SharedState`, `CompileScheduler`, `worker`, `cluster`** | **NO** — internal orchestration, no external/cross-crate consumer | should be `design/int/` design docs + `src/` source rustdoc |

Key evidence: `SharedState` does **not** cross into typecheck — typecheck depends
only on `cranelisp-types` + `cranelisp-frontend` and cannot name `SharedState`
(the lone hit in the typecheck crate is a comment). int unpacks SharedState's
constituent boundary-type fields (`symbol_tables`, `module_aliases`,
`next_type_id`) and passes those individually through `check_forms`. SharedState
itself is int-internal plumbing.

**Consequences (ratified):**
1. The int facade-**as-boundary** (CLI + REPL + cross-crate types) is **solid**.
2. `SharedState`'s shape is **internal** — it does NOT gate facade-settledness and
   may keep evolving (the FIXME 0176/0179 cluster-atomic redesign) with zero
   effect on any boundary. (The S76 "facade not solid because SharedState
   diverges" worry conflated internals with the boundary — withdrawn.)
3. **W-Retire is therefore a documentation reorganization, NOT gated on
   0176/0179.** `facades/int.md` is ~90% internal architecture mislabeled as a
   "facade."

## S77 action — W-Retire as doc-reorg

1. **Internal orchestration** (`CompilerSession`/`SharedState`/scheduler/worker/
   cluster + the ~30 `facades/int.md` sections describing them) → migrate to
   `design/int/` design docs + `src/` source rustdoc (crate-root `//!` +
   per-item `///`). Most of int.md's target-stating + PIF/drift annotations
   **dissolve** (they tracked an as-designed↔as-built gap that is meaningless
   once source is canonical), exactly as in the 7 prior library-facade retirements.
2. **Outside-in CLI surface** — give it the home it lacks: a CLI reference
   (a `user/` doc, /docs-owned, since `user/` is currently empty) and/or a
   `main.rs` crate-level `//!` rustdoc narrative for the modes + options.
   REPL stays in `repl/spec.md`; language behaviour stays in `spec/`.
3. **`bounded-contexts.md` §6** — add the closing "Per-surface documentation"
   paragraph (the 8th and final data point of the retirement pattern).
4. **`design/arch/CLAUDE.md`** facade-table row — flip int → retired; "no
   remaining live facades" (completing the 8-surface arc).
5. **No `public-api.txt` baseline owed** for int — a binary has no external
   consumers; `facade_compliance.rs` already excludes it (tombstone). Its
   conformance is the e2e suite.
6. **Reclassify `tests/facade_pif_rows.rs::shared_state_field_count_matches_facade_after_pif`**
   — it introspects an internal struct, so it does not belong in a
   *boundary*-conformance file. Move it to an int-internal design-target tracker
   (or fold it into the 0176/0179 tracking). It stays failing-not-ignored either
   way until the cluster-atomic redesign reduces SharedState to target.

## Context

Surfaced in S76 Wave 5 while clearing the public-api conformance gates. W-Settle
completed in-sprint (all format-staleness gates cleared, `schema_literal`
removed, `public_api_check` green, `facade_pif_rows` 20/21). The capstone
(W-Retire) + the SharedState field reduction are both correctly carried to S77 —
not because they're blocked on the facade being unsolid, but because (a) the
SharedState reduction is gated on the 0176/0179 cluster-mode redesign (a large
same-crate pipeline effort), and (b) the W-Retire doc-reorg is best done as one
deliberate pass, not at sprint close. The reframing above means neither blocks
the *boundary* from being considered settled.

## Absorbed: FIXME 0281 (int-facade dead-API trim) — S81

The S81 stale-FIXME sweep (batch 3) confirmed FIXME 0281 stale and folded it
into this FIXME. 0281 asked to trim the dead `priority_boost_jit` /
`wait_for_inmem` priority-codegen pseudocode from the int facade. That subsystem
was never needed and is already deleted from source (B5 disposition — see
`src/CLAUDE.md` and `src/scheduler.rs`); only retrospective comments remain. The
dead-API references therefore do not carry into the retired int facade, so the
0281 trim is subsumed by the W-Retire doc-reorg tracked here. 0281 deleted in S81.
