---
number: 0010
target: /typecheck
filed_by: /int
filed_at: 2026-05-01
sprint_filed: 64
refers_to: crates/cranelisp-typecheck/src/checker.rs:205-213
status: open
migrated_from_inline: true
---

# 0010 — Cross-skill hybrid ownership precedent on `ensure_module_exists`

## Issue

`/int` authored the rewrite of `ensure_module_exists` in `crates/cranelisp-typecheck/src/checker.rs` (a `/typecheck`-owned crate) under an explicit `/arch` cross-skill grant to close the H6 non-atomic compare-then-set race (see `design/int/heisenbug-race-closure.md §3d''`, /arch mini-review, Sprint 61 Wave 3, 2026-04-22). The public signature of `ensure_module_exists` is untouched. The FIXME documents the precedent as NARROW and explicitly NON-GENERALISABLE — further `/int → crates/` edits remain blocked without `/arch` arbitration. `/typecheck` is asked to (a) review the diff and confirm the approach still aligns with typecheck-crate intent, and (b) explicitly accept the precedent boundary so this entry can close.

## Source location

`crates/cranelisp-typecheck/src/checker.rs:205-213` (in the doc comment block above `ensure_module_exists`).

## Context

The mechanism (option d per §8.3.1 + /arch §3d'' mandatory variant): hoist the `user`-seed clone outside `entry()` so the `or_insert_with` closure performs no nested DashMap access; `entry(path).or_insert_with(|| {...})` then performs the check-then-insert atomically under the shard write-lock. See the comment block in-source for the full invariant statement.

## Proposed resolution

`/typecheck` reviews the rewrite, records acknowledgment of the narrow cross-skill precedent (e.g. via a one-line note in `crates/cranelisp-typecheck/CLAUDE.md` if appropriate), and either accepts in-place or proposes a `/typecheck`-owned reshape. Carry from S62 baseline ledger per `sprints/SPRINT.md §"Carries from S62"`.

## Disposition — CLOSE: precedent OVERTAKEN by relocation (S81 /arch Phase-3 ruling, 2026-06-13)

**The cross-skill precedent this FIXME preserved no longer exists as code — close it; no precedent boundary needs accepting.** Verified against current source (2026-06-13):

The `/int`-authored H6-race-closing rewrite that this FIXME flagged — the atomic `entry(path).or_insert_with(...)` create-if-absent in `crates/cranelisp-typecheck/src/checker.rs:205-213` — **has been relocated out of the `/typecheck` crate entirely.** The atomic logic now lives as a free `pub fn ensure_module_exists` in **`cranelisp-types`** (`crates/cranelisp-types/src/module.rs:1816`) — `/arch`'s own crate. What remains in typecheck (`checker.rs:571`) is a thin `pub(crate)` **shim** that delegates to the types-crate fn (`cranelisp_types::ensure_module_exists(self.modules, path)`) and adds only typecheck-local trace emission — its own rustdoc (the "Sprint 67 hack-back, FIXME 0192+0193" note) marks it as the backward-compat shim and directs cross-crate callers to the types free fn directly.

Consequences for 0010:

1. **There is no `/int`-authored code in a `/typecheck`-owned file at `checker.rs:205-213` anymore** — the H6-race authority moved to `cranelisp-types`, where authorship is `/arch`-only by definition. The "narrow, non-generalisable cross-skill precedent" the FIXME asked `/typecheck` to formally accept has dissolved: the boundary it guarded (an `/int → crates/cranelisp-typecheck/` edit standing in another skill's crate) no longer applies to this code.
2. **The remaining typecheck shim is ordinary `/typecheck`-owned (`/dev`-narrow) code** — a `pub(crate)` wrapper, authored and maintained by whoever is narrow-deployed to typecheck. No cross-skill grant governs it.

**Action (for `/typecheck`, as resolver):** verify the relocation against `module.rs:1816` + `checker.rs:571` (above), then `git rm` 0010 with a commit note: "0010 closed — `/int`→typecheck `ensure_module_exists` precedent overtaken; atomic logic relocated to `cranelisp_types::ensure_module_exists` (`module.rs:1816`), typecheck retains only a `pub(crate)` shim (`checker.rs:571`)." No CLAUDE.md precedent-acknowledgment note is needed — the precedent it would have recorded is moot. Eligible for the typecheck wave (W4) or W2 stale-sweep. (Disposition ruled by `/arch`; the close is `/typecheck`'s per the target field.)
