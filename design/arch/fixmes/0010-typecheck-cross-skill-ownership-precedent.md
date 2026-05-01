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
