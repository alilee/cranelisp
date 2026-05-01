---
number: 0047
target: /int
filed_by: /stdlib
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/stdlib/examples-run-path.md:277
status: open
migrated_from_inline: true
---

# 0047 — Examples-run smoke test does not find prelude

## Issue

Sprint 60 Workstream F implementation discovered that the documented smoke-test command (`cargo run -- --run examples/01-integers.cl`) does NOT find the prelude by itself. Running that command sets `project_root=<cwd>/examples` per `resolve_target` (spec §0.5.1 rule 2). Prelude discovery (`resolve_prelude` → `assemble_lib_dirs`) then looks for `examples/prelude.cl`, `examples/Cranelisp.toml`, `$CRANELISP_LIB`, and `examples/stdlib/` — none exist. Result: no prelude loaded, primitives inaccessible as bare names.

The primitive re-exports are CORRECT — the fix was verified end-to-end with `CRANELISP_LIB=$(pwd)/stdlib cargo run -- --run examples/01-integers.cl`. The remaining work is making the bare command find the prelude (likely via an `examples/Cranelisp.toml` that points at `../stdlib/` — already addressed in Sprint 60 Wave 2 per `user/CLAUDE.md`'s S60 W4 note, but the design FIXME persists).

Could be `/int` (resolver) or `/examples` (provide a `Cranelisp.toml`).

## Source location

`design/stdlib/examples-run-path.md:277` (FIXME inside §4.4 step 4 rollout note).

## Context

Section §4.4 documents the rollout for the prelude re-export fix. The FIXME marks the residual bare-command-finds-prelude work.

## Proposed resolution

If `examples/Cranelisp.toml` already points at `../stdlib/`, confirm and remove the FIXME from the design doc. Otherwise: `/int` adjusts resolver default-search (or `/examples` adds the config file).
