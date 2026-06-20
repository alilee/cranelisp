---
number: 0410
target: /repl
filed_by: /sprint
filed_at: 2026-06-20
sprint_filed: 86
refers_to: repl/spec.md §0.5 (target/project-root resolution), spec/08-modules.md §8.11.4, src/session_setup.rs (load_project_config_lib_dirs / assemble_lib_dirs), design/int/cranelisp-toml.md
status: open
---

# REPL should scaffold a default `Cranelisp.toml` when pointed at a project root that lacks one

## Issue

Surfaced during S86 UAT. Today, running the REPL pointed at a project-root
directory that has no `Cranelisp.toml` is silent: `load_project_config_lib_dirs`
returns `Ok(None)` and lib-dir resolution falls through to the
`CRANELISP_LIB` env tier and the `{root}/stdlib/` default
(`src/session_setup.rs:171,229`). The user never sees that project config
exists, has no template to edit, and gets no signal that the directory is being
treated as a project root.

**Requested behavior:** when the REPL is started pointed at a project-root
directory (spec §0.5 rule 3 — `cranelisp myproject` where `myproject/` exists
and `myproject.cl` does not), and that directory has no `Cranelisp.toml`, the
REPL should **create one with sensible defaults** — a discoverable, editable
config scaffold (the `cargo`/`git init` ergonomic).

## Design fork to resolve (the trap)

`Cranelisp.toml` has **fully-replaces** semantics: spec §8.11.4 item 2 — "When
present, this takes precedence over `CRANELISP_LIB` and the default fallback."
The design doc restates it: a present file *fully controls* the lib-dir tier.

So a naively-scaffolded file is a **footgun**:
- `lib-dirs = []` (empty) present ⇒ lib resolution is now empty, which
  *suppresses* the tier-4 `{root}/stdlib/` fallback that an absent file would
  have used. Auto-creating it would silently change resolution and could break
  stdlib/prelude loading for a project that previously worked.

Two coherent resolutions (pick one; coordinate with /spec):
1. **Scaffold preserves current behavior.** The generated file's `lib-dirs`
   reproduce what the absent-file path would have resolved to (e.g. emit
   `lib-dirs = ["stdlib"]` only when `{root}/stdlib/` exists; otherwise emit a
   commented-out example and no active `lib-dirs` key). Requires that an
   **absent `lib-dirs` key** (vs. an empty list) means "fall through to lower
   tiers" — verify `#[serde(default)]` + `assemble_lib_dirs` treat a present
   file with no `lib-dirs` key as fall-through, NOT as empty-replaces. This may
   need a §8.11.4 clarification (present-file-with-absent-key ≡ tier
   fall-through for that key).
2. **Spec carve-out.** Define "a default/empty scaffold behaves identically to
   absent" normatively in §8.11.4, so scaffolding is always safe.

Either way the **§8.11.4 semantics must be settled first** (a /spec question);
this is the blocking design decision, not the file-writing mechanics.

## Open questions for /repl (scope of the trigger)

- **Trigger condition.** Only the explicit project-root-directory target (§0.5
  rule 3)? The user's phrasing ("pointing the repl to a project root
  directory") points here. Do **not** scaffold on the bare no-arg `cranelisp`
  cwd-default case — writing `Cranelisp.toml` into arbitrary cwd on every REPL
  launch would litter unrelated directories.
- **Modes.** REPL only (user said "running the repl"), or also `--run`/`--link`?
  Recommend REPL-only first; batch modes shouldn't mutate the project tree as a
  side effect of compiling.
- **Consent / noise.** Silent create, or a one-line notice (`[created
  Cranelisp.toml]`, mirroring the §-existing `[updated: <file>]` notification
  format)? A notice fits the self-documenting-REPL principle.
- **Idempotence + safety.** Never overwrite an existing file; never create
  outside the resolved project root; handle a read-only directory gracefully
  (warn, don't fail the REPL launch).

## Proposed resolution

1. /repl decides the trigger + experience (recommend: REPL mode, §0.5-rule-3
   explicit project-root target, emit a `[created Cranelisp.toml]` notice,
   never overwrite) and records it in `repl/spec.md §0.5`.
2. File onward to /spec for the §8.11.4 present-but-default semantics (fork
   above) — this gates implementation.
3. /int implements the scaffold writer in `src/session_setup.rs` beside
   `load_project_config_lib_dirs`, with a unit test (default-content +
   no-overwrite + resolution-unchanged) and an e2e (REPL launch on a bare
   project dir creates the file and still resolves the prelude).

## Operational implication / Context

- User-facing ergonomic + discoverability improvement, not a defect — current
  behavior is spec-correct (absent file falls through). Filed from UAT.
- Cross-skill: /repl (experience) → /spec (§8.11.4 semantics) → /int (impl).
- Keep the scaffold minimal — match `design/int/cranelisp-toml.md §2.2`'s
  commented template so the generated file teaches the schema.
