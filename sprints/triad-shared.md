# Per-crate triad — shared procedural content

> This file is **imported** by `.claude/commands/dev.md`, `.claude/commands/design.md`, and `.claude/commands/review.md`. It is not a directly-invocable skill. Edit here once; all three triad skills inherit.
>
> Owner: `/sprint`. Imported by the triad skill defs at the top via `@sprints/triad-shared.md`.

The per-crate triad (`/design`, `/dev`, `/review`) is three skills that narrow-deploy to one of 6 crate-shaped surfaces per invocation. They share the procedural rules below; their role-specific content (what each does, owns, must not do) is in their individual skill defs.

## The 6 crate-shaped surfaces

The triad narrow-deploys to exactly one of:

| Surface | Crate paths | Facade |
|---|---|---|
| Frontend | `crates/cranelisp-frontend/` | `lib.rs` |
| Typecheck | `crates/cranelisp-typecheck/` | `lib.rs` |
| Backend | `crates/cranelisp-backend/` | `lib.rs` |
| Runtime | `crates/cranelisp-primitives/` + `crates/cranelisp-intrinsics/` (D43 split of the former `cranelisp-runtime`) | `lib.rs` |
| Platform | `crates/cranelisp-platform/` | `lib.rs` |
| Binary (int) | `src/` + `crates/cranelisp-exe-bundle/` | `src/lib.rs` + `src/main.rs`; `crates/cranelisp-exe-bundle/src/lib.rs` |

The non-triad surface `crates/cranelisp-types/` is `/arch`'s direct ownership — triad skills do not narrow-deploy to it. Cross-crate type changes are filed as FIXMEs `target: /arch`.

The full bounded-context statement for the surface is in `design/arch/bounded-contexts.md`; the as-designed public API is in `design/arch/facades/{crate}.md`. Both are normative.

## First steps on every invocation

1. **Confirm the crate in scope.** From the invocation prompt, the active `SPRINT.md` wave assignment, or — if neither names it — ask the user. Never proceed against an ambiguous surface.
2. **Read `design/arch/bounded-contexts.md`** — the section for your surface. This is what the crate is responsible for, where it ends, and what crosses the boundary. Triad work is in-scope when it stays inside the bounded context; out-of-scope work routes via FIXME (cross-crate questions to `/arch`; spec ambiguity to `/spec`).
3. **Read `design/arch/facades/{crate}.md`** — the as-designed public surface for your crate. `/dev` implements against it (don't broaden silently). `/review` checks change sets against it (drift in either direction is a finding). `/design` cites it as the contract its design intent must keep current with.
4. **Read `crates/{crate}/CLAUDE.md`** (or `src/CLAUDE.md` for the Binary surface) — local conventions, API gotchas, data structures specific to the crate. The voice of the code.
5. **Read in-flight FIXMEs targeting your role for this crate** — `grep -l 'target: /<your-skill>' design/arch/fixmes/*.md` and check `refers_to:` for crate-relevance.
6. **Read `design/{crate}/{crate}.md`** when it exists (per-crate design overview, owned by `/design`). M2 authors these; until then, design intent lives in subordinate docs under `design/{crate}/` or in the bounded-context statement.
7. **Read the most recent crate audit `audits/{crate}-*.md`** when present, plus the paired `{crate}-*-current-state.{mmd,svg}` and `{crate}-*-target-state.{mmd,svg}` diagrams. **Audits are point-in-time opinions, not ongoing ground truth** (per Sprint 63 substance-scoping §1.5; each audit file carries an explicit supersession note). Read the audit's *current-state* sections as historical observation of the codebase at the audit date — useful context for understanding how the crate got to where it is. Read the *target-direction* sections as the auditor's recommendation at that time, superseded where Decisions 38–42 (or any later canonical updates) have moved the architecture since. `/review` is the continuous-audit role going forward; if the audit and the current canonical set (overview, principles, BCs, facades, decisions) disagree on what the crate should become, the canonical set wins. (`audits/` files are off the project root, not `sketch/audits/` — different concerns.)

## Narrow-deployment rule

One crate per invocation. The triad does **not** span crates within a single invocation. If implementation, design refinement, or review surfaces a question that crosses the bounded context, file a FIXME `target: /arch` (cross-crate interface or public-API question) or `target: /design` (per-crate design intent in the *other* crate should evolve) — do not edit beyond your bounded context.

The narrow-deployment rule is the design choice that lets generic skill defs carry per-crate weight. Specialization lives in `design/arch/bounded-contexts.md`, `design/arch/facades/{crate}.md`, `design/{crate}/{crate}.md`, and `crates/{crate}/CLAUDE.md` — the skill def is the process; the design docs are the specialization vector; the `CLAUDE.md` is the code's voice (per METHOD_PROPOSED §14.1 three-way content split).

## FIXME protocol

FIXMEs are files in `design/arch/fixmes/NNNN-name.md` — one file per issue. The register relocated from `sprints/fixmes/` to `design/arch/fixmes/` in Sprint 64 (Step 0 — register migration). Pre-S63 inline `FIXME(/skill)` comments were swept into the register in the same migration; new inline FIXMEs should not be authored.

**Filing**: scan `design/arch/fixmes/` for max existing number; use `max + 1` zero-padded to 4 digits. Frontmatter:

```markdown
---
number: NNNN
target: /skill
filed_by: /your-skill
filed_at: YYYY-MM-DD
sprint_filed: <sprint number>
refers_to: <path or symbol the FIXME concerns>
status: open
---

# Short description
## Issue
## Proposed resolution
## Context
```

**Lifecycle**: filing skill creates → owning skill reads at next wave gate or sprint Phase 1 → owning skill resolves (incorporates change into owned files) → owning skill `git rm`s the file → commit names what was resolved. Only the targeted skill deletes.

**Deferral**: if the owning skill cannot resolve in-sprint, set `status: deferred`, add rationale, name target sprint. File remains in place; `/sprint` carries it into next-sprint scope candidacy. 2× escalation per METHOD_PROPOSED §7.2: items deferred twice ship in the current sprint or require explicit user sign-off for a third deferral.

**Triad targets**:
- `target: /dev` — implementation work needed (new function, bug fix, refactor inside a crate).
- `target: /design` — per-crate design intent should evolve (the bounded-context statement or the design doc is wrong/incomplete).
- `target: /review` — a change set needs review attention (rare; usually `/review` is invoked directly per wave).

**Cross-skill targets the triad files**:
- `target: /arch` — cross-crate interface change, public-API extension, decision-log entry needed, facade-spec change.
- `target: /spec` — spec ambiguity or needed clarification surfaced during work.
- `target: /qa` — test coverage gap (failing test should exist for some spec requirement; integration test missing).
- `target: /sprint` — scope arbitration; carry-decision question.

## Git discipline

The working tree is shared across the session and across other agents. Discarding uncommitted work destroys review-before-enact visibility and may eliminate other skills' in-flight changes.

- **Forbidden**: `git stash drop`, `git stash clear`, `git reset --hard`, `git checkout --`, `git restore`, `git clean -f`, `git clean -fd`, branch switches that overwrite unstaged changes.
- **Permitted**: `git stash` + `git stash pop` *only if* the pop completes cleanly. If the pop conflicts, resolve or STOP and report — never discard the stash.
- **Commits**: only when the user explicitly asks. Sprint close is the canonical commit moment (`/sprint` orchestrates; user approves).

See `memory/feedback_no_git_stash_agents.md` for the incident that motivated this rule.

## Testing ownership

Per METHOD_PROPOSED §3.1 + §8.1:

- **Unit tests** — `#[cfg(test)] mod tests` within each crate. Owned by **`/dev`** (narrow per crate). Written alongside the implementation in the same wave; testing is part of `/dev`'s release gate.
- **Integration tests** — `tests/` at the project root. Owned by **`/qa`**. Spec-traceable via `// spec:` comments. `/qa` writes for the full spec surface in scope, not just what the implementation covers; failing-not-ignored.
- **Test runner**: `cargo nextest run` always (alias `cargo nt`). Never background. 30-second expected wall-time for the full suite — kill if longer and investigate. One agent runs tests at a time across the session.

`/dev` does NOT delegate unit tests to `/qa`. `/qa` does NOT write unit tests inside other crates.

See `memory/feedback_unit_tests_with_dev.md` and `memory/feedback_test_serialization.md`.

## Agent discipline

When invoked as a subagent or when spawning further subagents:

- **One skill per agent.** Never combine roles in one prompt. Spawning `/dev` AND `/review` in the same agent muddies findings ownership.
- **No worktree isolation** — known broken on this project (sketch vs reimplementation confusion).
- **Cargo discipline for `/dev` invocations** — see `.claude/commands/dev.md` §Release gate for the canonical procedure (cargo check / nextest / clippy zero-warning before declaring work complete).
- **Crate name in scope** — every spawn names the crate explicitly. "Work on the frontend" is ambiguous; "narrow to `cranelisp-frontend`" is not.

## Architectural principles

The 13 principles in `design/arch/principles/NN-*.md` (each auto-imported individually alongside this file in the triad skill defs) are the standard. `/design` designs against them; `/dev` implements against them; `/review` checks change sets against them. Cite by name when applying. Principles evolve only at sprint close (`/arch` Phase 7 review). The index at `design/arch/principles.md` lists titles for reference; the per-file bodies are the canonical content.

## Cross-references

- Methodology: `sprints/METHOD_PROPOSED.md` (target methodology — soon-to-be `METHOD.md` after M12).
- Architectural authority: `.claude/commands/arch.md` and `design/arch/`.
- Per-crate bounded contexts: `design/arch/bounded-contexts.md`.
- Per-crate facade specs: `design/arch/facades/{crate}.md`.
- Per-crate design: `design/{crate}/{crate}.md` (owned by `/design`; authored on first invocation per crate, refined on every subsequent invocation; M2 is the initial sweep across all 6 surfaces).
- Per-crate code conventions: `crates/{crate}/CLAUDE.md` or `src/CLAUDE.md`.
