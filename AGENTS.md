# Cranelisp

## First steps

Codex loads this root file as the repository-wide guidance. In directories that
do not contain an `AGENTS.md`, `.codex/config.toml` makes the local `CLAUDE.md`
the fallback project guidance. Before changing files in a directory, read and
follow the applicable local guidance. More-specific guidance overrides this
file for files in its scope.

## Project layout

| Directory | Purpose |
|---|---|
| `spec/` | Language specification — owned by `$spec` (scribe; the user arbitrates semantics) |
| `design/` | Architecture and per-crate implementation design — `design/arch/` owned by `$arch`, `design/{crate}/` by `$design` |
| `src/` | Compiler binary crate — pipeline, REPL, CLI, session |
| `crates/` | Bounded-context library crates (types, frontend, typecheck, backend, primitives, intrinsics, platform, exe-bundle) |
| `user/` | User-facing documentation — owned by `$docs` |
| `stdlib/` | Standard library in Cranelisp — owned by `$stdlib` |
| `examples/` | Learning-sequence examples — owned by `$examples` |
| `exemplar/` | Showcase project (Sudoku Solver) — owned by `$port` |
| `repl/` | REPL experience spec, demos, harness — owned by `$repl` |
| `tests/` | E2e suite — strategy/plan owned by `$qa`, test sources by `$testing` |
| `audits/` | Whole-context audit assessments — owned by `$audit` |
| `sprints/` | Delivery coordination — method, roadmap, current sprint, archive — owned by `$sprint` |

## Sketch oracle (retired)

The prototype compiler that lived in `sketch/` was deleted at the close of
Sprint 87. Language semantics are frozen, and the reimplementation's references
in `design/`, `audits/`, and `spec/` supersede it. Recover it from git history
only when an ambiguity genuinely requires the historical oracle.

Do not copy the sketch's pipeline structure. Its duplicated `TopLevel` and
`ReplInput` pipelines were defective; the v4 pipeline was designed
independently. See `design/arch/archive/pipeline-convergence-review.md`.

## Pipeline

The v4 scheduler-driven pipeline is the only pipeline. `CompilerSession` in
`src/session_v4.rs` is the unified session type. `main.rs` uses one code path
for Run, Link, and REPL; divergence among REPL, `--run`, and `--link` is always
a defect. See `design/arch/overview.md` and `design/int/CLAUDE.md`.

## Skills

Invoke the 14 repository-local Codex skills by short name. The user may invoke
one explicitly with `$name`; a matching request may also trigger it implicitly.
Roles, categories, and phase participation are normative in
`sprints/METHOD.md` §1. Model and effort names in Claude-oriented documents are
advisory role allocations, not Codex model identifiers.

| Skill | Role |
|---|---|
| `$spec` | Language Specification Scribe — owns `spec/`; records settled semantics and brings every open normative question to the user |
| `$arch` | Compiler Architect — owns `design/arch/` and `crates/cranelisp-types/`; principles, bounded contexts, public-API approvals |
| `$qa` | QA Authority — strategy, risk, coverage, traceability, defect attribution, and cross-crate triage; owns `tests/plan/` |
| `$testing` | Test Developer — e2e tests, repro isolation and reduction, and `// defect:` notation; owns test sources under `tests/` |
| `$audit` | Whole-Context Auditor — rolling per-sprint assessment of one bounded context; owns `audits/` |
| `$design` | Per-crate designer — narrow-deployed to one crate; owns `design/{crate}/` |
| `$dev` | Per-crate implementer — narrow-deployed; code and unit tests |
| `$review` | Per-crate reviewer — narrow-deployed change-set review against design intent |
| `$sprint` | Sprint Manager — increments, waves, gates, and dispatch; owns `sprints/` |
| `$stdlib` | Standard Library Developer — owns `stdlib/` |
| `$examples` | Example Developer — owns `examples/` |
| `$docs` | Documentation Owner — owns `user/` |
| `$repl` | REPL Experience Developer — owns `repl/` |
| `$port` | Exemplar Project Developer — owns `exemplar/` |

The former frontend, typecheck, backend, int, and platform roles are retired and
collapsed into narrow `$dev` deployment.

## Agent coordination

Codex sub-agents may perform read-only searches, surveys, or independent design
analysis in parallel. Source-touching work must be serial: worktree isolation is
broken and all agents share the same tree. Never delegate simultaneous edits.
Only the agent that owns source changes runs tests, and test runs must not
overlap. A skill may delegate only when the task and current Codex environment
permit it; delegation does not relax ownership or verification rules.

## Delivery

Phases A–G are complete; the project is in Phase H (release compiler). Sprint is
the sole scheduling axis. Consult:

- `sprints/METHOD.md` for the delivery method and FIXME protocol.
- `sprints/ROADMAP.md` for progress.
- `sprints/SPRINT.md` for the active plan, when present.
- `sprints/artefacts.md` for agent artefacts, escalation, and audit cycle.
- `sprints/reimplementation.md` only as historical strategy.

`$arch` is the final arbiter of cross-crate design. `$sprint` orchestrates. The
user approves scope, sprint close, and all language-normative questions.

## Findings and defects

User-proxy skills (`$stdlib`, `$examples`, `$docs`, `$port`, `$repl`) file
usability findings as numbered FIXME files in `design/arch/fixmes/`.

A compiler defect is not closed until `$testing` has committed a narrow,
failing-not-ignored repro carrying a `// spec:` annotation. Reproduced defects
remain permanently in the suite. Make every complete or partial reduction a
small committed test.

Cross-skill handoff requires a minimal repro according to `tests/CLAUDE.md`.
Before `$sprint` delegates cross-skill triage, the discovering skill must create
one or request `$testing`. Escalate contested attribution to `$qa`.

## Cross-skill changes

A skill must not silently edit another skill's owned document. File
`design/arch/fixmes/NNNN-short-name.md`; the owner evaluates it, applies any
change in its own files, and deletes the FIXME. Filing is the sole ownership
exception. Follow `sprints/METHOD.md` §3.3.

Do not author new inline `FIXME(/skill)` comments; they are the retired protocol.
Before `$sprint` advances a wave, it must resolve or explicitly defer every open
FIXME targeting a skill in that wave.

Every skill plan ends with a **Next skills** section. When a sprint is active,
use `sprints/SPRINT.md` for dependencies; otherwise use `sprints/ROADMAP.md`.

## Design principles

- Keep the REPL self-documenting. Every valid symbol and expression should
  produce useful type, value, or usage feedback.
- Follow Clojure standard-library naming and design where possible.
- Keep the prelude optional; the core language must work without it.
- Keep tests and examples independent of `stdlib/`. Only `exemplar/` and the
  production binary may depend on the standard library.

## Testing

- Always use `cargo nextest run --no-fail-fast`, or the `cargo nt` alias,
  instead of `cargo test`.
- Never run tests in the background. A full run should finish within roughly
  three minutes including a rebuild; stop and investigate longer runs.
- Only one agent runs tests, and only one source-editing agent works at a time.
- Every fix requires a unit test. Before implementation, assess whether an e2e
  test is also warranted, write failing tests first, and land tests with the fix.
- The suite intentionally contains failing-not-ignored defect guards. A RED is
  a regression only when it does not trace to a known open defect. Never hide a
  known defect with `#[ignore]`.

## Git and remote

- `origin` is `https://github.com/alilee/cranelisp` and has orphan history; an
  explicitly requested push uses `git push --force origin main`.
- Never push without explicit user authorization.
- Commit directly to `main`; do not create branches.
- Never use `git stash drop`, `git stash clear`, `git reset --hard`,
  `git checkout --`, `git restore`, `git clean -f`, or `git clean -fd`.

## Requirements and test traceability

Every spec requirement must trace to a test, and every test must carry a
`// spec:` comment tracing to a requirement. Spec-side coverage annotations are
`[Tested ...]`, `[Tested+Neg ...]`, `[Tested]`, `[Tested+Neg]`, `[S{M}]`, and
`[S{M} — tests/file::test_name IGNORED]`. `[Done]` is retired.

`$testing` adds test-side comments. `$qa` owns the coverage-annotation band in
`spec/*.md` and `repl/spec.md` and may edit that band directly without a FIXME;
requirement prose remains owner-gated.

See `sprints/reimplementation.md` §Risk Analysis for known-issue disposition.
