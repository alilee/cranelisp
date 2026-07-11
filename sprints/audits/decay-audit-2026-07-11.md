# CLAUDE.md & Memory Decay Audit — 2026-07-11 (pre-S108)

> **Owner**: `/sprint`. Point-in-time audit record — input to the decay reset
> scheduled in `sprints/artefacts.md` §II.9 / increment F. Every finding below
> was verified against the working tree at commit `456a433d` (post-S107);
> none is suspicion. Resolved on execution: each reset dispatch consumes its
> file's section here as the work-list.

## Roll-up

| File | Verdict | Reset owner (target-state skill) | Headline decay |
|---|---|---|---|
| `CLAUDE.md` (root) | REWRITE | `/sprint` + user (increment A) | Skill table lists 5 retired skills, omits `/design` `/dev`; dead refs (`pipeline-v4*.md`, `design/arch/roadmap.md`, `memory/*` paths); ring model stated as active then retired in the same file; METHOD §3.3 protocol duplicated wholesale |
| `tests/CLAUDE.md` | REWRITE | `/qa` + `/testing` | "25 e2e files" vs 82 on disk; `tests/legacy/` described as populated, holds 0 `.rs`; coverage commands name deleted `ring*` binaries; coverage table row for the dissolved `cranelisp-runtime`; Sprint-21 baseline numbers; 6 dead `memory/*` refs; duplicated limitation paragraph |
| `spec/CLAUDE.md` | REWRITE | `/spec` | Half the file is a frozen Sprint 0–2 session log; sketch-oracle arbitration workflow (sketch retired, semantics frozen); inline-FIXME protocol (superseded S63); 16-file count vs 17 |
| `stdlib/CLAUDE.md` | REWRITE | `/stdlib` | FIVE stacked "Current State" sections (S91/S87/S86/S82/S81), newest 16 sprints behind S107; stale IO-trampoline/DLL blockers (landed); ring language; Sprint-14/17 pipeline-change log; module inventory duplicating `plan-stdlib.md` |
| `exemplar/CLAUDE.md` | REWRITE | `/port` | NINE stacked "Current State" sections (S103…S86); parallel-search/0408 story retold five times; keep Design Decisions/Conventions/Tests sections |
| `design/CLAUDE.md` | REWRITE | `/arch` | Ownership table maps 4 retired skills; misses 5 of 11 subdirs; dead refs (`design/reimplementation.md`, `arch/architecture.md`, `arch/roadmap.md`, `sketch/docs/`); ring-model roadmap; frozen Phase-B checklist |
| `design/review/CLAUDE.md` | REWRITE | `/review` | Built on `sketch/audits/` (does not exist) as "primary input"; ring checklists as review structure; retired-skill workflow; dead `design/arch/roadmap.md` + `tests/plan/strategy.md` refs |
| `src/CLAUDE.md` | TRIM | `/dev` (narrow `src/`) | Keep conventions (error handling, structure, naming, heap access, dep graph); drop ~half: per-sprint wave narratives (S66→S106), in-flight regression notes; 2 dead facade paths (`facades/int.md`, `facades/intrinsics.md` → only `*-audit-s69.md` exist); reconcile ~9s vs ~60s suite figures |
| `design/arch/CLAUDE.md` | TRIM | `/arch` | `METHOD_PROPOSED.md` cited as current methodology (:5,:89 — live METHOD.md supersedes); dead `facades/{crate}.md` cross-ref + self-contradictory "int still carries a facade" (:132 vs :15); dead `sketch/audits`/`sketch/src` refs; ~1500-word narrative cells in the canonical-docs table belong in the named docs |
| `crates/cranelisp-typecheck/CLAUDE.md` | TRIM | `/dev` + `/design` | Content current and correct; altitude problem — sprint-stamped design rationale (cross-module mono, ctor dual-facet) belongs in `design/typecheck/`; keep terse invariants + code-site pointers |
| `design/frontend/CLAUDE.md` | TRIM | `/design` (narrow) | Retired-skill ownership line; empty-`sketch/docs` ref; "per-ring evolution" |
| `design/backend/CLAUDE.md` | TRIM | `/design` (narrow) | Same three items |
| `design/typecheck/CLAUDE.md` | TRIM | `/design` (narrow) | Same three items |
| `design/platform/CLAUDE.md` | TRIM | `/design` (narrow) | Same three items |
| `repl/CLAUDE.md` | TRIM (two phrases) | `/repl` | "ring-aware" spec tagging (axis retired S64); "Layer 4 (E2E)" (four-layer pyramid retired S64 → two tiers) |
| `design/arch/principles/CLAUDE.md` | KEEP | — | Clean; triad import-block discipline accurate |
| `design/int/CLAUDE.md` | KEEP | — | Model example: current (S97–S102), distinguishes retired `/int` skill from live int bounded context, all refs resolve |
| `design/intrinsics/CLAUDE.md` | KEEP | — | Clean; all refs resolve |
| `repl/demos/CLAUDE.md` | KEEP | — | Verified against disk (10 demos, archive, player); practices the current-state discipline it preaches |
| `user/CLAUDE.md` | KEEP | — | Doc-set table matches disk exactly; honest authored-vs-pending status |
| `sprints/METHOD.md` §Cross-references | KEEP | — | `METHOD_OLD.md`/`METHOD_PROPOSED.md` exist and are honestly labelled predecessor/draft |

Also decayed, outside the CLAUDE.md set: `.claude/commands/design.md:80` and
`review.md:44` cite `METHOD_PROPOSED` as if current (fix rides increment A's
command work); `tests/plan/baseline.md` still exists beside its rename
`ledger.md`.

## Cross-cutting decay patterns (most → least pervasive)

1. **Retired-skill ownership** — every `design/*/CLAUDE.md` except
   int/intrinsics/principles names `/frontend` `/backend` `/typecheck`
   `/platform` as owner; the triad (`/design` `/dev` `/review`) replaced them.
2. **References into the deleted `sketch/`** — `sketch/docs/`,
   `sketch/audits/`, `sketch/src/` cited as live in design/, review/, spec/
   files. Verified: `git ls-files sketch` = 0; on disk only 4 untracked
   droppings (`.DS_Store`, `.cranelisp_history`) in empty dirs — remove the
   residue (increment E).
3. **Ring-model vocabulary** (axis retired S64) — frontend/backend/typecheck/
   platform/review/stdlib/repl CLAUDE.md files + root.
4. **Stacked per-sprint "Current State" logs** — stdlib (5×), exemplar (9×),
   src (interleaved), spec (Sprint 0–2 session log). CLAUDE.md files are
   current-state memories, not changelogs: ONE current-state section,
   consolidated at sprint close; history lives in `sprints/archive/`.
5. **Dead `memory/*` path citations** — root CLAUDE.md (3) + tests/CLAUDE.md
   (6) cite `memory/...` paths that exist only in the per-machine harness
   store (`~/.claude/projects/-home-alilee-cranelisp/memory/`) — and ONE
   (`feedback_failing_not_ignored.md`, root `CLAUDE.md` + `tests/plan/ledger.md`)
   is absent even there. Reset rule: state the rule inline in the canonical
   doc; do not cite harness-store paths from repo docs.
6. **Stale counts** — 15 skills (17 command files, 12 live), 16 spec files
   (17), 25 e2e files (82), Sprint-21 test baselines, `tests/legacy/`
   described as populated (empty).

## Harness memory store (live: `~/.claude/projects/-home-alilee-cranelisp/memory/`, 21 files)

Maintained by the assistant, per-machine, non-normative (METHOD §3.5:
durable content migrates to canonical docs, memory retires).

| Verdict | Files |
|---|---|
| **RETIRED now** (content verbatim in canonical docs, no by-name citations) | `s84-concrete-types-ambiguity-ruling.md` (→ `spec/03-types.md` §3.11, implemented + tested), `feedback_dev_strategy_derived_unit_scenarios.md` (→ METHOD §2.2 "Implementation-strategy unit scenarios"; its FIXME 0494 closed) |
| **UPDATED now** | `linux-vm-baseline.md` (S80 pass/fail counts stripped — `tests/plan/ledger.md` is the live baseline; toolchain recipe kept), `introspection-repl-only-principle.md` (implementation landed — `session_v4.rs` `introspection: Option<DashMap<…>>`; aged line-refs stripped, principle kept pending a `design/arch/` home) |
| **Retire when `sprints/artefacts.md` ratifies** | `feedback_spec_scribe_user_arbiter.md` (→ §II.1/§I.2), `feedback_frame_recurring_failure_by_symptom.md` (→ §II.4 trigger 1) |
| **Load-bearing — retire only after editing the citing doc** | `feedback_unit_test_per_fix.md` (cited root CLAUDE.md; content verbatim in METHOD §2.2), `annotation-reader-macro-binds-following-form.md` (cited `design/int/session-persistence.md:415`; semantics now scribed in spec §§1.4.5/2.3.8/3.11/4.9) |
| **KEEP** (live, verified, not canonical anywhere) | `workflow-commit-to-main-no-branches.md`, `agent-prelude-awareness-via-harvest-not-primer.md`, `mermaid-svg-render-setup.md` (verified `~/mmdc-run/` exists), `feedback_design_rulings_prose_review.md`, `feedback_agent_liveness_not_transcript.md`, `feedback_verify_fix_not_symptom_absence.md`, `feedback_investigate_suspected_dual_path.md`, `feedback_no_defer_for_size_decompose_evidence_gated.md`, `feedback_measure_orders_of_magnitude_not_precision.md`, `feedback_review_root_cause_and_duplication.md`, `feedback_no_fixme_with_failing_test.md`, `feedback_close_fixmes_each_sprint.md`, `feedback_actors_functions_before_synthesis.md` (last three are METHOD-migration candidates — the "drain all actionable FIXMEs", "no companion FIXME for a failing test", and actors-before-synthesis rules are not yet fully canonical) |

## Stale macOS store (`.claude/projects/-Users-alilee-Projects-nosync-rust-cranelisp/memory/`, in-repo working tree)

All four files obsolete: `feedback_no_premature_perf.md` (covered by live
dual-path memory; the v1 batch path it warns about no longer exists),
`feedback_test_timeout.md` (actively wrong — claims seconds-scale suite; warm
suite is ~60s/1657 tests), `project_ring5.md` (ring model dead),
`session_restructure.md` (S49 restructure long landed; cited design doc gone).
**Verdict: delete the whole directory** — scheduled increment E, alongside the
13 stale macOS-path permission lines in `.claude/settings.local.json` and the
`sketch/` droppings.
