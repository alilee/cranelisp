# Sprint 120 QA evidence delta — shared-role integration proof

**Status:** Wave 3 plan of record, revised at the Wave 4 review triage (§7);
§4 is the Wave 6 final adequacy judgment on the 2026-08-30 working tree —
superseded for compiler state by the accepted `cbb3be9e` (see the §4 scope
note), and reconciled for repository-gate state at Phase 6b (§4.5,
2026-08-31: W6, C8 and W7 landed, the Codex review launcher retired). §4.6 is
the Phase 6b final evidence-adequacy judgment (2026-08-31).
**Authority:** `qa`. Scope is `sprints/SPRINT.md` §Scope and acceptance; this
document allocates evidence and states what existing evidence proves. It does
not implement anything.
**Measured on:** working tree at `0ccacf0b` plus the uncommitted Wave 0–2
changes, 2026-08-30.

## 1. ACT-0946 measurement

The checker was run in-process with `DOC_GLOBS` / `SOURCE_ROOTS` widened
against the working tree; `new` counts findings absent from the 610-entry
baseline. `--corpus live` throughout unless stated.

| Config | Docs | Citations | New findings | Where |
|---|---|---|---|---|
| A. current (control) | 434 | 7,507 | 0 | — |
| B. `sprints/` as root only | 434 | 7,739 | 4 | `design/arch/legacy/` ×4 (citing `sprints/triad-shared.md`, which does not exist, and a `fixmes/0001..0009` range) |
| C. `sprints/**/*.md` as corpus only | 443 | 7,598 | 8 | `ROADMAP.md` ×2, `reimplementation.md` ×5, dated decay audit ×1 |
| D. both | 443 | 7,975 | 16 | B + C + `ACT-0946` ×2 (its own request prose), decay audit ×2 |
| E. D + `.claude/` `.agents/` roots + their `*.md` as corpus | 483 | 8,083 | 34 | D + 18 citations to `.claude/commands/*.md`; **0 from `.claude/` or `.agents/` documents** |
| F. D with `--corpus all` | 710 | 14,017 | 1,319 | 707 from `sprints/archive/` — the live filter is load-bearing |
| J. D + `design/ spec/ audits/ user/` as roots (informational) | 443 | 10,121 | 214 | doc→doc citations, 165 from `design/`; out of ACT-0946's scope → ACT-0950 |

Probe (scratch document under `target/`, citing `sprints/<absent>.md`,
`src/<absent>.rs` and `sprints/METHOD.md`): current roots report the `src/`
fault only; with `sprints/` a root both faults are reported and the real path
verifies. Wall time 4.4 s for A; E is the same order.

Ruling: ACT-0946 §Ruling items 1–7, resolved and deleted at Wave 6.
**Provenance correction (2026-08-31, `qa`):** the ruled text is *not* in git
history — the §Ruling section was authored and then deleted in the uncommitted
working tree, so its verbatim prose is unrecoverable. Git holds only the
pre-ruling request — the deleted action
was at `0ccacf0b:sprints/actions/ACT-0946-citation-instrument-corpus-gap.md`.
Do not
reconstruct the ruling prose; the surviving durable carriers are authoritative:
items 1–4, 6 and 7 are carried by `scripts/verify-citations.py`
itself — `DOC_GLOBS`, `CORPUS_EXCLUDED_ROOTS`, `SOURCE_ROOTS`, `SYMBOL_ROOTS`,
`HISTORICAL_RE`, `LIFECYCLE_PATHS` and the docstring's "does not catch" list —
and item 5, the widening-absorption rule for the ratchet, is condition C4 below
and the exception stated in `scripts/citation-drift-baseline.txt`'s header.
This document's "§Ruling N" citations name the item numbering as reproduced
here, which is that numbering's surviving record.

## 2. Evidence delta

### D-1 — citation instrument widening (ACT-0946)

**Implementer:** `test` — the executing gate and its fence are
`tests/citation_drift.rs`, and this is independent solution evidence; `test`
revises that file's own "not `/testing`'s to edit" note when it lands the
script change. `sprint` confirms, since `scripts/verify-citations.py` has no
declared owner (it landed in one commit with the gate, `162bedd9`). `qa` keeps
the corpus policy and the ratchet property.

| Condition | Plausible wrong outcome it discriminates | Layer | Extends |
|---|---|---|---|
| C1 corpus += `sprints/**/*.md`, `.claude/agents/*.md`, `.github/agents/*.md`, `.github/copilot-instructions.md`; corpus −= `.agents/**` | a scheduling record or host adapter cites a path that does not exist and nothing reports it | existing gate on every `cargo nextest run` | `DOC_GLOBS`, `collect_docs` |
| C2 roots += `sprints/`, `.claude/`, `.agents/` for PATH/LINE; `.rs` under `.claude/` and `.agents/` stay out of the bare-filename symbol set | a citation to a deleted `sprints/` or `.claude/commands/` file, or to a missing role contract, passes silently; or the overseer's `lib.rs` widens bare `lib.rs::sym` resolution | same | `SOURCE_ROOTS`, `_source_files` (review point, no plant) |
| C3 `HISTORICAL_RE` recognises `-YYYY-MM-DD` | a dated record is graded live and its moment-accurate citations become findings; or (today) 26 dated-audit entries sit in the baseline as if live | same | `HISTORICAL_RE` |
| C4 **standing rule for any corpus or root widening** (ACT-0946 §Ruling 5): the baseline is regenerated once with `--write-baseline`, in the widening change-set and nowhere else, and `qa` verifies the diff before accepting it — (i) every added entry has its citing document or its cited target inside the newly admitted scope, so nothing from the old scope enters; (ii) every removed entry is a named repair or left scope by classification; (iii) the old-scope entry count does not rise. Enrolled entries stay debts of the citing document's owner. The next widening is ACT-0950's, if ruled | a widening quietly enrols old-scope drift or hand-added entries | change-set review (`qa`) | `scripts/citation-drift-baseline.txt` |
| C5 fence: a planted `sprints/<absent>.md` and a planted `.claude/commands/<absent>.md` — real-looking names in the scratch text, no placeholder characters, no exemption markers — each → exit 1, output names `PATH` and the planted path; clean document citing `sprints/METHOD.md`, `.claude/agents/qa.md`, `.agents/skills/qa/SKILL.md` → exit 0, `3 paths` verified, `0 exempt` | the widening never fires, or fires for the wrong reason | `tests/citation_drift.rs`, identical invocation to the gate | existing fence pattern (scratch under `target/`, pinned counters, no exemption markers in the plant prose) |
| C6 corpus membership: the script lists its live corpus (`--list-docs`, or a `documents` array under `--json`); a fence leg asserts `sprints/METHOD.md`, `.claude/agents/qa.md`, `.github/agents/qa.agent.md` and `.github/copilot-instructions.md` are members and `.agents/CLAUDE.md` and every `sprints/archive/` path are not | any of the four C1 globs is removed and the gate stays green — C5 cannot see this, because explicit documents bypass `DOC_GLOBS` (control: 431 documents, 0 findings, against 465); or `.agents/` prose re-enters the corpus | `tests/citation_drift.rs` | `collect_docs`; the leg is self-arming — presence and absence are asserted in one run, so a listing that reported everything or nothing fails |
| C7 lifecycle path: `sprints/SPRINT.md` is recognised as a citation, never verified against existence, never a finding (ACT-0946 §Ruling 6); fence: a scratch document citing only `sprints/SPRINT.md` → exit 0 in any phase, `1 citations (0 paths`, `1 exempt` (or a dedicated counter); the script docstring's "does not catch" list names the class | between sprints the live gate reports 174 `PATH` findings in 76 documents; mid-sprint a citation meaning a past sprint verifies against the current file | `tests/citation_drift.rs` | `check_document` ahead of the existence test; the counter is what separates "recognised and exempted" from "not recognised" |

C1–C7 landed and verified at Wave 6 (§4.1); ACT-0946 is resolved and deleted.
C4 on the final diff: 26 removed, all `audits/*-2026-06-14.md`; 21 added, every
one citing from `sprints/` or targeting `sprints/` or `.claude/`; 610 → 605.

Allocated at Wave 6 from audit finding F-6
(`audits/shared-role-integration-s120.md` §4); **landed at Phase 6b
(2026-08-31)** — see §4.5. Ruling (`qa`, 2026-08-30): the
`review/` directory pattern in `HISTORICAL_RE` is over-broad by one file class;
`design/review/CLAUDE.md` describes itself as live guidance and is live corpus.
The correction is a classification, as ruling item 4 was, not a suppression.

| Condition | Plausible wrong outcome it discriminates | Layer | Extends |
|---|---|---|---|
| C8 a standing `CLAUDE.md` under a `review/` directory is a live-corpus member — `design/review/CLAUDE.md` listed by `--list-docs` and asserted by the C6 leg — while the dated `design/review/sprint*` records stay excluded. Sequenced after `review` repairs that file's two citations of the retired `.claude/commands/review.md` (lines 24 and 43): the gate goes green by repair, never by enrolment. The other undated files in `design/review/` (`checklist.md`, `crate-quality.md`, `naming-convention-review.md`, the `ring*` checklists and reports) are not classified here — `review` states which are standing before `qa` admits any; admitting a directory without inspecting each file's lifecycle is the Wave 3 error ruling item 6 corrected | a live convention file routes a role to a retired mechanism and the widened instrument cannot see it, because a filter written for dated review records also swallows the directory's standing guidance | `tests/citation_drift.rs`, C6 leg | `HISTORICAL_RE`, `CORPUS_MEMBERS` |

Owner was `test` (pattern and leg), after `review` (content); both delivered
at Phase 6b. `review` repaired `design/review/CLAUDE.md` (no retired-mechanism
citation remains), `HISTORICAL_RE`'s `review/` clause now excepts that file,
and the C6 listing leg asserts its membership while the dated review records
stay excluded. The other undated `design/review/` files remain outside the
corpus until `review` classifies each one's lifecycle — that residual is
`review`'s (§6).

### D-2 — role-wiring gate

**Implementer:** `test`. One executing check under nextest, shape at the
implementer's discretion (pure Rust reading the files, or a stdlib-only python
under `scripts/` with a Rust consumer as the citation gate does). It takes a
root path so its fence can run it against a scratch copy under `target/`.

| Condition | Plausible wrong outcome |
|---|---|
| W1 R := role names from root `CLAUDE.md` §Roles table rows; R == names of `.claude/agents/*.md` == names of `.github/agents/*.agent.md`; for each `<r>`, `.agents/skills/<r>/SKILL.md` exists and `[roles.<r>]` is present in `.agents/skill-composition.toml` | a declared role lacks a contract, an adapter, or a composition entry; an adapter exists for an undeclared or retired role |
| W2 each `.claude/agents/<r>.md`: frontmatter `name: <r>`, non-empty `model:` and `effort:`, body cites `.agents/skills/<r>/SKILL.md`; each `.github/agents/<r>.agent.md`: `name: <r>`, body cites the same | an adapter names the wrong role, carries no allocation (the transport would then refuse at dispatch time, which is late), or points at the wrong contract |
| W3 every skill named in `skill-composition.toml` (`[support].skills`, `always`, `standing_documents`) has `.agents/skills/<s>/SKILL.md` | composed support is missing |
| W4 `.claude/settings.json` declares `SubagentStart` and `SubagentStop` command hooks naming `.agents/tools/subagent_telemetry.py`; that file and `.agents/tools/claude_role.py` exist; `.claude/skills` is a symlink resolving to `.agents/skills` | the shared hook is not wired; the transport is absent |
| W5 files `design/arch/principles/NN-*.md` == set cited by `design/arch/principles.md`, both directions; each file's frontmatter `number` == its `NN` | a Principle on disk is not in force, or the index names a Principle that does not exist |
| W6 (**open** — allocated at Wave 6 from audit finding F-3) for each role `sprints/METHOD.md` §1.1 names as reading the principles first — `arch`, `design`, `dev`, `review` — both host adapters cite `design/arch/principles.md`; plant: delete that paragraph from the copy's `.claude/agents/dev.md` → W6 names the file; the clean leg pins `4 first-read roles` | an adapter drops the first-read and nothing observes it. `design/arch/principles/CLAUDE.md` names "the adapter-inventory check" as that falsifier; W2 checks `name`, `model`, `effort` and the contract path only, so today the claim is asserted without an observing check |

Fence (one plant per condition, each on its own scratch copy, one clean run):
remove one adapter → W1 names the role; change one adapter's `name:` → W2 names
the file; remove `.agents/skills/quality-standards/` from the copy → W3 names
`quality-standards`; rewrite one event's hook command in the copy's
`.claude/settings.json` to a script that is not `subagent_telemetry.py` → W4
names that event; add a principle file without an index line → W5 names it. The
unmodified copy passes with the role, composed-skill and principle counts pinned
(`12 roles`, `2 composed skills`, `26 principles` today). W1–W5 and all five
plants landed at Wave 6; **W6 and its plant landed at Phase 6b (2026-08-31)**
— the script reads the obliged set out of `sprints/METHOD.md` §1.1 rather than
carrying a copy, the clean leg pins `4 first-read roles`, and the plant
(first-read paragraph deleted from a scratch copy's `.claude/agents/dev.md`)
fires naming the file. W4's plant is the hook-command match because that is
the only W4 branch with logic; the absent-file and symlink branches are
read-verified only, and the fresh-clone case (`settings.json` untracked) is
R1. With W6 measured, `arch`'s falsifier claim in
`design/arch/principles/CLAUDE.md` now names a check that exists and has been
shown to detect (audit R-2 closed).

**W7 (allocated at Phase 6b, 2026-08-31, owner `test`; landed and measured
the same day — the wiring gate pins `12 allocation pairs` and the plant
fires).** The Wave 3
form of this paragraph ruled the tier↔role mapping out of the gate: "asserting
`arch → fable` in a test would copy the declaration the test exists to check."
Repaired here: that rationale held while the allocation's only carriers were
prose, and it does not survive the governing user decision that the shared
package is definitive for role/model/effort and a hosted project must not
remap it. The shared `.agents/agents/<role>.md` frontmatter is the definitive
executable allocation (`.agents/CLAUDE.md` §Execution tiers) — a determinant
on disk. Comparing each consumer adapter's `model:` and `effort:` fields
against its shared carrier's, read from the carrier at check time, is
single-sourcing from the determinant, not copying a declaration: no role→tier
table appears in the script or the test. All twelve pairs match and the gate
now observes the equality continuously; per-host adapter copies are the shape
that drifted twice (S65, S76), and a primary-harness named dispatch reads the
consumer adapter, so a silent local remap would execute there (the transport
itself now reads model and effort from the shared carrier only).

| Condition | Plausible wrong outcome it discriminates | Layer | Extends |
|---|---|---|---|
| W7 for each declared role, `.claude/agents/<r>.md` frontmatter `model:` and `effort:` equal `.agents/agents/<r>.md`'s, read from the shared carrier at check time (Copilot adapters carry no allocation fields and are out of scope). Plant: change one allocation field in a scratch copy's consumer adapter → W7 names the role and both values; the clean leg pins `12 allocation pairs` so an empty comparison cannot pass vacuously | a consumer adapter silently remaps a role's model or effort away from the definitive shared allocation and every gate stays green | `scripts/verify-role-wiring.py` + a plant leg in `tests/role_wiring.rs` — maintenance check, same class as W1–W6 | the script's existing adapter walk and frontmatter reader |

W7 landed with its plant leg in `tests/role_wiring.rs`, the clean-leg pin, and
the repaired rationale in `scripts/verify-role-wiring.py`'s docstring (the
script is `test`'s per `sprints/METHOD.md` §3.1; verified 2026-08-31, gate
exit 0). What W7 cannot prove stands: the *executed* model and effort are the
dispatch row's, reviewed at Phase 7 with the dispatch log — W7 checks the
declared copy, not the execution.

Cost: one test file, sub-second runtime. Warrant: the sprint's goal names
objective wiring checks; per-host adapter copies (12 × 2) are the shape that
drifted twice (S65, S76); the package converges every sprint and can rename or
drop a role; and `design/arch/principles/CLAUDE.md` names "the
adapter-inventory check" as a falsifier that does not yet exist. W5 is
permanent rather than a Phase-7 memory item because a reconciliation that
depends on remembering is the failure state.

### Not allocated here (package-side; contribute at close, not acceptance-gating)

Most of this list was delivered by the integrated `.agents` delta and verified
against source 2026-08-31 (suites fresh at 20/20 and 10/10): interruption
closure is tested with precedence (provider error outranks a missing
transcript; interruption, exit 130, outranks a provider error → `abandoned`);
`dispatch_stats.py` partitions every dispatch into exactly one reported state
and counts `open` and `transcript_unavailable` rows on their own lines, so an
orphaned open row is visible from the summary; the unreachable package-adapter
fallback is deleted — `role_agent` refuses without a consumer-visible agent,
and a test proves the refusal fires despite a present package adapter; the
terminal classification order and the writer docstrings are repaired.

Still lacking test coverage in `.agents/tools/test_claude_role.py` — three
refusal branches of `claude_role.py` that exist in code but have never been
exercised against a planted fault: the missing-contract refusal (the fixture's
refusal case, `maintain-documents`, has a `SKILL.md` and refuses on the absent
consumer agent instead), the adapter-name-mismatch refusal (no case rewrites a
consumer adapter's `name:`), and the missing-`model` refusal (no case blanks
the shared carrier's allocation). Owner: the package bootstrap owner (`arch`,
Wave 0), via `CONSUMING.md` §Contributing.

## 3. What the existing evidence proves, and does not

| Evidence | Proves | Does not prove |
|---|---|---|
| 20 fake-provider cases (ran green 2026-08-31; 14 at Wave 6) | argv carries `--agent r --model M --effort E --permission-mode P`; brief verbatim on stdin and absent from argv/telemetry; open/close rows share one identity; provider failure closes `error` with status propagated; missing transcript closes `transcript_unavailable`; interruption (exit 130) closes `abandoned`, outranking a provider error, which outranks a missing transcript; refusals open no row, including with the consumer agent absent and a package adapter present; hook start/stop pair; reconciliation is session-scoped and idempotent | that the real CLI honours `--agent`/`--effort`; anything about cranelisp's twelve adapters; the three unexercised refusal branches (§2 "Not allocated here") |
| 10 dispatch-summary cases (green; 5 at Wave 6) | the reduction over synthetic rows; every dispatch in exactly one reported state, with `open` and `transcript_unavailable` counted on their own lines | the producers |
| live dispatches through the transport, closed rows: `arch` (`fable`/`xhigh` sent, `claude-fable-5` reported, 85 turns), `spec` (`opus[1m]`/`high` → `claude-opus-5[1m]`, 36 turns), `qa` ×2, `test` ×2, `review` ×2, `audit` — all `success` | end-to-end for 6 of 12 roles; the **consumer** allocation was selected — package defaults are `fable/high` and `opus/high`, and the rows carry `xhigh` and `[1m]` | the other six adapters (`design`, `dev`, `docs`, `training`, `ops`, `sprint`); that `--effort` was applied (the CLI does not echo it) |
| first `arch` attempt (sandbox timeout, exit 1) closed `transcript_unavailable` | a real failed dispatch closes | the interrupted path |
| hook probe, this wave: a haiku `Explore` subagent from the `qa` session produced an open row and a closed `success` row (`tool_uses: 1`, `turns: 2`, no `provider` field, session id matching) | `.claude/settings.json` hooks fire on both events in this checkout | that the wiring exists on a fresh clone (`settings.json` is untracked) |
| citation gate (`live_corpus_citations_resolve_against_source`; C5, C6, C7 fences) | live doc→source citations resolve modulo the ratchet, now including `sprints/`, `.claude/` and `.agents/` targets and the scheduling and host-adapter documents; the lifecycle path is counted and never verified | doc→doc citations (~214 stale today, ACT-0950); the undated `design/review/` files other than its `CLAUDE.md`, excluded until `review` classifies their lifecycle (C8 landed for the standing file, §4.5) |
| inventory searches this wave | 12/12 contracts, 12/12 Claude adapters (`name` matches, model/effort present), 12/12 Copilot adapters, 14 skill dirs, composition entries for all twelve, `.claude/skills → ../.agents/skills`, principles 26 ↔ 26, no `.claude/commands` reference in `.claude/`, `.github/`, root `CLAUDE.md`, `spec/`, `sprints/METHOD.md`, top-level `design/arch/*.md` | anything after today; they are observations, not a mechanism — D-2 is their permanent form |

## 4. Readiness verdict (Wave 6 working tree, 2026-08-30)

> **Scope note (2026-08-31, `qa`).** This section is a dated record of the
> 2026-08-30 tree — `0ccacf0b` plus the then-uncommitted host-alignment
> changes; "final working tree" meant final *for that judgment*, not for the
> sprint. Its compiler census — the empty compiler-source `git status`, the
> 5,692 / 20-failed run, and §4.2's carry of the two
> `nullary_arm_beside_boxed_arm_0917` REDs — is **superseded by `cbb3be9e`**
> (2026-08-31), the user-accepted FIXME 0917 backend correction, whose
> acceptance evidence (`sprints/SPRINT.md` §Acceptance, Waves 2–4) is the
> current record of compiler state. The dated figures below stand as history
> and are not restated. The Phase 6b exit runs a fresh full suite; that run,
> not this section, states the then-current failure set.

**Recommend acceptance now, with the close gates in §4.3.** Every gate this
plan named was re-executed on the final tree; no acceptance item rests on a
condition graded by inspection; and the one open blocker (R1) is a publication
act that needs the user's authorisation, not missing evidence.

### 4.1 Gates re-executed

| Gate | Command | Result |
|---|---|---|
| Repository gates | `cargo nextest run --test citation_drift --test role_wiring` | 7 passed, 0 failed, 4.4 s — C5, C6, C7 and the W1–W5 plants fire and clear |
| Citation instrument, live | `python3 scripts/verify-citations.py --corpus live --baseline scripts/citation-drift-baseline.txt` | 465 documents, 8,046 citations, 0 findings, 183 lifecycle (464 documents once ACT-0946 is deleted) |
| Corpus membership | `… --list-docs` | 9 `sprints/` members including `SPRINT.md` and the actions; 12 + 12 adapters; `copilot-instructions.md`; 0 `.agents/`, 0 `sprints/archive/`; 0 `design/review/` (C8) |
| Wiring gate, live | `python3 scripts/verify-role-wiring.py` | exit 0: 12 roles, 12 + 12 adapters, 2 composed skills, 26 principles |
| Package suites | `python3 -B .agents/tools/test_claude_role.py`; `…/test_dispatch_stats.py` | 14 OK; 5 OK; `__pycache__` ignored by the submodule's `.gitignore` |
| Telemetry lifecycle | `.local/subagents.jsonl`, last state per `agent_id` | 25 rows, 13 ids: 12 closed, 1 open — this `qa` dispatch (session `2eb155b6`). The failed first `arch` attempt is closed `transcript_unavailable` (exit 1, 178 s, 0 tokens) |
| Summary | `python3 .agents/tools/dispatch_stats.py --since 2026-08-30` | 11 runs — `arch`, `spec`, `qa` ×2, `test` ×2, `review` ×2, `audit`, `Explore` ×2 — no abandoned line; the failed `arch` row is omitted by the summary (§7 A) and is accounted from the row file above |
| Review-launcher preamble | `rg` over `scripts/codex-review.sh` — a dated row: that launcher and its schema were removed at Phase 6b (2026-08-31), when review moved to a primary-harness role subagent | empty on 2026-08-30; the then-preamble read root `CLAUDE.md`, METHOD §2.3, the `review` and `quality-standards` contracts and `design/arch/principles.md` |
| Baseline ratchet (C4) | `git diff -- scripts/citation-drift-baseline.txt` | −26, all `audits/*-2026-06-14.md`; +21 — seven FIXME `refers_to:`, five `design/arch/legacy/`, one `design/typecheck/`, three ROADMAP, five `reimplementation.md`; 610 → 605 |
| Compiler-source census | `git status --short -- src crates stdlib exemplar examples platforms benches Cargo.toml Cargo.lock` | empty. The only `tests/*.rs` changes are the two repository gates |
| Full suite | `cargo nextest run --no-fail-fast` | 5,692 run / 5,672 passed / 20 failed / 1 skipped, 251 s |

### 4.2 The 20 REDs

They are S119's close set name for name: `sprints/archive/sprint-119.md`
records 5,687 run / 20 failed at close, and `tests/plan/s119-test-plan.md`
enumerates all twenty — fifteen by name, five as `spec_field_accessor::{…}` ×3
and `nullary_arm_beside_boxed_arm_0917::{…}` ×2. Every one is a
compiler-behaviour test carrying a `// defect:` line (`launch_grid_corrupt`
carries the equivalent RED-on-HEAD header) with owner `/dev` and an open FIXME
on disk: 0903, 0907, 0913, 0916, 0917. The count is 5,687 + 5 repository-gate
cases = 5,692; the coordinator's 5,690 predates C6 and C7. **Attribution: not
caused by and not affecting this increment** — zero compiler-source changes,
no untraced RED, no regression. They are the next product sprint's Phase-1
scope (METHOD §2.2: scope a drawdown from a test run), outside this boundary.

### 4.3 Blockers and close gates

| # | State at Wave 6 | Owner | Close gate |
|---|---|---|---|
| R1 | **Open — the only blocker.** The pin `b856b8f2` is three local commits ahead of `origin/main` (`3bbc70a`, an ancestor — the push is a fast-forward) and its tree holds none of `tools/{claude_role,subagent_telemetry,test_claude_role}.py`; `.agents/{CLAUDE,CONSUMING}.md` and `.agents/.gitignore` are modified; `.claude/settings.json` is untracked; the consumer delta is 24 modified or deleted and 8 untracked paths. Precision (audit F-2): the twelve contracts and twenty-four adapters *are* committed at `HEAD` + pin — what is uncommitted is the dispatch path and the declaration, and the pin itself is unpublished (F-1). | `sprint`, with the user's push approval | §4.4 in order; then `git status --porcelain` empty in both trees, `git ls-files .claude/settings.json` non-empty, `git -C .agents ls-tree -r HEAD --name-only` listing `tools/claude_role.py`, and a fresh clone passing both python gates |
| R2 | Closed — verified at Wave 6 by `rg` and by reading the preamble (§4.1). Commits with R1. | — | none beyond R1 |
| R3 | Closed — the C6 membership leg and the C7 lifecycle leg are green in both delivery phases with controls; ACT-0946's completion lines are met and the action is deleted. | — | **Phase 7 live confirmation**: after `sprints/SPRINT.md` is archived, `python3 scripts/verify-citations.py --corpus live --baseline scripts/citation-drift-baseline.txt` still reports 0 findings with the `lifecycle` count unchanged |
| R4 | Closed — the W3 and W4 plants fire for the right reason and the clean leg pins `2 composed skills`. | — | none |

### 4.4 Publication order — after user acceptance

No step below is claimed as done, and the present checkpoint is not
reproducible anywhere but this machine until step 2 has happened.

1. **Package commit.** `git -C .agents add -A` and commit on the submodule's
   local `main` (three modified files, three new tools; `__pycache__` is
   ignored). Re-run `python3 -B .agents/tools/test_claude_role.py` and
   `test_dispatch_stats.py` from the committed tree; `git -C .agents status
   --short` empty.
2. **Publish — on the user's explicit approval.** `git -C .agents push origin
   main`, a fast-forward from `3bbc70a`. Verify `git -C .agents ls-remote origin
   refs/heads/main` returns the new commit. If the user elects to carry the
   package locally instead (`CONSUMING.md` §Contributing permits it), the
   acceptance record states that the proof is single-machine and step 4 is
   deferred to the converge that publishes.
3. **Consumer commit.** `git add .agents .claude/settings.json` plus the rest of
   the working tree; one commit on `main`. Verify `git ls-files
   .claude/settings.json` non-empty, `git ls-tree HEAD .agents` equal to the
   pushed commit, `git status --porcelain` empty.
4. **Fresh clone.** `git clone --recurse-submodules /home/alilee/cranelisp
   <scratch>` — the submodule resolves from the GitHub URL in `.gitmodules`,
   which is what proves step 2. In the clone: `python3
   scripts/verify-role-wiring.py` exit 0 with the five counts; `python3
   scripts/verify-citations.py --corpus live --baseline
   scripts/citation-drift-baseline.txt` 0 findings; `python3 -B
   .agents/tools/test_claude_role.py` 14 OK. A clone whose submodule URL is
   overridden to the local path proves the consumer side only.
5. **Phase 7.** Archive `sprints/SPRINT.md` to its numbered file under
   `sprints/archive/`; run the live checker again (R3's close gate); update
   `ROADMAP.md`; commit.
   Pushing cranelisp `main` is a separate explicit user request.

### 4.5 Phase 6b repository-gate state (2026-08-31)

The §4.1 table is a dated record of 2026-08-30; this subsection reconciles it
with the Phase 6b working tree. **The Phase 6b exit run — the fresh full suite
named in the §4 scope note — has not happened; nothing here claims it.** These
are the repository maintenance checks only, re-executed by `qa` on 2026-08-31:

- **Wiring gate:** `python3 scripts/verify-role-wiring.py` exit 0 — 12 roles,
  **4 first-read roles** (W6 landed with its plant; the 2026-08-30 row
  predates it), 12 + 12 adapters, **12 allocation pairs** (W7, landed later
  the same day), 2 composed skills, 26 principles.
- **Citation gate:** `python3 scripts/verify-citations.py --corpus live
  --baseline scripts/citation-drift-baseline.txt` — 466 documents (465 at
  Wave 6; `design/review/CLAUDE.md` joined per C8), 0 findings after this
  document's own two references to the removed Codex launcher were repaired in
  this revision. Baseline entries untouched; 605 entries.
- **Ownership (§7 C-i):** resolved — `sprints/METHOD.md` §3.1 now declares
  `scripts/verify-*.py` → `test`, `scripts/citation-drift-baseline.txt` →
  `qa`, and the host adapters plus `.claude/settings.json` → `sprint`. The
  recommended row for the removed `scripts/codex-review.sh` → `review` is
  moot: that launcher and its removed `scripts/codex-review-schema.json` left
  the tree at Phase 6b.
- **Gate-file header (§6 `test` items):** `tests/citation_drift.rs` now cites
  the script docstring as the single condition carrier, states the METHOD
  §3.1 ownership, and no longer cites the deleted ACT-0946 by path.
- **Open under this plan:** the undated `design/review/` lifecycle
  classification (owner `review`); ACT-0950 (excluded from this increment);
  R1 and the §4.4 publication order (unchanged, user-gated). W7 closed —
  landed and measured 2026-08-31 (§2 D-2): the wiring gate reports
  `12 allocation pairs` and its plant fires.

Classification unchanged (`tests/plan/PLAN.md` §"Repository gates"): both
gates are **maintenance checks** — they protect record currency and wiring
declarations, and are never compiler acceptance evidence.

### 4.6 Phase 6b final evidence-adequacy judgment (2026-08-31)

**Adequate. No blocking or required finding remains.** Made on the Phase 6b
working tree after the independent review (root `cbb3be9e` → tree, `.agents`
`ed26b4c` → tree: no blocker, no defect in delivered wiring, tooling, gates or
standing documents; one required QA-record repair, discharged by this
revision) and on fresh objective results:

- Package suites 20/20 (`test_claude_role.py`) and 10/10
  (`test_dispatch_stats.py`), re-run 2026-08-31.
- Wiring gate exit 0: 12 roles, 4 first-read roles, 12 + 12 adapters,
  12 allocation pairs, 2 composed skills, 26 principles; citation gate 0
  findings (both maintenance checks, never compiler acceptance).
- Compiler census: the Phase 6b exit run completed twice. First run 5,700 /
  5,681 passed / 19 failed / 1 skipped with one method-only-import 0917 cell
  failing transiently; on the user's requested retry that cell passed 1/1,
  and the complete second census is **5,700 run / 5,682 passed / 18 failed /
  1 skipped, 167.8 s, both `nullary_arm_beside_boxed_arm_0917` cells green**.
  The stable 18 are the carried non-0917 defect set (S119's enumeration minus
  the two 0917 cells), every one tracing to an open FIXME with a named owner;
  Phase 6b changed no compiler or language source, so they are next sprint's
  Phase-1 drawdown scope, not this increment's.
- The review's advisory that `claude_role.py` does not structurally refuse
  `sprint` is **moot against source**: `role_agent` refuses `sprint` before
  provider launch and `test_sprint_refuses_before_provider_launch` proves it.
  No routing needed.

Residual risk is §5 as revised — package-side refusal-coverage gaps routed to
`arch` at contribution time, `review`'s lifecycle classification, ACT-0950,
and the user-gated R1 publication order (§4.4). None is acceptance evidence
for this increment. Phase advancement and close operations remain the user's.

## 5. Residual risks after R1–R4

- Six of twelve roles have never been dispatched live (`design`, `dev`,
  `docs`, `training`, `ops`, `sprint`); W1–W2 check their structure only.
  Falsifier: each role's first live dispatch row.
- Local↔shared adapter allocation equality is W7's, continuously observed
  since 2026-08-31 (12 pairs, plant proven). W7 checks the declared copy;
  the *executed* model and effort remain the dispatch row's, read at the
  Phase-7 dispatch-log review.
- The undated `design/review/` files other than `CLAUDE.md` stay outside the
  live corpus until `review` classifies each one's lifecycle (C8 residual).
- `effort` in a row is what was sent, not what was applied; the CLI reports
  the model, not the effort.
- The interrupted-dispatch closure is fake-provider-proven only (exit 130 →
  `abandoned`, with precedence over `error`); no live dispatch has been
  interrupted through the transport. Open rows now appear on the summary's
  own counted line, so an orphan is visible without reading the row file.
- The citation gate stays blind to doc→doc citations (ACT-0950, advisory).
- 175 live citations of `sprints/SPRINT.md` in 77 documents are lifecycle
  references the gate declares out of scope (C7); those meaning a past sprint
  are stale in a way only a reader can see, and each owner repairs to the
  archive path on touch.
- Closed (was §7 A): `dispatch_stats.py` now counts `transcript_unavailable`
  rows on their own line — the first `arch` attempt (exit 1, 178 s) is
  reported, not dropped — so the Phase-7 dispatch-log review may read the
  summary; `.local/subagents.jsonl` remains the row-level record.
- Enrolled debts from the widening: seven FIXMEs whose `refers_to:` name
  `.claude/commands/` (0764 `review`, 0765 `dev`, 0938/0940/0941/0943 `arch`,
  0944 `qa`), three `design/arch/legacy/` lines (`arch`),
  `design/typecheck/ast-annotation.md:1234` (`design`), `sprints/ROADMAP.md`
  lines 3 and 522 (`sprint`). Rustdoc at
  `crates/cranelisp-backend/src/cache/manifest.rs:217` cites the retired
  command file and is outside both the checker and this sprint's boundary
  (compiler source) — next product sprint, `dev`/backend.

## 6. Handoffs

| To | What |
|---|---|
| `sprint` | R1 in the §4.4 order; the user decisions named in the Wave 6 report (publication now or carry locally; owners for `.claude/`, `.github/`, `AGENTS.md`, `.codex/`; the `xhigh` effort override in root `CLAUDE.md` §Models; the Copilot inventory); moving `sprints/reimplementation.md` to `sprints/archive/` or accepting its 5 enrolled entries; ROADMAP line 3 (cites `tests/plan/strategy.md`, which does not exist) and line 522 |
| `test` | **Nothing open.** W7 — the allocation-equality condition, its plant, and the docstring repair in `scripts/verify-role-wiring.py` — was delivered at Phase 6b (§2 D-2, verified 2026-08-31), as were the earlier Wave 6 items: W6, the C8 leg, the `tests/citation_drift.rs` header contradiction and its stale ACT-0946 path, the §7 C-ii dedupe (§4.5) |
| `review` | State which undated `design/review/` files besides `CLAUDE.md` are standing, so `qa` can admit them to the live corpus per file (C8 residual). The content repair of `design/review/CLAUDE.md` itself was delivered at Phase 6b |
| `arch` | package-side at contribution time: the three unexercised refusal branches in §2 "Not allocated here" (missing-contract, adapter-name-mismatch, missing-`model`). The rest of that list — the summary's dropped `transcript_unavailable` rows, the unreachable adapter fallback, the `close_row` classification order and the stale writer docstring (§7 A, B; audit F-7) — was delivered in the integrated `.agents` delta, verified against source 2026-08-31. Still open: `design/CLAUDE.md`'s dead `sprints/METHOD.md` §1.4 anchor; `design/arch/legacy/` retired-mechanism lines at archive triage |

## 7. Wave 4 review triage

Findings from the independent direct review of Wave 4, each verified against
source before disposition. Verdicts: the three required findings are
**confirmed**; the advisories are classified and not implemented.

| # | Finding | Verdict and evidence | Disposition | Owner |
|---|---|---|---|---|
| 1 | C1 corpus membership not continuously discriminated | Confirmed. `collect_docs` returns explicit paths before the glob loop; control run with the four S120 globs removed: 431 documents, 0 findings (465 with them). Neither the gate nor C5 moves. | C6 allocated (listing + membership leg; pinned count rejected as a bump-without-looking tax) | `test` |
| 2 | `sprints/SPRINT.md` lifecycle vs. `sprints/` as a root | Confirmed and measured: 175 citations / 77 live documents; 174 PATH findings / 76 documents with the file absent; 97 carry `§`, so they also resolve falsely mid-sprint. Coverage defect attributed to `qa` (Wave 3 admitted the root without inspecting lifecycle finality). | Ruled at ACT-0946 §Ruling 6: lifecycle unchanged, path declared lifecycle-scoped, C7 leg; no bulk rewrite; stub rejected (turns coordination state into a file and still resolves falsely) | `test` (C7); owners repair to archive paths on touch |
| 3 | W3 and W4 have no planted proof | Confirmed by reading the fence: plants for W1, W2, W5 only; the clean leg pins roles and principles but not composed skills. | One plant each, smallest discriminating delta (§2 D-2); `2 composed skills` pinned | `test` |
| C4 | Baseline 610 → 605, +21 / −26, old-scope flat | Confirmed on the diff: every added fingerprint under ruling 5 (i), every removed one an `audits/*-2026-06-14.md` entry under item 4. | Recorded in ACT-0946 §Ruling 5; the action stays open on C6 and C7 | `qa` |
| A | `dispatch_stats.py` omits the failed `transcript_unavailable` `arch` row | Confirmed: `read_rows` filters that outcome out; the live summary shows 6 runs and no line for the first `arch` attempt. | Advisory, package-side. Test allocation: one `test_dispatch_stats.py` case — a closed `transcript_unavailable` row is counted apart like `abandoned`, never averaged, never dropped. No cranelisp test. Final-QA consequence: none for acceptance; Wave 6 reads the row file directly. | `arch` (package contribution) |
| B | Package adapter fallback may be unreachable | Confirmed: `role_agent` falls back to `.agents/agents/<role>.md` only when `.claude/agents/<role>.md` is absent, then invokes the CLI with `--agent <role>`, which resolves from `.claude/agents/` — the branch validates an adapter the CLI cannot load. `test_claude_role.py`'s fixture creates both files and no case removes the consumer one; here W1 makes the consumer adapter a gate condition, so the branch is unreachable from a wired consumer. | Advisory, package-side: delete the fallback (the docstring already promises refusal without a consumer-visible agent) or make it real. Test allocation: none in cranelisp; a package case if the branch is retained. Final-QA consequence: none. | `arch` (package contribution) |
| C | Ownership and commentary for the two `scripts/` checkers duplicated or unclear | Confirmed: root `CLAUDE.md` §Project Layout has no `scripts/` row; the directory holds `review`'s dispatch preamble, `qa`'s ratchet and the executing halves of two `test`-owned gates, and `citation_drift.rs` plus §2 D-1 each carry an ownership theory. The W1–W5 list is stated in three places, the three-check list in two. | (i) `sprint` declares ownership in root `CLAUDE.md` §Project Layout or METHOD §3.1 — recommended: `scripts/verify-*.py` to `test` (changed only with their fences), `scripts/citation-drift-baseline.txt` to `qa`, and the review launcher `scripts/codex-review.sh` to `review` (that launcher and its schema were since removed at Phase 6b, so its row is moot). (ii) `test` keeps one carrier of each condition list — the script docstring, with the `.rs` header citing it; this document is the sprint allocation and is not the durable carrier. Test allocation: none. Final-QA consequence: none; a commentary-grade defect. **Both delivered at Phase 6b (§4.5).** | `sprint` (i), `test` (ii) |

Minimal test allocation from this triage: C6, C7, the W3 and W4 plants, the
composed-skill pin — all in the two existing gate files, no new test binary.
Final-QA consequence: acceptance items 1 and 3 remain graded by inspection for
exactly those conditions until the legs are green, and C7 blocks Phase 7
independently of acceptance.
