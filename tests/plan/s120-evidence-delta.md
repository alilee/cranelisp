# Sprint 120 QA evidence delta — shared-role integration proof

> **Retained dated record (S122 consolidation).** Only the parts that open
> [ACT-0950](../../sprints/actions/ACT-0950-citation-checker-doc-to-doc-roots.md)
> and the S120 shared-role audit cite remain, with their original numbering:
> §1 (the ACT-0946 measurement), §2 with condition table D-1 (C1–C8), §4 with
> §4.1, and §7. The citation instrument measured here was retired in S122 in
> favour of the shared document checker; [PLAN](PLAN.md#repository-gates--maintenance-checks-never-compiler-authority)
> states the current repository gates, so these are measurements of a former
> instrument, not current conditions. The role-wiring conditions, RED
> enumeration, publication order, Phase-6b judgments, residual list and handoffs
> are recoverable with `git show 48d6e713:tests/plan/s120-evidence-delta.md`.
## 1. ACT-0946 measurement

The checker was run in-process with `DOC_GLOBS` / `SOURCE_ROOTS` widened
against the working tree; `new` counts findings absent from the 610-entry
baseline. `--corpus live` throughout unless stated.

| Config | Docs | Citations | New findings | Where |
|---|---|---|---|---|
| A. current (control) | 434 | 7,507 | 0 | — |
| B. `sprints/` as root only | 434 | 7,739 | 4 | the historical architecture legacy directory ×4 (citing `sprints/triad-shared.md`, which does not exist, and a `fixmes/0001..0009` range) |
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
| Baseline ratchet (C4) | `git diff -- scripts/citation-drift-baseline.txt` | −26, all `audits/*-2026-06-14.md`; +21 — seven FIXME `refers_to:`, five the historical architecture legacy directory, one `design/typecheck/`, three ROADMAP, five `reimplementation.md`; 610 → 605 |
| Compiler-source census | `git status --short -- src crates stdlib exemplar examples platforms benches Cargo.toml Cargo.lock` | empty. The only `tests/*.rs` changes are the two repository gates |
| Full suite | `cargo nextest run --no-fail-fast` | 5,692 run / 5,672 passed / 20 failed / 1 skipped, 251 s |

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
