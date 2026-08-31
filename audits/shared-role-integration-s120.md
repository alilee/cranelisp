# Shared-role integration (`.agents` consumer wiring) — Whole-Context Assessment — Sprint 120

> **Context**: Cranelisp's consumption of the shared role package — the
> submodule pin and its uncommitted delta, the twelve role contracts and their
> composition, the two host-adapter inventories, the cross-provider transport
> and telemetry path, the consumer hook wiring, the package's consumption
> guidance, and the repository gates that keep those relationships coherent.
> User-directed, out of rotation (`sprints/SPRINT.md` §Audit); the unspent
> `src/` rotation remains next. First assessment of this context — no
> predecessor trail.
>
> **Checkpoint** (2026-08-30, read-only): superproject `HEAD = 0ccacf0b`
> ("connect .claude and .github to .agents; retire the command files") plus
> the uncommitted Sprint 120 working tree — 22 modified, 2 deleted, 6 untracked
> paths in the superproject; submodule `.agents` pinned at `b856b8f2` on its
> local `main` with 3 modified and 3 untracked files in its working tree. This
> document is the only file written.
>
> **Method**: the acid test (`sprints/METHOD.md` §2.7) — *if we lost this
> context's code and docs but retained the insight, would a lean second-time
> solution look like this?* — then the audit contract's separate grades for
> requirement fulfilment and maintenance economy. Every claim in the dispatch
> brief, `sprints/SPRINT.md` and `tests/plan/s120-evidence-delta.md` was
> re-verified against source or by executing the check (§7).
>
> **Scale at audit**: 14 contracts (12 roles + 2 support, ≈1,900 lines); 36
> adapter files (12 consumer Claude, 12 Copilot, 12 package defaults); package
> tools 348 + 293 + 207 lines plus 300 + ~100 lines of their tests; consumer
> gates `scripts/verify-role-wiring.py` 313 lines with `tests/role_wiring.rs`
> 345 lines, and the S120 growth of `scripts/verify-citations.py` (+~110) with
> `tests/citation_drift.rs` (+500, now 778); 23 telemetry rows in
> `.local/subagents.jsonl`.

---

## 1. Verdict

### 1.1 Acid test, per attribute

| Attribute | Grade | One-line basis |
|---|---|---|
| Design quality (fitness) | **strong** | Pin + one symlink + thin consumer adapters carrying only allocation and entry text + one stdlib-only transport + one append-only telemetry writer + two executing gates with planted-fault proofs. The package/consumer split — procedure in the package, allocation/routing/declaration in the consumer — is the split a second-time solution would draw. |
| Design realisation | **weak at this checkpoint** | The realisation exists only in two working trees. The submodule pin `b856b8f2` is on **no ref of the package remote** (§4 F-1), so a fresh clone cannot even check the package out; the transport, telemetry, hooks and the root declaration are uncommitted (F-2). As-built-in-tree matches the design; as-committed does not. |
| Simplicity & volume | **adequate** | Contracts and transport are lean. Twenty-four hand-copied adapter bodies and ~1,100 lines of gate-plus-fence code for ~420 lines of checker are heavier than the risk they cover (F-8, F-9). |
| Duplication | **adequate** | The role inventory lives in four carriers *by design* and is measured; the adapter bodies are 24 copies of one table; the W1–W5 condition list is stated in three places. |
| Risk-weighted coverage | **strong** | Both gates carry planted-fault proofs in both polarities with controls; five of twelve roles have live end-to-end dispatch rows; the transport's failure classes are pinned by 14 fake-provider cases. Two gaps: the principle first-read leg is claimed but not measured (F-3); the fresh-clone path is unproven and currently broken (F-1). |
| Maintainability | **adequate** | Ownership of `scripts/` is now declared (uncommitted); the host-wiring surfaces themselves (`.claude/`, `.github/`, `AGENTS.md`, `.codex/`) have no declared owner (F-4); one package tool docstring names a writer that no longer exists (F-7). |
| Memory freshness | **adequate** | Root `CLAUDE.md` (working tree), the adapters and the contracts are current. `sprints/SPRINT.md`'s dispatch log is five rows behind the telemetry (F-5); a *live* `design/review/CLAUDE.md` still routes the reviewer to the retired command file, hidden from the gate by an over-broad historical filter (F-6). |

**Overall.** Would the second-time solution look like this? **In shape, yes.**
The pieces are the right pieces and there are few of them; nothing here is
speculative infrastructure, and every instrument has been made to fire against
a planted fault before being trusted. **In state, not yet:** the sprint's whole
proof lives in uncommitted working trees, and the one committed fact — the
submodule pin — points at a commit the world cannot fetch. The second-time
solution would also not hand-maintain twenty-four adapter files and then write
six hundred lines to detect their drift; it would generate them from the one
table they copy, which makes the drift class unconstructable and covers the
first-read obligation by construction.

### 1.2 Requirement fulfilment

Measured against `sprints/SPRINT.md` §Scope and acceptance, on the working
tree unless stated.

| # | Acceptance item | State | Basis |
|---|---|---|---|
| 1 | Twelve declared roles resolve through the pinned package; every committed adapter names a live contract | **Met on this machine; not reproducible elsewhere** | 12/12 contracts committed at the pin; 12/12 + 12/12 adapters name `.agents/skills/<r>/SKILL.md`; `verify-role-wiring.py` exit 0. The pin is unreachable from the remote (F-1), so no other checkout can establish this. Note: the literal item is true at committed `HEAD`+pin — what is uncommitted is the *dispatch path*, not the contracts (§7.3). |
| 2 | `ACT-0948`/`ACT-0949` resolved; no live `.claude/commands/` reference in the owning roles' surfaces | **Met as scoped** | Both action files deleted; `design/arch/*.md` (top level), `design/arch/principles/`, `spec/` clean by `rg`. Outside the item's scope but inside this boundary: `design/review/CLAUDE.md` (F-6), seven FIXME `refers_to:` lines, `design/arch/legacy/`, `design/typecheck/ast-annotation.md:1234`, `crates/cranelisp-backend/src/cache/manifest.rs:217` still cite it — all enrolled or filtered, none live-gating. |
| 3 | `ACT-0946` ruled, with detection-proven evidence for the retained corpus | **Met** | Seven rulings recorded; C1–C7 landed; `cargo nextest run --test citation_drift` 4/4 green; live run 465 documents, 8,045 citations, 0 findings; baseline 610→605 with the diff shape the ruling requires. The action's "open" lines are now satisfied but the record still says open — `qa` closes at Wave 6. |
| 4 | Independent audit with every finding routed | **This document** | §4 routes every finding. |
| 5 | Applicable checks pass from the final tree; QA recommends or names the residual | **Not yet assessable** | The final tree does not exist (F-1, F-2). On the working tree: both repository gates and both package suites green (§7.1). The full suite was not run here — it is `qa`'s Wave 6 act and no compiler source changed. |

The sprint goal — *demonstrate that Cranelisp can run a bounded increment
through the shared role package* — is **demonstrated in the record**: five
roles (`arch`, `spec`, `qa`, `test`, `review`) ran through the transport on
their consumer allocations, two Claude-hosted subagents were recorded by the
hooks, a real failure closed its row, and owner repairs landed in owned files.
It is **not yet demonstrated as a repository state** anyone else can reproduce.

### 1.3 Maintenance economy — **C**

Assessed independently of correctness and of the green evidence above.

Material, bounded, avoidable weight at the wiring layer:

- **Change amplification.** A role rename or a package converge that drops a
  role touches root `CLAUDE.md`'s table, two adapters, the composition file,
  the contract directory and three pinned counts in the fence. That is by
  design measured rather than structural, and the design chose measurement
  where generation was cheaper (F-8).
- **Duplicated carriers.** 24 adapter bodies copying one table; a second,
  consumer-less inventory for Copilot (F-9); the W1–W5 list in three places;
  two ownership theories for `scripts/verify-citations.py` at this checkpoint
  (F-11).
- **Evidence amplification.** ~1,100 lines of gate and fence for ~420 lines of
  checker, with assertion messages that restate the rationale of the document
  they cite. Each leg discriminates something distinct; the prose does not.
- **Coordination.** The contribute-at-close cadence sanctions a window in
  which the consumer's pin is unpublished — the window this checkpoint is in —
  and nothing in the method closes it before a fresh clone would hit it (F-1).

Not D: the weight does not cross any product path, and ordinary role work — a
dispatch — stays local and cheap. Not B: the propagation is real and recurs on
every converge.

---

## 2. What is required, in plain terms

Cranelisp must be able to run its increments through roles whose procedure it
does not own: each of twelve named roles must reach its shared contract from
whichever host is coordinating (Claude Code, Codex, potentially Copilot), run on
the model and effort Cranelisp chose for it, receive exactly the brief it was
given, and leave a record of having run — so that the sprint can attribute
work, review spend, and notice a dispatch that never came back. The package
must be pinned so that an increment is evidence of one contract revision, and
Cranelisp's own changes to that package must be provable before they are
published. Records that name any of these relationships must stay true, and the
truth must be measured rather than remembered.

Sources: the user's stated S120 goal; root `CLAUDE.md` §Roles, §Cross-provider
routing, §Host adapters, §Assurance; `.agents/CONSUMING.md` §Wiring,
§Cross-provider dispatch, §Cadence, §What a consumer declares.

## 3. Delivery posture and the counterfactual

**Posture.** Phase H, single developer, one machine; the coordinator this
sprint was Codex, the roles ran on Claude; no CI. Everything is reversible and
nothing here touches the compiler. The cost of delay on a working solution is
low — the value is in the *proof*, and the proof decays if the state it proved
is not committed.

**Smallest credible realisation** (economic counterfactual only):

1. The submodule pin, the `.claude/skills` symlink, and `.gitmodules` with
   `update = merge` — as built.
2. One table (role → description, model, effort, first-read flag) and a
   ~50-line generator that writes both adapter sets; the gate becomes
   "regenerate and diff" and W1/W2 vanish as measured conditions. Copilot
   adapters exist only if Copilot dispatches.
3. The transport and telemetry writer as built (they are already near minimal
   and stdlib-only), with the failure-classification order corrected (F-7).
4. `settings.json` hooks — as built, and tracked.
5. The principle-index reconciliation (W5) and the composed-skill existence
   check (W3), which have no structural form.
6. The citation-gate widening as built, minus the repeated rationale in
   assertion prose.

Against that: the as-built solution carries items 2 and the F-9 inventory as
its avoidable weight, and lacks the committed state.

## 4. Findings

Ranked by impact × likelihood × urgency. Evidence class: **D** direct (read or
executed here), **I** inference, **U** unknown. Owner per the audit contract's
routing; priority is assessment priority, not a disposition.

### F-1 — The pinned package commit is unreachable from its remote · **High** · `sprint` (with `arch` for the package claim) · D

`git -C .agents ls-remote origin` returns `refs/heads/main = 3bbc70a` and one
canary branch; **no ref contains `b856b8f2`**, the commit `.gitmodules` and
`HEAD` pin. The three commits above `3bbc70a` (`2d6e02d`, `e94fbde`,
`b856b8f`) exist only on this machine's submodule `main`. A fresh clone of
cranelisp at `HEAD` fails `git submodule update`; `.agents/CONSUMING.md`
§Wiring's "a fresh clone resolves the role contracts with no bootstrap step" is
false today, and acceptance item 1 cannot be established anywhere but here.

The package's own guidance sanctions this window (§Contributing: "its
superproject pin references a commit no other repository holds until the
change is contributed"), which contradicts its §Wiring promise. One of the two
claims must narrow — routed to `arch` as the package contribution owner. The
operational fact — publish before the sprint is called accepted, or state in
the acceptance that the proof is single-machine — is `sprint`'s.

### F-2 — The consumer's executable wiring is uncommitted in both trees · **High** · `sprint` · D

Untracked: `.claude/settings.json` (the only hook wiring),
`.agents/tools/{claude_role,subagent_telemetry,test_claude_role}.py`. Modified,
uncommitted: `.agents/{CLAUDE,CONSUMING}.md`, `.agents/.gitignore`, root
`CLAUDE.md` (§Cross-provider routing and §Host adapters replace the "In
transition" paragraph), `sprints/METHOD.md` §1.1 and §3.1, the five adapters
that gained the principles first-read, `scripts/codex-review.sh`, both gates
and their fences. Confirms `qa`'s R1 and R2. Positive note: on a fresh clone
the wiring gate's W4 fails loudly (no `settings.json`, no tools), so the
absence would be detected rather than silent — provided the clone could resolve
the submodule (F-1).

Precision on R1's wording: acceptance item 1's literal claim is true at
committed `HEAD`+pin — all twelve contracts and all twenty-four adapters are
committed. What is uncommitted is the dispatch *path* and the *declaration*.
The acceptance record should say which.

### F-3 — The principle first-read is claimed measured and is graded by inspection · **Moderate** · `qa` (allocation), `arch` (the claim) · D

`design/arch/principles/CLAUDE.md` line 14 names "the adapter-inventory check"
as the falsifier for "an adapter that drops the first-read", and
`tests/role_wiring.rs` lines 14–18 say "This file is both" of the named
falsifiers. `scripts/verify-role-wiring.py` W2 checks `name`, `model`,
`effort` and the contract path only; `grep -n principles.md` on the script
finds W5 lines alone. Deleting the `design/arch/principles.md` paragraph from
`.claude/agents/dev.md` passes the gate. This is precisely the §Assurance
class the sprint set out to close — a record borrowing the language of a
mechanism it does not have. Least-cost repair: one W2 clause for the four
roles `sprints/METHOD.md` §1.1 names, one plant; or F-8, which retires the
question.

### F-4 — The host-wiring surfaces have no declared owner · **Moderate** · `sprint` · D

Root `CLAUDE.md` §Project Layout has no row for `.claude/`, `.github/`,
`AGENTS.md`, `.codex/` or `scripts/`; the uncommitted `sprints/METHOD.md`
§3.1 now names owners for `scripts/verify-*.py`, the ratchet and the review
launcher, but none for the adapters, `settings.json`,
`copilot-instructions.md` or `.codex/config.toml`. This sprint `arch` edited
five adapters (the first-read lines); the adapters also carry the model and
effort allocation whose change requires user sign-off. The `sprint` contract
is explicit: "Take ownerless structure to the user."

### F-5 — The sprint dispatch record is behind the telemetry and silent on how review executed · **Moderate** · `sprint` · D / I

`sprints/SPRINT.md` §Dispatch log has five rows. `.local/subagents.jsonl`
holds nine closed role dispatches through the transport (`arch` ×2 including
the failed first attempt, `spec`, `qa` ×2, `test` ×2, `review` ×2) plus this
audit's open row; no `test` or `review` row appears in the plan, and no row
carries the session id the `sprint` contract requires ("record provider,
model, session and outcome in the live sprint dispatch log"). The evidence log
ends "the final entry will name…", so some of this is timing — but Wave 5 runs
after Wave 4 closed, and the record at this checkpoint does not say whether the
Wave 4 review reached Codex (`sprints/METHOD.md` §2.3) or used the direct
fallback the method requires be recorded. The delta calls it "independent
direct review"; the two `review` rows are Fable; no Codex artifact is visible
under `scripts/`. **Inference:** the fallback was used and not recorded.

### F-6 — A live convention file routes `review` to the retired command file, and the gate cannot see it · **Moderate** · `review` (content), `qa` (corpus classification) · D

`design/review/CLAUDE.md` line 24 names the retired `.claude/commands/review.md`
as "the `/review` role: workflow, findings classification…", and line 43
instructs the reader to walk its cues "alongside the quality checks in" that
same retired file, `.claude/commands/review.md`. The file describes itself as
live ("this section is a **live** part of the review standard"). It is absent from the
live corpus (`--list-docs` lists 0 `design/review/` paths) because
`HISTORICAL_RE` treats every `review/` directory as historical — a filter
written for dated review records that also swallows a standing `CLAUDE.md`.
It is in nobody's enrolled-debt list. Acceptance item 2 is scoped to `arch`
and `spec`, so this does not fail it; it is the same defect class in a third
owner's surface, invisible to the mechanism that was widened to catch it.

### F-7 — Package-side: outcome classification hides failures; unreachable fallback; stale writer name · **Moderate (advisory for acceptance)** · `arch` (package contribution) · D

- `claude_role.py::close_row` tests `measured` before `status != 0`, so a
  failed dispatch without a transcript is labelled `transcript_unavailable`,
  never `error`; `dispatch_stats.py::read_rows` then excludes that outcome.
  Executed: the summary lists 10 runs from 11 closed rows — the first `arch`
  attempt (exit 1, 178 s, 0 tokens) is in neither the figures nor the
  abandoned line. Open rows are likewise invisible. Confirms review finding
  A; the Phase 7 spend review must read the row file, not the summary.
- `subagent_telemetry.py::record_event` closes every hook `SubagentStop` with
  `"outcome": "success"` when a transcript exists; the hook has no failure
  signal, so "success" means "stopped with a transcript". The row schema
  conflates two facts.
- `role_agent` falls back to `.agents/agents/<role>.md` and then launches the
  CLI with `--agent <role>`, which resolves from `.claude/agents/`; from a
  consumer wired per `CONSUMING.md` the branch validates an adapter the CLI
  cannot load. Confirms review finding B. `test_claude_role.py`'s
  non-dispatchable case exercises the missing-*agent* refusal, not the
  missing-*contract* one (the fixture writes `maintain-documents/SKILL.md`).
- `dispatch_stats.py` docstring: rows "written by
  `.claude/hooks/log-subagent.py`" — that writer does not exist; the writers
  are `subagent_telemetry.py` and `claude_role.py`.
- The summary groups "by role" but lists `Explore`, a built-in helper agent
  the hooks also record; it is a by-agent table.

### F-8 — Measured where structural is cheaper: the adapters · **Advisory (economy)** · `sprint` (shape), `test` (implementation) · D

Twenty-four adapter files are copies of one table — role, description, model,
effort, and for four roles a first-read paragraph. W1 and W2 exist to detect
their drift, at 313 + 345 lines and three pinned counts. A generator from root
`CLAUDE.md` §Roles plus a twelve-row allocation map, with the gate reduced to
"regenerate and compare", makes the drift class unconstructable, subsumes F-3
(the first-read line becomes template content) and halves the fence. W3 and W5
stay measured; they have no structural form. `maintain-documents` §Repair
names this move — "derive inventories mechanically where hand-maintained
copies can disagree".

### F-9 — Weight without a consumer · **Advisory (economy)** · `sprint` → user · D / U

- Twelve Copilot adapters and `.github/copilot-instructions.md` have no
  dispatch record anywhere in the repository; they add W1/W2 branches and
  corpus globs. Classification: potential future extension. Trigger to keep:
  the first Copilot dispatch. Least-cost response otherwise: delete, or
  generate (F-8) so they cost nothing to keep.
- `.claude/settings.local.json` — a personal permission allowlist with
  absolute `/home/alilee/…` paths — is tracked, while the shared hooks file
  `settings.json` is not. Claude Code's convention is the inverse.

### F-10 — The effort override is undeclared · **Low** · `sprint` · D

The package allocates every role at `high`; cranelisp runs `arch`, `audit`
and `qa` at `xhigh`. Root `CLAUDE.md` §Models declares tiers only; effort
lives solely in adapter frontmatter. `sprints/METHOD.md` §2.6 treats tier as
a spend decision needing sign-off, and effort is the same class. One clause in
§Models closes it. (Whether `--effort` is *applied* by the CLI is a `qa`-noted
unknown; the row records what was sent.)

### F-11 — Two carriers of one ownership fact disagree at this checkpoint · **Low** · `test` · D

`tests/citation_drift.rs` lines 42–46: "`scripts/verify-citations.py` has no
separately declared owner … governed by [this gate]". The uncommitted
`sprints/METHOD.md` §3.1 now declares it `test`'s. Both are in the same
working tree. The `.rs` header should cite the row, not restate a theory.

### F-12 — Retired role vocabulary in live convention files · **Low** · `test` (`tests/CLAUDE.md`), `arch` (`design/CLAUDE.md`) · D

`tests/CLAUDE.md` says `/testing`, `/qa`, `/dev` throughout while its new
S120 paragraph says `test`/`qa`. `design/CLAUDE.md` uses `/arch`, `/design`,
`/stdlib`, `/review` and cites "`sprints/METHOD.md` §1.4", a section that no
longer exists (METHOD has §1.1–§1.3). Section anchors are outside the
citation checker's remit, so this stays human.

## 5. Strengths

- **Every instrument was made to fire before it was trusted.** Both gates
  carry planted faults for every condition that has logic, each on its own
  scratch copy, with the negative leg pinning counts so an empty enumeration
  cannot pass; the lifecycle fence runs both delivery phases on synthetic
  roots with a control in each. This is §Assurance practised, not cited.
- **The transport is small and honest.** Stdlib-only, one role per run, brief
  on stdin and provably absent from argv and telemetry, refusal before any row
  is written, consumer allocation read from the adapter the CLI will load.
  Its first real failure (sandbox timeout) closed its own row.
- **The cross-provider path worked five times on the consumer allocation** —
  rows show `fable`/`xhigh` sent and `claude-fable-5` reported, `opus[1m]`
  sent and `claude-opus-5[1m]` reported. That is direct evidence the consumer
  override, not the package default, reaches the provider.
- **Owner repairs landed in owned files and deleted their filings**
  (`ACT-0948`, `ACT-0949`), and the retired mechanism is now a *dead target*
  the citation gate can see (proved by a planted `.claude/commands/` citation).
- **The corpus ruling refused two tempting wrong repairs** — a pinned document
  count and a standing `SPRINT.md` stub — and recorded why.

## 6. Traces

**Normal path, Claude coordinator.** Agent tool → `.claude/agents/<role>.md`
(this host lists all twelve with these descriptions) → contract via
`.claude/skills → ../.agents/skills` (this session's skill list carries all
fourteen) → `SubagentStart`/`SubagentStop` hooks →
`.agents/tools/subagent_telemetry.py` → open row, closed row with transcript
metrics. Evidence: two `Explore` rows, opened and closed, session id matching
their `qa` parent. **Cost:** one JSON file, one Python module, no
coordinator involvement.

**Normal path, non-Claude coordinator.** `python3 .agents/tools/claude_role.py
<role> <brief>` → contract exists? → consumer adapter exists and names the
role? → `model`/`effort` from frontmatter → open row → `claude -p --agent
<role> --model M --effort E --permission-mode acceptEdits --output-format json
--session-id S` with the brief on stdin → result JSON → transcript located under
`~/.claude/projects/*/S.jsonl` → reconcile any open hook children of S → closed
row → stdout passed through. Evidence: nine closed rows. **Cost:** one
process per role, no intermediary.

**Review path.** `scripts/codex-review.sh` composes a preamble naming root
`CLAUDE.md`, METHOD §2.3, the `review` and `quality-standards` contracts and the
principles index; runs `codex exec -s read-only` against
`codex-review-schema.json`. The preamble is repaired (R2). Whether it was
*used* this sprint is unrecorded (F-5). `codex` 0.150.1 is on `PATH`.

**Gate path.** `cargo nextest run` → `tests/role_wiring.rs` → `python3
scripts/verify-role-wiring.py <root>` → W1–W5 → exit 0 with counts; and
`tests/citation_drift.rs` → `verify-citations.py --corpus live --baseline …`
→ 0 findings. Executed here: 7/7 green in 4.5 s.

**Failure paths.** (a) Missing adapter → W1 names the role; proved by plant.
(b) Adapter naming the wrong role → W2; proved. (c) Composed skill missing →
W3; proved. (d) Hook rewritten to another real script → W4; proved. (e)
Orphan principle → W5; proved. (f) Fresh clone → submodule fetch fails at
the pin (F-1) — *before* any gate can run. (g) Transport: provider exit ≠ 0
with transcript → `error`, status propagated (tested); without transcript →
`transcript_unavailable` and dropped from the summary (F-7, observed live).
(h) SIGINT/SIGTERM → `abandoned` — coded, untested (package-side gap `qa`
already names). (i) Package converge renames a role → W1 fires on the
contract path; the adapter must then be edited by hand in two places (F-8).
(j) A record citing a retired path under `design/review/` → invisible (F-6).

## 7. Evidence ledger

### 7.1 Checks executed

| Command | Result |
|---|---|
| `git status --short`; `git log --oneline -5`; `git submodule status`; `git ls-tree HEAD .agents`; `cat .gitmodules` | HEAD `0ccacf0b`; pin `b856b8f2` = submodule HEAD; `update = merge`, `branch = main` |
| `git -C .agents status --short`; `git -C .agents log --oneline origin/main..HEAD`; `git -C .agents ls-remote origin` | 3 modified + 3 untracked; 3 local-only commits; remote `main` = `3bbc70a`; **0 refs contain the pin** |
| `git -C .agents ls-tree -r HEAD --name-only` | 14 `skills/*/SKILL.md`, 12 `agents/*.md`, `tools/dispatch_stats.py` + tests + `overseer/`; **no** `claude_role.py` / `subagent_telemetry.py` at the pin |
| `git ls-files .claude .github`; `git check-ignore -v .claude/settings.json .local/subagents.jsonl`; `readlink .claude/skills` | adapters and `settings.local.json` tracked; `settings.json` untracked and not ignored; `.local/` ignored; symlink `../.agents/skills` |
| `git diff` on root `CLAUDE.md`, `.gitignore`, `sprints/METHOD.md`, `scripts/codex-review.sh`, both adapter dirs, `tests/CLAUDE.md`, `scripts/verify-citations.py`, `tests/citation_drift.rs`, `design/arch/**`, `spec/CLAUDE.md`; `git -C .agents diff` | read in full; summarised in §4 |
| `python3 scripts/verify-role-wiring.py` | `12 roles, 12 claude adapters, 12 copilot adapters, 2 composed skills, 26 principles. 0 finding(s).` exit 0 |
| `python3 scripts/verify-citations.py --corpus live --baseline scripts/citation-drift-baseline.txt` | `465 documents, 8045 citations (6045 paths, 806 line refs, 1992 symbols verified; 941 exempt, 182 lifecycle). 0 finding(s).` |
| `… --corpus live --list-docs` | 465 paths; 12 + 12 adapters, `copilot-instructions.md`, 9 `sprints/` present; 0 `.agents/`, 0 `sprints/archive/`, 0 `design/review/` |
| `python3 -B .agents/tools/test_claude_role.py`; `python3 -B .agents/tools/test_dispatch_stats.py` | 14 OK; 5 OK |
| `python3 .agents/tools/dispatch_stats.py --since 2026-08-30` | 10 runs (`test` 2, `qa` 2, `review` 2, `arch` 1, `spec` 1, `Explore` 2); the failed `arch` row absent |
| `cargo nextest run --test role_wiring --test citation_drift` | 7 passed, 0 skipped, 4.5 s |
| `rg -n '\.claude/commands'` (excluding `target/`, `.git/`, the baseline) | 51 files total incl. archive; live non-enrolled: `design/review/CLAUDE.md` ×2 (F-6) |
| `grep -n principles.md scripts/verify-role-wiring.py` | W5 lines only (F-3) |
| `grep -c '"open": false' .local/subagents.jsonl` | 11 closed rows |
| `python3 --version`; `which claude codex`; `codex --version` | 3.14.4; both CLIs present; `codex-cli 0.150.1` |

### 7.2 Read in full

All 36 adapters; all 14 contracts' frontmatter and the `audit`, `sprint`,
`review`, `quality-standards`, `maintain-documents` bodies;
`.agents/skill-composition.toml`; `.agents/{CLAUDE,CONSUMING,AGENTS}.md` and
the three plugin manifests; `.agents/tools/{claude_role,subagent_telemetry,
test_claude_role,dispatch_stats}.py`; `.claude/settings*.json`;
`.codex/config.toml`; `AGENTS.md`; `.github/copilot-instructions.md`;
`scripts/{verify-role-wiring.py,codex-review.sh}`; `tests/role_wiring.rs`;
`tests/citation_drift.rs`; `sprints/{SPRINT,METHOD}.md`;
`tests/plan/s120-evidence-delta.md`; `ACT-0946`, `ACT-0950`;
`design/arch/principles/CLAUDE.md`; `design/review/CLAUDE.md` §"Where the
live review standard actually lives"; `.local/subagents.jsonl`.

### 7.3 Brief and delta claims — verified, refined, refuted

| Claim (source) | Verdict |
|---|---|
| R1: mechanism exists only in the working tree (delta §4) | **Verified**, and worse than stated — the pin itself is unpublished (F-1). |
| R1: "acceptance item 1 is false at the pin" (delta §4) | **Refined** — the contracts and adapters are committed; the dispatch path and declaration are not. |
| R2: preamble repaired, `rg` empty on `codex-review.sh` (delta §4) | **Verified** by reading the script. |
| R3/R4: C6, C7, W3, W4 plants open (delta §4) | **Superseded** — all landed and green at this checkpoint (7/7). |
| "live `arch` and `spec` dispatch … 2 of 12 roles" (delta §3) | **Superseded** — five roles now have rows (`arch`, `spec`, `qa`, `test`, `review`); ten-of-twelve-unproven is now seven. |
| Review findings A and B, package-side (delta §7) | **Verified** by reading `close_row`, `read_rows`, `role_agent`; A observed live in the summary. |
| Hook probe: hooks fire on both events (delta §3) | **Verified** — two `Explore` open/closed pairs. |
| Inventory 12/12/12/14, 26↔26 principles (delta §3) | **Verified** by execution. |
| "no `.claude/commands` reference in … top-level `design/arch/*.md`" (delta §3) | **Verified as scoped**; `design/review/CLAUDE.md` is outside the listed scope and live (F-6). |
| "`.claude/skills` resolves the shared contracts directly" (root `CLAUDE.md`) | **Verified** — this session's skill inventory carries the fourteen. |
| `design/arch/principles/CLAUDE.md`: "the adapter-inventory check" is the falsifier for a dropped first-read | **Refuted** (F-3). |

### 7.4 Unknowns

- Whether `--effort` is applied by the CLI (`qa` residual; rows record what
  was sent).
- Whether the Wave 4 review reached Codex (F-5; no record either way).
- The interrupted-dispatch path (`abandoned`) — coded, never exercised.
- Whether any Copilot dispatch has ever occurred (no record; F-9).
- Full-suite state on the final tree — not run here; no compiler source
  changed this sprint.

## 8. Recommendations

Each carries evidence (§4), a cost class, and a proposed owner. Next sprint's
Phase 1 disposes them with the user; `audit` files nothing.

| # | Recommendation | Cost | Owner | Priority |
|---|---|---|---|---|
| R-1 | Commit the package delta on the submodule's local `main`, push it (user approves), bump the pin, track `.claude/settings.json`, commit the consumer delta — and state in the acceptance which of these has happened. Narrow `CONSUMING.md` §Wiring's fresh-clone claim or close the contribute window before acceptance. | small | `sprint`; `arch` for the package text | High |
| R-2 | Either add the first-read leg to W2 for the four roles METHOD §1.1 names (with a plant), or adopt R-4 and let the claim in `design/arch/principles/CLAUDE.md` become true by construction; until one lands, reword the claim to "asserted". | small | `qa` allocation; `test`/`arch` | Moderate |
| R-3 | Declare owners for `.claude/`, `.github/`, `AGENTS.md`, `.codex/` and `scripts/` in root `CLAUDE.md` §Project Layout (or METHOD §3.1), and state the effort override in §Models. | small | `sprint` → user | Moderate |
| R-4 | Generate both adapter inventories from one table; reduce W1/W2 to regenerate-and-diff; decide whether the Copilot inventory has a consumer, and if not, drop it or keep it only as generated output. | small–medium | `sprint` (shape) → `test`; user on Copilot | Advisory |
| R-5 | Repair `design/review/CLAUDE.md` to name the contract and launcher; narrow the citation checker's `review/` historical pattern so a standing `CLAUDE.md` under it stays in the live corpus. | small | `review`; `qa` | Moderate |
| R-6 | Package contribution at close: classify `status != 0` before `measured`; carry `transcript_unavailable` and open rows in the summary as their own lines; distinguish hook "stopped" from "success"; delete or realise the package-adapter fallback; add the missing-contract and SIGTERM cases; fix the `dispatch_stats.py` writer docstring. | small | `arch` | Moderate (advisory for acceptance) |
| R-7 | Bring `sprints/SPRINT.md`'s dispatch log to parity with the row file, with session ids, and record how the Wave 4 review executed. | small | `sprint` | Moderate |
| R-8 | Align `tests/citation_drift.rs`'s ownership header with METHOD §3.1; sweep the retired `/skill` vocabulary and the dead `§1.4` anchor in `tests/CLAUDE.md` and `design/CLAUDE.md`. | small | `test`; `arch` | Low |

## 9. Disposition trail

*(Appended at Sprint 121 Phase 1 by `sprint` with the user: accepted →
filed against the proposed owner; declined → recorded here with rationale.
This assessment is a point-in-time record and is not rewritten.)*
