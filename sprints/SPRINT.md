# Sprint 89: Agentic-REPL Phase 2 — Build + Document + pre-flight validator (rungs 5–6)

**Status**: PHASE 5 COMPLETE ✅ (Waves 1+2+3 CLOSED) — Phase 6 (user-facing) next, pending user go

**Goal**: Polish the embedded REPL agent's output rendering (prompts, markdown, pretty-printed code) and give it its first **write** capabilities — submit forms (confirm-gated, behind a silent pre-flight validator) and record durable understanding (docstring/preamble edits) — on the read-only Advisor MVP base shipped + live-validated in S88.

## Scope

S89 is the **second sprint of the agentic-REPL track** (the first track after the pre-H consolidation arc; ROADMAP §"Agentic-REPL track"). S88 shipped rungs 0–4 (the read-only Advisor MVP, live-validated against Anthropic). S89 delivers **rungs 5–6** — the step from *advise* to *act*, entirely behind the default-off `agent` feature.

Entry baseline (S88 close): default `cargo nextest run` **1516/1516, 0 intentional reds**; `--features agent` **33/33 lib + 23/23 e2e**; default build provably agent-free (no rig/tokio in the dep tree). Any red in the default suite is a true regression. The Stage B/C feature fault-line and the **byte-identical-when-feature-OFF** invariant are load-bearing and must survive this sprint.

### Agent output rendering — live-use polish + 1 defect [core]

Surfaced by the user from live S88 use (2026-06-22). The read-only Advisor works, but its output presentation is rough. Four items — three experience improvements, one defect. `/repl` owns the experience spec (`repl/spec.md §17` agent frame); `/dev (src/)` implements; `/qa` repros the defect.

1. **Agent inputs get no prompt (improvement).** When the agent issues a pull (a command rendered as if typed) or its turn is echoed, there is no prompt prefix marking the line as agent-issued. Give agent-originated input a visible prompt (distinct from the human prompt) so the transcript reads honestly — keystroke-by-keystroke who did what.
2. **Markdown not formatted (improvement).** The agent returns markdown prose; today it renders raw. It should be formatted for the terminal (headings/lists/emphasis/inline-code) within the existing agent-prose style frame (`repl/spec.md §10.3`; degrades cleanly under `--no-color`).
3. **`​```lisp` fenced blocks not pretty-printed (improvement).** Lisp code fenced as ```` ```lisp ```` inside the agent's markdown should be routed through the **existing S-expression pretty-printer** (S24 — syntax highlighting + Lisp indentation, Principle 7 reuse), not emitted as a raw fence.
4. **Pretty-printer leaks raw escape codes on agent output (DEFECT).** When the pretty-printer renders agent output, ANSI color codes appear as literal text instead of rendering. **Needs a `/qa` narrow failing-not-ignored repro (CLAUDE.md §Testing) before closure** — likely a color-mode / writer-target mismatch on the agent render path vs. the normal REPL render path. Owning skill flips it green in the same change-set with its mandatory unit test.

**Acceptance:** an `/ask` answer containing prose + a ```` ```lisp ```` block renders with formatted prose and a pretty-printed, correctly-colored form; agent-issued pulls show an agent prompt; no literal escape codes anywhere; `--no-color` stays clean.

### Rung 5 — Build mode (agent submits forms) + pre-flight validator [core]

The agent gains its **first write path**, and the safety machinery that makes it safe by construction:

1. **Build mode — confirm-gated submit.** The agent can propose-AND-submit a form. Submission goes back through `self.process_commands` / `self.eval` — the *same* cluster-atomic staging path `main.rs` uses (commit-on-Ok / discard-on-Err), inheriting error recovery and backing-file regeneration (design §7.1). The read-only pull allowlist (S88) is **extended with a confirm-gated write arm**; writes remain structurally unconstructable without passing the gate.
2. **Pre-flight validator + silent-repair-anything (U5).** Before generated code is shown or submitted, run it through the **real frontend + typechecker** on staging — the `pub(crate)` **typecheck-only dry-run seam** S88 deliberately kept open (stage→check→discard; design §6.2, §7.5). On **any** failure (parse OR type — U5 ratified *silent-repair-anything*, overriding the design doc's "surface type errors" lean), feed the actual compiler error back to the model and retry **silently**; the user structurally cannot see an agent compile failure. The primer lowers the retry rate; the gate guarantees the floor.

**Acceptance (rung 5):** `/ask "define a function that doubles its argument"` → the agent proposes a `(defn …)`; on confirm it is submitted and **always at least parses**; a deliberately-broken generation is silently repaired and never shown.

3a. **`--yes` autonomous-submit flag (user-requested, 2026-06-22).** A REPL-only CLI flag (companion to `--agent`/`--no-agent`, `repl/spec.md §0.6.1`) that makes the agent's **write-consent gates auto-accept** — Build-mode form submits *and* Document-mode preamble/docstring edits — so the agent acts without the per-action `[y/N]` prompt. **Bypasses *consent*, not *validation*:** the pre-flight validator still runs (silent-repair-anything, U5); only compiling code ever reaches the session. **Off by default**; meaningful only with `--features agent` + an active agent (no-op on default builds, like `--agent`). The read-only pull allowlist is unchanged — `--yes` only auto-answers the gate that already guards writes. **Open design points (flag, don't block):** (a) one blanket flag for all agent writes vs. Build-only — *default: blanket* (the `-y` convention); (b) whether an autonomy escalation warrants a one-time first-use notice (→ `/repl`+`/arch`); (c) naming. **Touches the R3 consent model → quick `/arch` confirm + `/repl`/`/design (src/)` doc updates before Wave 2 builds.**

### Rung 6 — Document mode (durable understanding) [core]

3. **Document mode — consultative docstring/preamble edits.** The agent records its rationale durably in the code, using the S88 module-preamble substrate (first-class comment-block preambles, `SymbolTable.module_preamble`, byte-stable regen). A preamble/docstring the agent writes **round-trips byte-stably** and is **read back by the harvester next session** (closing the memory loop, design §3.1/§3.4).

**Acceptance (rung 6):** the agent writes a module preamble; it round-trips through save/reload byte-identically; a fresh session's harvester reads it back into context.

### Carries folded in

4. **0429 — close (`target: /qa`).** Substantially met in S88 (the rig-trait `MockModel` continuation-pairing test landed). Residual: the one-line `tests/plan/agent-testing-strategy.md §1` correction (the stub implements `AgentModel`, not rig's `CompletionModel` directly) + formal close + **`/qa` deletes the FIXME**.
5. **0423 — delete the resolved FIXME file (`target: /int`).** Fixed in S88 W1b (lib-dir extraction path + annotation spacing); the fix + green test are the durable record. The file is still on disk; `/int` deletes it. Bookkeeping only.

### Out of scope (deferred, with rationale)

- **`claude-oauth` / subscription-OAuth provider — dropped (user, 2026-06-22): "not a feature."** Surfaced as a S88 idea; explicitly out of the agentic track. Not deferred — removed.

- **Agentic Phase 3 / rung 7 — S90:** compensation-telemetry-driven push/primer curation, semantic spec search (precompute-and-ship index), push-transparency header (U4 — ratified *ambient for MVP, prunable header in Phase 3*), provider/local polish. The S88 **R5 valve** items (spec-grep retrieval + telemetry skeleton) ride this rung.
- **Effect-concurrency track, then Phase H** — the established sequencing (ROADMAP §"Phase H sequencing"). Standing Phase-H carries (0050/0052/0365/0407/0419) + concurrency-track FIXMEs (0408/0424/0425/0426) + ruling-gated (0410/0416) confirm-deferred.

## FIXME debt

| FIXME | Target | Status | S89 disposition |
|---|---|---|---|
| 0050 | /int | deferred | Phase-H carry (display protocol) — confirm deferred |
| 0052 | /repl | open | Phase-H carry (`/learn`) — confirm deferred |
| 0365 | /spec | open | Phase-H carry (Type.member) — confirm deferred |
| 0407 | /arch | open | Phase-H carry (Model-B closure-callback) — confirm deferred |
| 0408 | /port | open | Concurrency-track carry (Sudoku parallel-search) — confirm deferred |
| 0410 | /repl | open | Ruling-gated (`/spec §8.11.4`) — confirm deferred |
| 0416 | /arch | open | `stdlib num.bits` covers — confirm deferred |
| 0419 | /arch | open | Phase-H carry (HostCallbacks builder) — confirm deferred |
| 0423 | /int | resolved-on-disk | **S89 — `/int` delete owed** (fix + green test landed S88; flagged again at Wave-2 close; file is the only residue) |
| 0424 | /arch | open | Concurrency-track carry (par-map/spark) — confirm deferred |
| 0425 | /arch | open | Concurrency-track carry (dependency-service extraction) — confirm deferred |
| 0426 | /arch | open | Concurrency-track carry (D0030 deadlock revisit-trigger) — confirm deferred |
| 0429 | /qa | **CLOSED+deleted** (`a21ec3b`) | rig-trait `MockModel` green; `agent-testing-strategy.md §1.1` reconciled; FIXME deleted |
| 0430 | /design | **filed** (`4bb4cd0`, Wave 3) | docstring-into-source regen (`set-doc` descoped this wave; future Document increment) — confirm-deferred to a later agentic sprint |
| (new) | — | to file | Phase-2 design locks (validator seam, write-allowlist) filed per design §10 "Next skills" |

## Architecture review (Phase 2)

**Verdict (/arch, 2026-06-22): APPROVE.** Technically coherent; every load-bearing seam rungs 5–6 need **already exists** from S88 — Build/Document/validator are *consumer* extensions of the int bounded context, not new machinery. **Zero new cross-crate edges; zero `public-api.txt` baselines move; zero `cranelisp-types` change; no `CACHE_SCHEMA_VERSION` bump.** One owned-doc currency edit (`repl-embedded-agent.md` brought current: U1–U6 ratified, U5 = silent-repair-anything, §9 Phase 2 spelled out; committed `3630b69`).

- **Cluster B — Build mode (first write path):** extending the read-only pull allowlist with a confirm-gated write arm **holds BC §6.3** (REPL-cadence consumer, not a new state window). Submitted forms re-enter via `self.process_commands`/`self.eval` — the *same* cluster-atomic staging path `main.rs` uses (commit-on-Ok / discard-on-Err, Decision 44); **no new eval entry, no new cross-crate edge**. Read-only-by-default stays the structural floor; the write arm is reachable only past the confirm-gate.
- **Cluster B — validator + silent-repair-anything (U5):** the stage→check→discard seam is the **existing** `check_forms` discard-on-Err arm (`src/cluster.rs`/`src/process_form.rs`/`src/worker.rs` — already `pub(crate)`, int-internal). **No new public surface, no facade delta.** U5 needs *less* machinery than the superseded "surface type errors" lean (any `Err` → discard + re-prompt; no error-classification branch).
- **Cluster C — Document mode:** full substrate landed S88 (`SymbolTable.module_preamble`, `capture_module_preamble`, `apply_module_preamble` + byte-stable regen, cache v9). **No `cranelisp-types` change.** Write→save→reload→harvester-read-back crosses no new boundary (reuses the regen path 0423 corrected + the harvester's existing preamble read).
- **Cluster A — agent output rendering:** purely int-internal. Routing ```lisp fences through the existing S24 `pretty_print` is clean Principle-7 reuse, **no interface change**. The ANSI-leak is an **int-internal wiring bug** (agent render path double-handling already-styled text / a fence not routed through `pretty_print`), **not a missing color-mode parameter** — color is globally owned by `src/style.rs::is_color_enabled` (`OnceLock`). No architectural seam.
- **Feature-gating:** PRESERVED — rungs 5–6 + cluster-A render ride the existing four `#[cfg(feature="agent")]` cuts; feature-OFF stays byte-identical. Cluster A is the watch-item: markdown/fence render must live **inside** `src/agent/`, never touching a default-build render path.

### Revisions (applied to scope)

- **R1 — Cluster-A markdown/fence rendering MUST be agent-output-only + fully `#[cfg(feature="agent")]`.** Formatter + ```lisp→`pretty_print` routing live in `src/agent/` (consume `pretty_print`, never modify it, never reachable from the default REPL render path). Protects byte-identical-feature-OFF; the normal REPL already pretty-prints (no default-build work).
- **R2 — The ANSI-leak defect is int-internal; NO public color-mode parameter.** `/qa` repro + fix stay within int (`src/agent/` render + `src/style.rs`/`src/pretty.rs` wiring). Do NOT add a color-mode/writer-target arg to `pretty_print` or any `cranelisp-types` printer — the bug is double-styling/mis-routing, not a missing param (adding one = Principle-8 interim machinery for a wiring bug).
- **R3 — Build write arm reuses the existing `process_commands`/`eval` staging path; no new eval entry, no parallel submit path.** Widen the §4.2 allowlist in one place; validator reuses the `check_forms` discard-on-Err arm. Holds BC §6.3 + design §7.5 by construction.
- **R4 — No `cranelisp-types` change and no `CACHE_SCHEMA_VERSION` bump this sprint.** Document mode reuses the S88 `module_preamble` field + v9. If `/dev` finds it needs a new boundary type / cached-struct change in Phase 5, that is cross-crate → file `target: /arch` (none anticipated). Pins the zero-baseline-movement claim as a checkable Phase-5 gate.

**Public-API impact:** **zero baselines move.** `src/` is a binary (no baseline); `cranelisp-types` unchanged; `cranelisp-exe-bundle` untouched (agent never ships in `--link`/`--release`, NG4); all rung-5/6 + cluster-A render additions are `pub(crate)`, int-private, `#[cfg(feature="agent")]`.

### Phase-3 advisories
- **`/repl`** — cluster-A experience (`repl/spec.md §17`): agent-input prompt prefix (distinct glyph, normative), markdown rendering within the §10.3 agent-prose frame (degrades `--no-color`), fenced Lisp via the S24 printer; Build/Document UX (confirm-gate wording, consultative preamble-edit prompt) additive to §17.
- **`/dev (src/)`** — all three clusters serial. Build = widen §4.2 allowlist + route through `process_commands` (R3); validator = reuse `check_forms` discard-on-Err (no new seam); Document = `module_preamble` edit over `apply_module_preamble`+regen; cluster-A render in `src/agent/`, fully gated (R1); ANSI-leak fix = `style.rs`/`pretty.rs` wiring (R2). Keep feature-OFF byte-identical.
- **`/qa`** — agent lane behind `#[cfg(feature="agent")]`: stage→check→discard repair loop (Lane A, stub `AgentModel`), confirm-gated-write + allowlist-still-refuses-non-writes guard, Document round-trip, **cluster-A ANSI-leak narrow failing-not-ignored repro** (owed before closure). Plus 0429 close + delete. Default ~9s suite stays agent-free + byte-identical.
- **`/spec`** — **no language-semantics change this sprint** (module preambles §8.16 already landed S88). No action expected.

## Skill plans (Phase 3)

### `/design (src/)` — DONE (commit `a288870`; `design/int/agent.md §14–§19`)

**Task** (3 clusters, all honoring R1–R4):
- **Cluster A — agent output rendering (§14).** New `src/agent/render.rs` (agent-only, `#[cfg(feature="agent")]`, R1): (1) agent-input prompt prefix at the two agent-echo sites; (2) markdown→terminal within the §10.3 frame; (3) ```lisp fences → existing `pretty::pretty_print_str` (P7 reuse). DEFECT root-caused as a **style-once-at-the-leaf** wiring fix — NO color-mode param (R2).
- **Cluster B — Build + validator (§15/§16).** Confirm-gated `submit` write arm widened in one place (`run_pull` head); re-enters via `process_commands`/`eval` staging (R3, no new eval entry). `validate_forms_dry_run` reuses the `check_forms` discard-on-Err arm (`worker.rs:243`); silent-repair-anything (U5), capped, stub-drivable; `pub(crate)`, no facade delta.
- **Cluster C — Document mode (§17).** `apply_preamble_edit` over the S88 `module_preamble` field + byte-stable section-0 regen (`save.rs:96/308`); tool-name discriminates the consultative gate from the Build confirm. No `cranelisp-types` change, no cache bump (R4).

**Crate:** `src/`. **Design refs:** `design/int/agent.md §14–§19`; `repl-embedded-agent.md §6.2/§6.4/§7.1/§7.5/§9`; `repl/spec.md §17`. Seams: render `agent/mod.rs:234`,`style.rs:72/88/133`,`pretty.rs:33`,`repl.rs:966/1856`; Build `agent/pull.rs:29/72/96`,`main.rs:313-326`; validator `worker.rs:243-290`; Document `save.rs:96/308/326`.

**Acceptance (Phase-5 verify):** A — `/ask` answer with prose + ```lisp renders formatted prose + pretty-printed colored form, agent pulls show the agent prompt, no literal escape codes, `--no-color` clean (+`/qa` ANSI-leak repro §14.6). B — `/ask "define a function that doubles its argument"` → proposed `(defn …)`, on confirm submitted + always-≥-parses, broken generation silently repaired + never shown (Lane A §16.5); +neg unconfirmed/non-read tool never reaches `eval` (§15.4). C — agent writes a preamble, round-trips byte-identically, fresh-session harvester reads it back (§17.3/4). Gate (§18): zero baseline movement, no `cranelisp-types`/cache change, feature-OFF byte-identical.

**Coupling flagged for reconcile (→ `/repl`, `/qa`):** see §"Phase-3 coupling reconciliation" in Notes.

### `/repl` — DONE (commit `62a16b7`; `repl/spec.md §17.12–§17.15, §10.3`)

**Task** — agent Build/Document/render UX, four additive `[S89]` subsections settling the four `/design §19` points:
- **Cluster A:** new §10.3 "Agent-input prompt" role + **§17.12 glyph `agent>`** (distinct from `user>` and the `▌` prose gutter; at both agent-echo sites; `--no-color`→plain `agent>`). **§17.13** markdown formatted *inside* the prose frame via existing §10.3 roles; ```lisp via the pretty-printer; **normative §17.13.3: no literal ANSI escape ever appears, `--no-color` clean**.
- **Cluster B — §17.14:** confirm-gate — proposed form shown pretty-printed under `agent>`, then `submit this definition? [y/N]` (default-decline); accept→bound, decline→still unbound. **§17.14.3/.4:** silent validator; user NEVER sees a raw compiler error; give-up = single graceful prose apology, never submits.
- **Cluster C — §17.15:** consultative gate `record this as <module>'s preamble?` (distinct posture from Build confirm); shows exact text; accept writes durably (byte-stable), decline writes nothing. **§17.15.3 durable-memory promise.**

**Owned artifact:** `repl/spec.md` §10.3, §17.3/.9 cross-refs, new §17.12–§17.15 (all `[S89]`, additive). **Acceptance:** as `/design` clusters A/B/C above, at the experience level.

### `/qa` — DONE (commit `5cdc002`; `tests/plan/s89-test-plan.md`)

**Task:** Phase-3 test PLAN (no `.rs` yet — those land Phase 5 Stage 1, serial). 0429 residual closed (the §1 `agent-testing-strategy.md` correction applied; rig-trait mock + FIXME deletion owed Phase 5).

**Owned artifact:** `tests/plan/s89-test-plan.md` (+ `agent-testing-strategy.md §1` fix + `ledger.md` entry). **Design refs:** `design/int/agent.md §14–§19`; `agent-testing-strategy.md §3.4/§3.5/§6`; `repl/spec.md §17`.

**Acceptance (Phase-5 exit):** all rows RED-first → `/dev` flips green in-change-set with mandatory unit tests:
- **A** — A.1 ANSI-leak repro **failing-not-ignored** (RED on HEAD's leaking render, green on the §14.6 leaf-styling fix; R2 no color param); A.2 agent-prompt-on-pulls + markdown + `--no-color` + Lane-D golden transcript.
- **B** — B.1 stage→check→discard repair loop (stub broken-then-fixed; broken text never surfaces, fixed form submits, +neg user-never-sees-error); B.2 read-only floor +neg (unconfirmed/non-read tool never reaches `eval`); B.3 0429 rig-trait mock.
- **C** — C.1 write→save→reload→harvester-read-back byte-stable round-trip; B/C decline +neg.
- **Lane B** default ~9s suite stays agent-free + byte-identical. **Gate §18:** zero baseline movement, no `cranelisp-types`/cache change. **0429** fully closed when B.3 green → `/qa` deletes the FIXME.

**Testability seams required from `/dev`:** (1) **broken-then-fixed stub-script DSL** (`CRANELISP_AGENT_STUB_SCRIPT` must express turn-1-broken/later-clean); (2) a **hook to drive the validator repair loop** observably through the `AgentModel` membrane (zero network) so the broken intermediate's absence is assertable e2e — else an `/int` transcript/echo testability gap.

### Scope addition 3a — `--yes` autonomous-submit flag (design pass, 2026-06-22)

User-requested mid-plan; folded into Cluster B / Wave 2. Quick design pass (planning paused at Phase-4-complete, so no built code to rework):
- **`/arch` `93961e8` (`repl-embedded-agent.md §7.4`):** **POLICY KNOB, not a boundary change** — auto-*answers* the consent gate; R3 structural floor + the validator are untouched. Blanket (Build + Document). One-time first-use notice warranted (`/repl` owns wording). **Validation-floor invariant non-negotiable** — `--yes` skips *consent*, never *the validator*; flagged as a Phase-5 `/dev` guard + `/qa` test obligation. **Zero public-API/cross-crate impact.**
- **`/repl` (`repl/spec.md §0.6.2, §17.14.5/.6, §17.15.2a, §17.16`):** flag **`--yes` (`-y`)**; off by default; no-op on default builds / when no agent active; does NOT enable the agent or bypass opt-in-twice (pair `--agent` + `--yes`). Both gates auto-accept but the form/edit is **still shown** (`agent>` echo); decline path unreachable by design. **§17.16 one-time first-use notice** (autonomy-escalation disclosure, sibling to §17.8.1: agent acts *without asking*, user still sees every write, validator still gates correctness, "restart without `--yes`" to regain control). Normative: broken generation still silently repaired under `--yes`.
- **`/design (src/)` `0c11fcf` (`design/int/agent.md §20`):** `--yes`/`-y` parsed in `parse_args` (`main.rs:413`) beside `--agent`, threaded `run`→`enable_agent`(`lifecycle.rs:133`)→`build_agent_state`(`provider.rs:47`)→ new `AgentState.auto_accept` (`types.rs:132`). `agent_auto_accept()` short-circuits **only** the prompt-read at `run_submit` (§15.2) + `run_document_edit` (§17.2); render + downstream `process_commands`/`eval`/regen byte-identical. **§20.3 validation-floor guard:** `auto_accept` is read only at the consent site (after `validate_and_repair` returns `Ok`); the validator takes no `auto_accept` param → structurally unobservable to it. Once-flag `auto_accept_notice_shown` fires the first-use notice once/session.

### Phase-3 coupling reconciliation — CLOSED (no FIXME)

All four `/design (src/)` §19 points settled + agreed across `/design`+`/repl`: glyph `agent>` (`/design §14.2` fixes one prefix fn so the two echo sites can't diverge); Build confirm `submit this definition? [y/N]`; Document `record this as <module>'s preamble?`; validator give-up = graceful prose apology (U5). The two `/qa` testability seams (stub-script broken-then-fixed DSL; validator-repair-loop observation hook) are recorded as **Phase-5 `/dev` obligations**, folded into the Wave-2 `/dev` step. `/arch` confirmed interface set complete (zero delta). **Phase-3 exit gate MET → Phase 4.**

## Waves (Phase 4)

**ALL `/dev` work is `src/` source → STRICTLY SERIAL** (one source-editor at a time; broken worktree isolation). Each wave is a `/qa`(failing tests, RED-first) → `/dev`(impl + testability seams + mandatory unit tests, flips green) → `/review`(change-set vs design intent + R1–R4) cycle. Clusters are dependency-ordered: A is independent (warm-up, lowest-risk); B is the core write path; C builds on B's consent-gate machinery. Phase-5 entry baseline: default `cargo nextest run` **1516/1516, 0 intentional reds**; `--features agent` 33/33 lib + 23/23 e2e; feature-OFF byte-identical.

### Wave 1 — Cluster A: agent output rendering + ANSI-leak defect (src/, serial)

| Step | Skill | Crate | Task |
|---|---|---|---|
| 1q | /qa | tests | A.1 ANSI-leak narrow **failing-not-ignored** repro (RED on HEAD; `no literal \x1b[`); A.2 agent-input-prompt-on-pulls + markdown-formatted + `--no-color`-clean + Lane-D golden transcript (all `#[cfg(feature="agent")]`) |
| 1d | /dev | src/ | New `src/agent/render.rs` (agent-only, gated, R1): one prefix fn for the `agent>` glyph at both echo sites; markdown→frame; ```lisp→`pretty::pretty_print_str` (P7). **ANSI-leak fix = style-once-at-the-leaf** wiring in `style.rs`/`pretty.rs` (R2, NO color-mode param). Flips 1q green + unit tests. Bookkeeping: `/int` deletes resolved FIXME `0423`. |
| 1R | /review | all | Feature-OFF byte-identical; render strictly agent-only (no default render-path touch); leaf-styling root-cause confirmed; R1/R2 held; +neg complete |

**Wave 1 CLOSED ✅** — `/dev` `5a666c9` resolved the 1R Important + Suggestion: real `#[cfg(test)]` color-force seam in `style.rs` (proof-it-bites verified — orphan-SGR break fails the guard), `SpanKind: Copy`. Production color path byte-identical (seam is `#[cfg(test)]`). Final green: agent lane 29/29, lib lane 14/14, **default 1517/1517** (+1 agent-free style-seam test), warning-clean. Commits: `5592169` (1q) → `668b4d3` (1d) → `5a666c9` (1R-fix).

**1R DONE** (`/review`): **GATE-READY** (0 Blocker). R1/R2/feature-OFF/root-cause all PASS (candidate-(a) genuine; the 3 remaining bare `agent_prose` sites carry only int-authored plain notices → no parallel leak path; P7 reuse genuine; `agent>` one shared fn). **1 Important → resolve in-wave:** the §14.6 color-ON leaf guard (`render.rs:303`) is **vacuous** — `style::init_color` resolves via `is_terminal()` (false in the non-TTY test process), so color is OFF regardless and the "color-on" assertion holds trivially; `style.rs:88` `OnceLock` has no test override. Fix = a `#[cfg(test)]` color-force seam in `style.rs` so the guard genuinely exercises color-ON well-formed SGR (nextest = process-per-test ⇒ no cross-test race). **Suggestions:** derive `Copy` on `SpanKind` (drop ~6 lines manual rebuild, P7); heading-nested-SGR cosmetic (accept as-is).

**1d DONE** (`/dev`, `668b4d3`): `src/agent/render.rs` (new, agent-only, R1) — `render_agent_prose` (markdown→prose-frame + ```lisp→`pretty::pretty_print_str` reuse), one `agent_input_prefix()` `agent>` glyph fn at both echo sites (`mod.rs` Done-arm, `pull.rs` echo). **ANSI-leak root cause = candidate-(a) render layer** (Done-arm passed raw model markdown verbatim → fences survived); fix = **style-once-at-the-leaf** (no `pretty_print*`/`cranelisp-types` color param, R2). 8 render unit tests incl. mandatory §14.6 color-ON/OFF leaf guard. **6 RED→green** (`--features agent --test agent` 29/29); **default suite 1516/1516 agent-free**; warning-clean. No R1/R2 deviation.

**1q DONE** (`/qa`, `5592169`): 6 failing-not-ignored Cluster-A tests in `tests/agent.rs` (all `#[cfg(feature="agent")]`, stub-provider harness): `agent_output_no_literal_ansi_escape_when_color_off_neg` (A.1), `agent_output_lisp_fence_pretty_printed_styled`, `agent_issued_pull_shows_agent_prompt`, `agent_prose_markdown_formatted_for_terminal`, `agent_prose_markdown_no_color_clean_neg`, `agent_session_render_golden_transcript`. RED confirmed: `cargo nextest run --features agent --test agent` = 29 run, 23 pass, **6 RED** (these). Default build agent-free (`cargo check` clean). **Testability split (→ 1d obligation):** the color-ON `\x1b[` leak (§14.6 candidate-b) is NOT e2e-reproducible (harness pipes stdout ⇒ color auto-off; no `--color=force`, `repl/spec.md §10.7`); the e2e A.1 pins the color-OFF half (raw fence → plain-indented Lisp). **`/dev` 1d MUST add the mandatory unit test in `src/agent/render.rs`** (`render_agent_prose` over a ```lisp fence: no literal `\x1b` color-off, well-formed SGR color-on, §14.6) — the one seam where the color-ON leak surfaces.

### Wave 2 — Cluster B: Build mode + pre-flight validator (src/, serial) — the safety-critical wave

| Step | Skill | Crate | Task |
|---|---|---|---|
| 2q | /qa | tests | B.1 stage→check→discard repair loop (stub **broken-then-fixed**; broken text never surfaces, fixed form submits, +neg user-never-sees-error); B.2 read-only-floor +neg (unconfirmed/non-read tool never reaches `eval`); B.3 0429 rig-trait `MockModel`. **+ `--yes` (3a):** B.4 **validation-floor-under-`--yes`** (broken generation still silently repaired with `--yes` on, only clean form committed, no `[y/N]`); B.5 `--yes` accepted-no-op on default build / `--no-agent` / `--run`-`--link`. *(/qa appends these rows to `s89-test-plan.md` when authoring.)* |
| 2d | /dev | src/ | Confirm-gated `submit` write arm widened **in one place** at `run_pull` head → `process_commands`/`eval` staging (R3, no new eval entry); `validate_forms_dry_run` reuses the `check_forms` discard-on-Err arm (`worker.rs:243`), silent-repair-anything (U5), capped; **+ the 2 `/qa` testability seams** (broken-then-fixed stub-script DSL; validator-repair observation hook). **+ `--yes` (§20):** parse `--yes`/`-y` (`main.rs:413`) + `AgentState.auto_accept` threaded; `agent_auto_accept()` short-circuits ONLY the consent prompt-read (never the validator — §20.3 guard); once-flag first-use notice. Flips 2q (incl. B.4/B.5) green + unit tests |
| 2R | /review | all | Read-only floor still structural (writes unconstructable without confirm); validator `pub(crate)`/no facade delta; cap + give-up correct; **`--yes` reads only at the consent site, validator unobservable to it (§20.3)**; R3/R4 held; feature-OFF byte-identical |

**2R DONE** (`/review`): **GATE-READY** (0 Blocker, 0 Important). Safety-floor STRUCTURAL (`synthesize_command` byte-unchanged + still refuses `submit`; one widening at `run_pull:111`; write reaches `eval` only past consent-or-`--yes`); **§20.3 structural + non-vacuous** (validator fns take no `auto_accept` param/read; `auto_accept_reader_reads_field_validator_unaffected` validates a broken form with `--yes` ON → still errs, never commits); R3 (existing `process_commands`→`eval`→regen, no new entry) + R4 held; contract evolution legitimate (`write_command_refused` floor preserved; keystone non-vacuous — asserts `(double 5)`→10 + no error text). **Suggestions (deferred, /dev's own code — noted not FIXME'd):** S1 repair loop doesn't record the model's repair response as an assistant turn (transcript fidelity, cap=3 bounds it); S2 `extract_form_from_prose` byte-paren-match ignores strings/comments (validator catches; submit uses tool-call not prose); S3 `submit` discriminator at 2 sites (below Principle-6 threshold). **Bare-unknown-under-agent test → `/qa` cleanup** (not a blocker): make agent-aware (S88 U1 routes bare-unknown→agent).

**Wave 2 CLOSED ✅** — GATE-READY; cleanup `a21ec3b`: `bare_primitive_unknown_name_*` split (`#[cfg(not(feature=agent))]` keeps default "undefined" assertion + `#[cfg(feature=agent)]` `bare_primitive_unknown_name_routes_to_agent` per U1) → `repl_introspection` 138/138 BOTH builds; **0429 closed + FIXME deleted** (`continuation_request_pairs_tool_use_before_tool_result` green; `agent-testing-strategy.md §1.1` reconciled to the `AgentModel` membrane). Commits: `3900c7b` (2q) → `843c596` (2d) → `a21ec3b` (cleanup). **0423 still on disk — owed `/int` to delete** (S88-resolved; green `inline_mod_test_extraction_writes_lib_dir_relative_not_cwd` is the record).

**2d DONE** (`/dev`, `843c596`): **§15** `submit` write arm — one allowlist widening at `run_pull` head (`run_submit`→`submit_clean_form`→ existing `process_commands`/`eval`/regen staging, R3 no new eval entry); `submit` always in `tool_defs()` but always confirm-gated (non-`submit` writes still refused at `synthesize_command`, B.2 floor). **§16** `worker::validate_forms_dry_run` reuses `process_cluster_with_staging`+`check_forms` **minus commit** (always discards); `validate_and_repair` silent-repair-anything (U5, any Err, no classification), **cap 3** + graceful give-up (never raw error/broken submit). **§20** `--yes`/`-y` parsed in recognized-flag arm (fixed `-y` trap), accepted-no-op default build; `AgentState.auto_accept`; first-use notice once-flag. **§20.3 enforced:** validator fns take no `auto_accept` param/read-path — proven by `auto_accept_reader_reads_field_validator_unaffected` + B.4. **Green:** agent lane 37/37, unit 50/50, **default 1519/1519**, warning-clean. **Contract evolution (→ 2R):** 2 S88 unit tests updated (`tool_defs_are_read_only`→`_plus_submit`) since `submit` is now always-offered-but-gated. **Flagged pre-existing (→ 2R/`/qa`):** `repl_introspection.rs::bare_primitive_unknown_name_produces_undefined_error_neg` fails **under `--features agent`** (failing on `3900c7b`, pre-2d) — S88 U1 routes bare-unknown→agent so no "undefined" error in the agent build; the test asserts default-build behavior + needs to be agent-aware. Default suite unaffected.

**2q DONE** (`/qa`, `3900c7b`): 8 tests in `tests/agent.rs` (+`s89-test-plan.md §B`/ledger). **RED:** B.1 `agent_build_broken_then_fixed_repaired_silently` (keystone), B.4 `agent_build_yes_validation_floor_still_repairs` (CRITICAL), B.5 `agent_yes_with_no_agent_is_accepted_no_op` + `yes_flag_accepted_no_op_default_build` + `y_short_flag_accepted_no_op_default_build` (last 2 default-lane). **Standing-green floor:** B.2 declined-submit-no-change + non-read-tool-refused. **B.3** 0429 `continuation_request_pairs_tool_use_before_tool_result` confirmed green (not duplicated). Agent lane 37 run/5 RED; default 1519/2 RED (B.5 default only). **DSL contract for 2d (verbatim):** new `tool: submit <FORM>` (rest-of-line = form); broken-then-fixed = **two consecutive `tool: submit` lines** (Nth = Nth repair attempt), no new keyword. **2d traps flagged:** (a) `submit` currently refused at `synthesize_command` (no write arm); (b) B.4 pipes no `y` (relies on `--yes` auto-accept); (c) **`-y` false-green trap** — today `-y` falls to the REPL-target `_` arm (`-y>` prompt) so a naïve unknown-flag check passes; 2d must add `-y`/`--yes` to the recognized-flag arm, not the target capture.

**0429 closes here:** B.3 green → `/qa` deletes `design/arch/fixmes/0429-*.md`.

### Wave 3 — Cluster C: Document mode (src/, serial)

| Step | Skill | Crate | Task |
|---|---|---|---|
| 3q | /qa | tests | C.1 write→save→reload→**harvester-read-back** byte-stable round-trip; B/C consent decline +neg |
| 3d | /dev | src/ | `apply_preamble_edit` over the S88 `module_preamble` field + byte-stable section-0 regen (`save.rs:96/308`); tool-name (`set-preamble`/`set-doc` vs `submit`) discriminates consultative gate from Build confirm. No `cranelisp-types`/cache change (R4). Flips 3q green + unit tests |
| 3R | /review | all | Round-trip byte-stable; harvest read-back; R4 held (zero baseline movement re-verified); feature-OFF byte-identical |

**Wave 3 CLOSED ✅ / PHASE 5 COMPLETE** — 3R re-review **GATE-READY** (no findings; anti-masking GENUINE — the 5 converted routing tests drive active stubs + assert the real `▌` frame, the 3 dormant tests assert today's display; two distinct meaningful populations). set-doc Blocker + classifier-class root both resolved. Commits: `a991fde` (3q) → `88f21df` (3d) → `4bb4cd0` (3R-fix). Minor carry: stale `set-doc` mention in a `tests/agent.rs` DSL-doc comment (harmless, `/qa` cleanup). **Phase-5 final green: agent lane 41/41, `--features agent` 1602/1602, default `cargo nextest run` 1519/1519, both `cargo check` warning-clean.**

**3R-fix DONE** (`/dev`, `4bb4cd0`): **(1)** `set-doc` fully descoped (const/routing/`apply_docstring_edit`/`tool_defs`/stub-parse/unit-tests removed; `set-preamble` keystone intact); **FIXME 0430** filed (`target: /design`, docstring-into-source regen). **(2)** classifier dormant fall-through per `/arch` `e3f7d57`: new `agent_is_active()` (= `Some && !is_dormant()`; `enable_agent` always sets `Some` even when `--agent` off, so `is_dormant()` is the right predicate) gates the `Classify::Agent` divert at `main.rs:322`; dormant/off ⇒ today's display; `/ask` door keeps its U6 notice. **Tests:** un-gated `bare_primitive_unknown_name_produces_undefined_error_neg` (green both builds); `bare_primitive_unknown_name_routes_to_agent` + **4 more `tests/agent.rs` routing tests** converted to **active stub** (active⇒route, ruling-consistent — `/qa`-owned, flagged for re-review). **Green:** agent lane 41/41, **`--features agent` 1602/1602** (3 dormant tests now green), default 1519/1519, warning-clean (3 pre-existing `main.rs` clippy). → **3R re-review** pending.

**3R DONE** (`/review`): **CHANGES-REQUESTED.** Preamble keystone sound (round-trip inverse-pair holds; `render_preamble_block` genuine P7 window on `generate_preamble`; R4 + feature-OFF confirmed). **Blocker (1):** `set-doc` non-persisting — `apply_docstring_edit` sets live `Def.docstring` but `save::generate_fns_and_macros` re-renders from stored sexp, never reads the field → docstring vanishes on restart, silently breaking §17.15.3. **Disposition: descope `set-doc` this wave** (owner `/dev`) + **FIXME `target: /design`** for docstring-into-source regen (real design Q: docstring-aware `render_decl_sexp` or sexp re-injection). **Important (2) — recurring classifier class (3rd instance):** root = `main.rs:316` routes `Classify::Agent` whenever `feature=agent` compiled-in, no guard on agent runtime-active; dormant ⇒ U6 notice instead of today's parse-error/undefined. **Disposition: escalate `/arch`** (dormant-fallback design Q, §17.1/U1) — NOT per-test gating; note Wave-2 `bare_primitive_unknown_name_routes_to_agent` must then run against an **active stub** (active⇒route, dormant⇒fall through). **Suggestions:** `resolve_document_module` non-current target writes an unpersisted table (MVP shape OK; guard/note); harvest preamble-format near-dup at 2 sites (below rule-of-3).

**3d DONE** (`/dev`, `88f21df`): `set-preamble`/`set-doc` routed at `run_pull` head beside `submit` → `run_document_edit` consultative gate (distinct wording, out of read-only allowlist); `apply_preamble_edit` sets `module_preamble` + byte-stable regen via `render_preamble_block` (window onto existing `generate_preamble` — P7, no second emitter); harvester current-module pin now emits `module_preamble` (closes write→read loop); **`/doc <module>` implemented** (small clean addition, §17.5.1). **Green:** agent lane 41/41, unit 413/413, **default 1519/1519** agent-free, warning-clean. R4 honored (no `cranelisp-types`/cache change). **2 flags → 3R:** (1) **`set-doc` persistence gap** — sets live docstring + regen, but regen emits def source from introspection not the entry docstring, so a `set-doc` docstring is NOT round-tripped into source (no test requires it; preamble keystone persists fine); (2) **recurring parse-error-under-`--features agent` class** — `repl_negative.rs::{parse_error_stray_close, parse_error_has_location}` fail under agent build (same U1-routing root as the Wave-2 bare-unknown test; 2nd+3rd instance → root-cause/escalate, not per-test gating).

**3q DONE** (`/qa`, `a991fde`): 4 tests in `tests/agent.rs`. **RED:** `agent_document_preamble_edit_round_trips_byte_stable` (C.1 keystone), `agent_document_harvester_reads_edited_preamble_back` (C.1 read-back via fresh `run_again()` + `/context` harvest), `agent_document_yes_auto_accepts_preamble_edit` (C.3). **Standing floor:** `agent_document_declined_preamble_edit_no_change_neg` (C.2, passes today — unknown tool refused). Agent lane 41 run/3 RED; default 1519/1519. **DSL contract for 3d (verbatim):** `tool: set-preamble <MODULE> <TEXT>` (split on first ws: module + stripped prose, NO `;;`) → `apply_preamble_edit`+regen; `tool: set-doc <SYMBOL> <TEXT>` → docstring; both tool-name-discriminated from `submit` (consultative gate, absent from read-only `ALLOWLIST`). **Read-back seam:** `/context` dump `=== HARVESTED CONTEXT ===`. **3d gap flagged:** `/doc <module>` unimplemented (`repl.rs:682` `handle_doc` resolves only symbols, §17.5.1/§8.16.4) — 3d implements it OR relies on `/context` (tests use `/context`).

### Wave 4 — Phase 6 (user-facing) — assessment + action

| Step | Skill | Task |
|---|---|---|
| 4a (6a) | /repl, /port | Assess the *delivered* agent against `repl/spec.md §17`; file gap FIXMEs if any. `/port` may exercise the Build/Document agent against the exemplar (optional, surfaces adequacy gaps via the user-proxy protocol) |
| 4b (6b) | /repl | New S89 demo: the Build/Document/render experience (agent submits a confirmed `(defn …)`, records a preamble, renders a formatted answer). All prior demos + the exemplar replay green (regression guard) |

*(Phase-5 Stage-1 "sprint-wide QA-first" is honored by the complete Phase-3 test PLAN; the actual `.rs` failing tests are authored per-wave because B.1 depends on the stub-script DSL seam `/dev` adds in 2d.)*

## Notes

- 2026-06-22: S88 closed (`5833bd1`/`3696931`/`d1d2e30`/`523eb9b`; archived `sprint-88.md`; ROADMAP updated). S89 opened as the next agentic-REPL increment (rungs 5–6) per ROADMAP §"Agentic-REPL track".
- Phase-1 scope draft authored. `claude-oauth` provider dropped (user: "not a feature").
- 2026-06-22: User added an **agent output rendering** cluster from live S88 use — agent inputs need a prompt; markdown should be formatted; ```lisp blocks should be pretty-printed (reuse S24 printer); + a DEFECT (pretty-printer leaks raw ANSI codes on agent output → `/qa` repro owed). Folded in as a [core] stage. `/repl` + `/dev (src/)` + `/qa`.
- **Scope APPROVED (user, 2026-06-22):** full rungs 5+6 (Build mode + validator AND Document mode) + the agent output rendering cluster. → Phase 2 (Arch review).
- **Phase 2 /arch verdict (2026-06-22): APPROVE** (clean — zero new cross-crate edges, zero baselines move, zero `cranelisp-types` change). R1–R4 applied to scope; one doc-currency edit `3630b69`. → Phase 3 DESIGN.
- **Phase 3 DONE (2026-06-22):** `/design (src/)` `a288870` (`agent.md §14–§19`, anchor) → `/repl` `62a16b7` (`spec.md §17.12–17.15`) + `/qa` `5cdc002` (`s89-test-plan.md`, parallel, disjoint trees). Coupling fully reconciled, no FIXME. Exit gate MET. → Phase 4.
- **Phase 4 DONE (2026-06-22):** 3 dependency-ordered implementation waves (A render+defect → B Build+validator → C Document) + Wave 4 (Phase 6 user-facing), all `/dev` serial-source. Plan complete (Phases 1–4). **Holding before Phase 5 (implementation) pending user go-ahead.**
- **Scope addition `--yes` (user, 2026-06-22), post-Phase-4:** autonomous-submit flag folded into Cluster B / Wave 2. Design pass done: `/arch` `93961e8` (policy-knob ruling, validation-floor invariant), `/repl` (`§0.6.2/§17.14.5-6/§17.15.2a/§17.16`), `/design (src/)` `0c11fcf` (`agent.md §20`). Zero public-API impact; no re-org of waves. Still holding before Phase 5.

## Phase 6 (user-facing)

**Live smoke #1 (user, 2026-06-22) → DEFECT found + fixed.** User ran `write me a fibonacci fn in this module`; the agent **proposed + said "copy the form above and submit it"** instead of issuing a confirm-gated `submit`, and the Lisp rendered with the model's raw indentation (not pretty-printed). **Root cause:** `src/agent/primer.txt` still carried the **S88 READ-ONLY framing** ("you cannot submit … show it as a code form for the user to copy") — the S89 `submit`/`set-preamble` tools were offered (`pull.rs:94/103`) but the primer told the model not to use them, and never instructed the ```lisp fence convention. The scripted-stub tests passed green because the stub *scripts* `tool: submit` — they never tested whether the live model is *instructed* to. **Fix** (`/dev`, `05c0d45`): primer rewritten — model now told it can ADVISE and ACT (use `submit` for define/add/write requests; `set-preamble` for docs; fence multi-line code as ```lisp), matched to the `tool_defs` descriptions; **4 regression unit tests** assert the primer is Build-capable + ```lisp-instructing + free of the stale read-only strings. Green: agent lane 41/41, default 1519/1519. **→ user re-smoke live to confirm Build mode now fires.**

**Finding (methodology — extends the S88 lesson):** the always-on **primer is part of the feature surface**, and a scripted-stub test cannot validate that the **live model is instructed to use a capability** (the stub emits the tool-call regardless of the prompt). A capability is only delivered when BOTH the plumbing (stub-tested, Lane A) AND the model-instruction (primer-content assertion, Lane A + a live Lane-C smoke) are in place. The headline Build/Document capability passed every green test while being live-inert. `/qa` to fold the primer-content-guard pattern into `tests/plan/agent-testing-strategy.md` at close.

## Outcome (Phase 7)

*(Pending — Phase 7.)*
