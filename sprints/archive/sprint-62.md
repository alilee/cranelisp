# Sprint 62: Concurrency Control — Audit, Risk Management, Test Strategy

**Status**: COMPLETE (closed mid-sprint 2026-04-25 — methodology pivot per `sprints/METHOD_PROPOSED.md`)

**Ring**: 4 (Effects — stabilisation continuation)

**Goal**: Produce the design artefacts that let us *gain and maintain control* over concurrency in the v4 scheduler + typecheck shared state. **Pure analysis + strategy sprint** — three documents land, no implementation. This sprint fixes no races, writes no loom code, writes no structured-interleaving tests. It produces the inventory, the risk register, and the test strategy that make subsequent sprints' race-closure work evidence-gated and verifiable.

## Scope

Sprint 61's methodology pivot retired stress-run verification as primary proof of race closure. Before replacement infrastructure (loom, structured interleaving tests) can be adopted responsibly, three prerequisite questions must be answered:

1. **What shared state exists?** — without an exhaustive inventory, any closure claim is scoped to what we happened to notice.
2. **What can fail, and how would we know?** — without a ranked risk register, investigation is reactive (chase the next heisenbug) rather than proactive (close the highest-likelihood + highest-blast-radius sites first).
3. **How do we gain and maintain control?** — without a test strategy decision, the team re-litigates "loom vs stress vs barriers" per defect and the project accumulates inconsistent approaches.

S62 answers all three by producing three design documents. Implementation of the strategy (loom adoption, structured tests, H6 residue closure) carries to S63+ gated on these documents landing and `/arch` approving the strategy.

### Three workstreams → three documents

1. **Audit** — `design/int/concurrency-audit.md` (co-authored by `/int` and `/typecheck`; see §Skill Plans for the section split)
   - Enumerate every shared-state access site across the following surfaces (extended per /arch Phase 2 §1):
     - `crates/cranelisp-typecheck/` — modules, symbol_tables, impl_registry, any DashMap/Mutex fields (`/typecheck`-authored section)
     - `src/scheduler.rs` — all `SchedulerState` fields, pool transitions, condvar patterns (`/int`-authored)
     - `src/worker.rs` — handle_import, register_dep, priority-worker claim loop, cache-writer path (`.meta.json`/`.o` writer), `OnceLock<TraceFilter>` env-var parse-once site (`/int`-authored)
     - `src/session_v4.rs` — register_dep_for_eval, wait_module_inmem_complete_blocking, SharedState access, any `Arc<T>` cloned into worker threads (`/int`-authored)
     - `crates/cranelisp-runtime/src/trace.rs` — IO trace ring buffer, `OnceLock<TraceFilter>` env-var parse-once site (`/int`-authored with `/backend` review)
   - **Entry addressing (durability per /arch Phase 2 §2, R1)**: each entry keys on `{module-path, field-name}` with line numbers recorded as "verified-at-SHA `xxx`" annotation, not as the primary key. Same discipline as `tests/plan/baseline.md`.
   - **Per-entry columns**: `{module-path, field-name}`, verified-at-SHA, operation, lock held (if any), **classification** (one of: `atomic-by-construction` / `under-lock-L` / `published-then-read` / `invariant-unclear`), invariant required, reachability-per-reader-class (scheduler / priority worker / nice worker / REPL eval — separate rows when invariant differs per reader), grep-match signature for the H6 non-atomic-check-then-insert pattern (yes/no), current implementation status.
   - Exhaustive — not illustrative. The audit is the inventory from which every downstream decision draws.

2. **Risk register** — `design/int/concurrency-risks.md` (authored by `/int` + `/arch`)
   - Ranked list of risks derived from the audit. **Three-tier lexicographic ranking (per /arch Phase 2 §5 — replaces multiplicative `likelihood × blast-radius`)**:
     - **Tier 1 — Observed**: a committed failing test reproduces the race. H6 residue at `sprint23::heisenbug_race_reduced_concurrent_import_pairs` qualifies; harness ceiling at `io_trace_off_path_*_generous_ceiling` qualifies by the same evidence bar (its mechanism is not a race but the observation discipline is identical).
     - **Tier 2 — Suspected by pattern**: audit entry matches a known-fires pattern — non-atomic check-then-insert (H6 shape), publish-after-register, condvar-without-seqlock.
     - **Tier 3 — Unknown surface**: audit-marked `invariant-unclear` — every such audit entry becomes a Tier-3 risk register row automatically (per §4 completeness criterion; no ratio budgeting).
   - Within each tier, order by blast radius: process-abort > wrong-result > spurious-error > diagnostic-only.
   - Per-risk fields: tier classification, audit-entry stable key, detection signal, blast radius, mitigation plan reference, owning sprint for closure.
   - `/arch` approves rankings; the register becomes the S63+ backlog driver (Tier 1 first, then Tier 2, then Tier 3 budgeted against other scope).

3. **Test strategy** — `design/int/concurrency-test-strategy.md` (authored by `/qa` + `/int`; reviewed by `/arch`)
   - Decision document answering "how do we gain and maintain control":
     - **Framework-scoring worksheet (per /arch Phase 2 R3)**: score every Tier-1 and Tier-2 risk-register entry against each candidate framework (`loom`, `shuttle`, `miri`, structured-interleaving-only) on four axes: (a) handles atomic orderings?, (b) handles DashMap?, (c) CI wall-clock cost multiplier, (d) can a skill without the tool run the test?. Framework choice is justified against the worksheet, not as a consensus vote. Document the chosen framework by capability ("bounded-permutation model checker") with the concrete pick as implementation detail, so a framework change later does not rewrite the doc.
     - **Candidacy matrix**: per audit site, whether it admits bounded-interleaving verification, exceeds practical depth, or requires a shim. One-way-door assessment per `/arch` Principle 8 — document reversibility costs (see /arch Phase 2 §6: lock-in is methodological, not structural).
     - **Structured interleaving pattern**: the `std::sync::Barrier` + atomic phase-marker template, with worked examples for **at least three distinct audit sites** — one atomic-ordering case, one lock-protected-invariant case, one DashMap case. Skeletons must typecheck in the real workspace (not pseudocode).
     - **Stress-run role**: formal downgrade to weak regression guard. Precise language: *"Stress runs are retained as weak regression guards; `/sprint` MAY run them; they are NEVER sufficient closure proof per se."* — matching S61 close wording. Include the statistical-power note (N-run 0/N gate proves failure rate `<1/N` with ~63% confidence, not absence).
     - **CI integration**: when loom/shuttle/miri runs, when stress runs, on-push vs on-PR vs nightly cadence, cost budget.
     - **Audit-refresh cadence**: new shared-state sites trigger audit updates — new file matching `Arc<T>|Mutex<T>|RwLock<T>|DashMap<_,_>|AtomicX|OnceLock<T>` grep pattern, new `#[derive]` of a shared-state container on a boundary type, diff detection on the field enumeration.
     - **Maintenance rule**: protocol for classifying a new site (four-label assignment + invariant statement + reachability-per-reader-class rows) before it lands.

### Out of scope — explicit deferrals (user-approved 2026-04-22)

| Item | Carried to | Rationale |
|---|---|---|
| Loom adoption (actual code) | S63 | Strategy doc must land first and gate choice of framework |
| Structured interleaving tests (actual code) | S63 | Same — template must be approved before instantiation |
| H6 residue closure (the 5-10% failure rate) | S63+ per risk register ranking | Fix depends on audit findings; chasing without audit is the methodology S62 retires |
| **Defect 6 exemplar stack overflow (5 carries, 3× deferred)** | **S63 — user-approved deferral 2026-04-22** | Orthogonal to concurrency. Explicit user sign-off per 3× escalation rule. |
| Harness ceiling (`io_trace_off_path_*_generous_ceiling`) | S63 | Not concurrency-domain; /qa cleanup slot |
| S61 /review Importants (Mutex hedge, test helper consolidation, counter_non_zero) | S63 | All implementation; out of pure-design scope |
| FQTypeName migration | S63+ | Per methodology pivot (S61 close) |
| Performance baseline | S63+ | Unchanged from prior plans |
| Stdlib prelude monolith | S63+ | Unchanged |
| Phase H / Tier 2 release backend | Post-Ring-4 | Unchanged |

### Showcase waived (user-approved 2026-04-22)

The cardinal rule "it's not done unless a user can use it" is explicitly waived for S62. This is a pure design sprint with no user-visible change. No new `repl/demos/*.demo` file is required. Prior demos are still verified to replay green at close (regression guard on prior sprints' deliverables).

### Precondition gates (all satisfied)

- Sprint 61 committed (all five waves: `b140ec5`, `35062ca`, `776a6cf`, `e20a7fa`, `dbe4bac`, close-prep `00fdf4a`, archive `f22dd2d`).
- Sprint 61 archived to `sprints/archive/sprint-61.md` and ROADMAP updated.
- User approval to open S62 with narrowed scope (2026-04-22).

## FIXME Debt

Phase 1 scan across the S62 target surface (`crates/cranelisp-typecheck/`, `src/scheduler.rs`, `src/worker.rs`, `src/session_v4.rs`) surfaced exactly one FIXME — the intentional narrow-precedent marker installed by S61.

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `crates/cranelisp-typecheck/src/checker.rs:205` | `/typecheck` | S61 H6 narrow-precedent hybrid ownership — /int implemented `ensure_module_exists` under /typecheck's auspices; formal ownership handoff pending | **Disposition framework pre-committed by /arch Phase 2 §10; /typecheck picks A/B/C during audit; /arch ratifies at Wave-1 gate**: <br> • **Option A — take formal ownership**: accept only if the audit finds `TypeCheckEnv` is the natural home for the concurrency invariant. /typecheck owns the invariant going forward; FIXME removed. <br> • **Option B — ratify narrow precedent**: add a numbered Decision to `design/arch/CLAUDE.md` documenting the long-lived cross-skill arrangement; FIXME removed; comment updated to cite the Decision. Long-lived cross-skill arrangements live in the design book, not in a code comment. <br> • **Option C — defer with concrete plan**: must name a target sprint AND a named owning skill. No open-ended deferral. <br> No in-sprint code change beyond the one-line FIXME removal if A or B is chosen; the ownership decision is recorded in the audit document regardless. |

**Out-of-scope FIXMEs carried forward** (noted, not addressed — all off the concurrency surface):

- `FIXME(/backend)` at `crates/cranelisp-runtime/src/io.rs:28` — Ring 2 RC migration continuation.
- `FIXME(/stdlib)` at `stdlib/plan-stdlib.md §3.2` — prelude monolith.
- 26 `FIXME(/qa)` in `tests/plan/ring4.md` — ongoing test-plan hygiene.
- Several `FIXME(/arch)`, `FIXME(/frontend)`, `FIXME(/typecheck)` across design docs.

## Baseline ledger carry-forward (7 entries)

All 7 S61-carried failures remain in the ledger at S62 open. None are resolved in S62 (no implementation). Target sprints update to S63+ per the deferral approvals above; the updates are authored by `/qa` during Slice 3.

| Test | Carried to | Rationale |
|---|---|---|
| `sprint23::heisenbug_race_reduced_concurrent_import_pairs` | S63 | Fix scheduled per risk register ranking |
| `sprint61_observability_io::io_trace_off_path_*_generous_ceiling` | S63 | /qa cleanup |
| 4× `sprint59_defects456_repro::d6_exemplar_*` | S63 | Defect 6 — user-approved 3×-deferral extension |
| `wave6_demo_repros::exemplar_solver_*` | S63 | Defect 6 end-to-end entry |

## Architecture Review

**Reviewer**: `/arch`
**Date**: 2026-04-22
**Verdict**: APPROVE WITH REVISIONS (revisions applied in-place 2026-04-22)

### 1. Technical coherence

The three-document decomposition (Audit → Risk Register → Test Strategy) is the correct shape. It mirrors the evidence-gated discipline that worked in S61 (`design/int/heisenbug-race-closure.md` §6): inventory, then hypothesis ranking, then verification strategy. The dependency between documents is linear and each output is the next's input — a skill reading only the three documents can begin S63 implementation without re-opening strategy debates, provided the revisions below are adopted. The Scope §1–3 framing (what exists / what can fail / how we control it) is well-posed.

One coherence gap: the proposal lists four target files for the audit (§Scope item 1) but the `cranelisp-runtime` IO trampoline trace state (`crates/cranelisp-runtime/src/trace.rs`) and the cache-writer thread state (referenced in S61 Wave 3 step 3f's "`.meta.json` write failed" stderr noise) are concurrency surfaces too. `/backend`'s review role (§Skill Plans) is too thin to discover these by inspection alone. The audit surface list must be pre-extended, not left to /backend's review pass.

### 2. No interim architecture (Principle 8)

The three documents are durable artefacts under one condition: the audit must use a file-and-symbol addressing scheme that survives crate reorganisation (e.g., addressing by `FQSymbol` + invariant, not by `src/scheduler.rs:412`). Line numbers drift every wave; an audit that reads "scheduler.rs:412 holds `state_mutex`" is interim. Recommend: each audit entry keys on `{module-path, field-name}` with line numbers as a "verified-at-SHA" annotation — same discipline as baseline.md.

The risk register is durable if rankings cite audit entries by stable key. The test strategy is durable if it names the chosen framework by capability (bounded-permutation model checker) with the concrete choice (loom/shuttle/miri) as an implementation detail inside the doc, not as the header. Otherwise replacing loom with shuttle later rewrites the doc.

### 3. Design references

Correct references cited in skill plans. Missing:

- `design/arch/CLAUDE.md` Decision 30 (form-by-form scheduler deadlocks on mutual imports) is directly relevant — the audit must flag mutual-import deadlock as a known architectural constraint, not a race.
- Decision 31 (per-redefinition JIT reclaim) touches `SharedState` fields — audit surface.
- `design/int/concurrent-pipeline.md` §7 (scheduler properties) — the test strategy must preserve the §7.1 assertions, not contradict them.
- `memory/feedback_failing_not_ignored.md` — already in /qa's refs; should also appear in the test strategy's own reference list since it constrains the stress-run downgrade wording.

### 4. Audit completeness criterion

The proposed "every field has an entry; every entry has non-empty invariant; invariant-unclear ≤ 15%" is too soft. 15% unclear means up to one-in-seven sites have no proved invariant — that is precisely the H6-residue posture S61 is exiting. Revised criterion:

- **Completeness**: 100% of fields typed `Arc<T>`, `Mutex<T>`, `RwLock<T>`, `DashMap<_,_>`, `AtomicX`, or `OnceLock<T>` in the target crates have an entry. (A mechanical grep of these types defines the denominator; two reviewers classifying the same site disagree only if the grep disagrees.)
- **Classification**: every entry carries one of four labels — `atomic-by-construction`, `under-lock-L`, `published-then-read`, `invariant-unclear`. The last label is permitted but each such entry becomes a Risk Register "Tier 3 — Unknown surface" entry automatically — no budgeting by ratio.
- **Reachability**: `Arc<T>` cloned into worker threads requires a separate entry per reader thread class (scheduler / priority worker / nice worker / REPL eval) if the field's invariant differs by reader. Single-entry-per-field is insufficient for state read by mutually-racing consumers.

The 15% threshold is dropped. Every unclear entry is a Risk Register row; the register ranks them; some tier down to "long-lived known unknown" at /arch approval.

### 5. Risk register ranking methodology

`likelihood × blast-radius` is arithmetic that invites spurious precision on estimates neither dimension supports quantitatively. **Lexicographic tiers** adopted:

1. **Tier 1 — Observed**: a committed failing test reproduces the race (H6 residue qualifies; harness ceiling qualifies by the same evidence bar though its mechanism is not a race).
2. **Tier 2 — Suspected by pattern**: audit entry matches a known-fires pattern (non-atomic check-then-insert; publish-after-register; condvar-without-seqlock).
3. **Tier 3 — Unknown surface**: audit-marked `invariant-unclear`; no observed fire, no suspicious pattern.

Within each tier, order by blast radius (process-abort > wrong-result > spurious-error > diagnostic-only). S63+ addresses Tier 1 first, then Tier 2, then budgets Tier 3 work against other sprint scope. This matches how S61 H4→H5→H6 actually proceeded — evidence drove ranking.

### 6. Test strategy one-way-door assessment

Loom adoption is **semi-reversible**: the loom-specific test code carries a `#[cfg(loom)]` annotation and loom-wrapped `std::sync` primitives. Removing loom costs the tests authored under it (they must be rewritten against real primitives or deleted) but does not contaminate production code. Shuttle is similarly scoped. Miri's concurrency mode attaches to any test.

The lock-in is **methodological**, not structural: once the team has loom literacy and the CI job, switching frameworks is a multi-week effort even though the code surface is small. That is the reversibility cost to name in the strategy doc.

Decision framework (for the doc to apply, not for /arch to pre-decide):

- **Does it handle atomic orderings?** Loom yes, shuttle partial, miri yes.
- **Does it handle DashMap?** Loom no (would need shim); shuttle similarly; miri yes but scales poorly.
- **Can CI afford it?** Loom: 10–30× test wall-clock for covered tests; shuttle: 2–10×; miri: 10–100×.
- **Can a skill without the tool run the test?** Loom/shuttle require the dev-dep; miri requires nightly.

The strategy doc must score each audit-derived test site against this framework and justify the overall pick.

### 7. S63 handoff brief requirements

The test strategy doc must, at minimum:

- Name the chosen framework (one) and its version.
- Score every Risk Register Tier-1 and Tier-2 entry against it (framework-applicable / framework-inapplicable / requires-shim).
- Contain worked examples for **at least three** distinct audit sites — one atomic-ordering case, one lock-protected-invariant case, one DashMap case. Skeletons that typecheck in the real workspace (not pseudocode).
- State the stress-run role in precise language: *"Stress runs are retained as weak regression guards; `/sprint` MAY run them; they are NEVER sufficient closure proof per se."* — matching the S61 close wording.
- Specify the CI cadence (on-push / on-PR / nightly) with wall-clock budget.
- Define the audit-refresh trigger (new file matching grep pattern X; new `#[derive]` of a shared-state container on a boundary type; diff detection on the field enumeration).

These are written into §Skill Plans "/qa" Acceptance line.

### 8. /int burden

The claim that `/int` burden is low is **wrong**. Authoring `concurrency-audit.md` exhaustively across four files plus the /backend surfaces added in §1 is a full-sprint effort for one skill. The risk register is co-authored but /int carries the audit-to-risk translation. The test strategy is co-authored but /int supplies the site-level knowledge /qa needs.

Scope adjustment adopted: split the audit between /int (scheduler, worker, session, runtime trace) and /typecheck (typecheck-crate) as **co-authors**, not reviewer roles. /typecheck writing its own crate's section is lower-latency than /int drafting and /typecheck reviewing.

### 9. Showcase waiver

Accepted. Precedent: pure-design sprints with no user-visible language change may waive the showcase **when** (a) the sprint produces no executable artefact, (b) prior-sprint demos are replayed green as regression guards, and (c) the next implementation sprint that follows picks up the showcase burden for the combined delivery. S62→S63 satisfies (c). The three-clause precedent is recorded in §Notes for potential future codification (user directed: not in skill def).

### 10. FIXME disposition at checker.rs:205

Pre-committed disposition framework — A/B/C as named in §FIXME Debt. /arch adds:

- **Option A (take formal ownership)** requires /typecheck to own a concurrency invariant on `TypeCheckEnv` — accept only if the audit finds this is the natural home.
- **Option B (ratify narrow precedent)** requires naming the precedent in `design/arch/CLAUDE.md` as a numbered Decision — long-lived cross-skill arrangements live in the design book, not in a code comment.
- **Option C (defer with concrete plan)** requires a named target sprint and a named owning skill — no open-ended deferral.

/typecheck picks among A/B/C during the audit; /arch ratifies at the Wave-1 review gate.

### Required revisions (ALL APPLIED 2026-04-22)

- ✅ **§Scope item 1**: audit surface extended to include `crates/cranelisp-runtime/src/trace.rs`, cache-writer path in `src/worker.rs`, and the `OnceLock<TraceFilter>` env-var parse-once sites.
- ✅ **Audit completeness criterion**: replaced with the four-label classification + per-entry addressing scheme (§Scope item 1). 15% threshold dropped.
- ✅ **Risk register methodology**: adopted three-tier lexicographic ranking (§Scope item 2).
- ✅ **§Skill Plans "/qa"**: §7 acceptance bullets added verbatim.
- ✅ **§Skill Plans "/int" and "/typecheck"**: audit split as co-authors (see below).
- ✅ **§FIXME Debt table row 1 "Resolution" cell**: replaced with A/B/C framework; /arch ratifies at Wave-1 gate.

### Recommended revisions (APPLIED)

- ✅ **Stable addressing**: audit entries keyed on `{module-path, field-name}` + verified-at-SHA annotation, not line numbers.
- ✅ **Test strategy framework-scoring worksheet**: added as §Scope item 3 sub-bullet.
- ⏸ **Showcase waiver precedent in `.claude/commands/sprint.md`**: user directed "no need to update skill definition" — three-clause precedent recorded in §Notes only.

### Handoff to Phase 3

Phase 3 is unblocked. Next skill is `/sprint` (Phase 3 plan collection), with `/int` authoring the audit plan first so /typecheck's co-author scope is defined before /typecheck drafts its Phase 3 plan. `/arch` will review all three design documents at Wave gates (Wave 1 audit, Wave 2 risk register, Wave 3 test strategy) and will ratify the FIXME(/typecheck) disposition at the Wave 1 gate per §10. The showcase waiver is accepted.

## Skill Plans

{To be filled during Phase 3 by each skill.}

### /int
**Task**: Co-author of audit document (scheduler, worker, session, runtime trace sections); co-author of risk register; co-author of test strategy.
**Design doc**: `design/int/concurrency-audit.md` (sections: scheduler, worker, session, runtime-trace), `design/int/concurrency-risks.md`, `design/int/concurrency-test-strategy.md`.
**Approach** (Phase 3a readout, 2026-04-22 — denominator counted from file inspection at current SHA):

**§4 Scheduler — `src/scheduler.rs`** (~14-18 rows, reader-class expanded ≈ 18).
- `SchedulerV4` top-level: `state: Mutex<SchedulerState>` + 3 `Condvar`s (`priority_work_available`, `object_work_available`, `completion`).
- `SchedulerState` (inside mutex): 7 fields — `modules: HashMap<ModuleFullPath, ModuleState>`, three `VecDeque` queues, `typecheck_done: VecDeque`, `cached_modules: HashSet`, `shutdown: bool`.
- Expected classifications: mostly `under-lock-L` (L = `state`); condvar-plus-flag pairs are `published-then-read`.
- Known-hard: condvar-notify ordering vs queue push — H6 pattern grep target.

**§5 Worker — `src/worker.rs`** (~15-20 rows, mostly reader-class expansions; 5,041 LOC but only 6 owned shared-state types — the bulk is parameter passes of Arc-cloned SharedState references).
- New worker-owned state: expected empty; confirmed during Wave 1.
- Cache-writer path (`.meta.json` + `.o` writers): `publish-then-read` via `SharedState.cache_state`.
- H6 grep targets: `handle_import` + `register_dep` (S61 H6-residue site).
- `re_register_module` (REPL eval entry point): reader-class rows split.

**§6 Session — `src/session_v4.rs`** (~35-45 rows; **dominant effort centre**).
- `SharedState` struct: **16 shared-state fields** — `lib_dirs`, `platform_dirs`, `module_sexps`, `suspend_states`, `compiled_o_paths`, `promote_nice_workers`, `cached_modules`, `file_to_module`, `cache_state`, `current_module`, `repl_check_state`, `typecheck_products`, `kept_dlls`, `introspection`, `symbol_tables`, `next_type_id`.
- `Arc<SharedState>` clone sites: every worker closure captures this.
- Known-hard: (a) `cached_modules` dual-store vs `SchedulerState.cached_modules` — Principle-7 question flagged for Wave-1 gate. (b) `repl_check_state` REPL-eval vs priority-worker reader-class split. (c) `next_type_id` + `typecheck_products` insertion ordering invariant.
- Decision 31 (per-redefinition JIT reclaim) cross-referenced explicitly on `symbol_tables` DashMap GOT-slot atomic swap.

**§7 Runtime trace — `crates/cranelisp-runtime/src/trace.rs`** (~4-6 rows).
- 3 statics: `TRACE_THREAD_ID: AtomicU64`, `THREAD_ID_COUNTER: AtomicU64`, `TRACE_STACK: Mutex<Vec<TraceFrame>>`.
- /arch §1 called out `OnceLock<TraceFilter>` — **grep returns zero matches in this file.** Flagged for /arch to resolve at Wave-1 gate: drop the callout, or identify the real site.

**Locked audit schema** (for /typecheck to mirror): columns A={module-path,field-name} / B=verified-at-SHA / C=reader-class / D=operation / E=lock-held / F=classification / G=invariant-required (1 sentence) / H=H6-grep-match / I=current-status.

**Risk register co-author (Wave 2)**: /int contributes site-level knowledge (pattern matches, blast-radius per site). /arch contributes ranking adjudication, taxonomy, one-way-door implications. Expected register size ≈ 8-25 rows (1 Tier-1 + 4-8 Tier-2 + Tier-3 1:1 with `invariant-unclear` audit entries).

**Test strategy co-author (Wave 3)**: /int contributes per-site loom/shuttle/miri applicability; skeletal structured-interleaving templates grounded in audit sites (compilable skeletons required per /arch §7). /qa contributes framework scoring, CI cadence, stress-run language, baseline-ledger re-triage.

**Scope-risk flags**: /int burden is NOT low (confirmed by file inspection). ~75-100 audit rows × ~3 min each = 4-5 focused hours for audit prose. Fits Wave 1 provided no additional /int tasks attach to Wave 1. Mitigations available: single-row-per-field where invariant does not differ by reader; cross-reference rather than re-enumerate worker-side parameter passes.

**Design refs**: `design/int/heisenbug-race-closure.md` (evidence-gated cycle precedent); `design/int/persistent-workers.md`; `design/int/concurrent-workers.md`; `design/int/concurrent-pipeline.md` §7 (scheduler properties — test strategy must preserve §7.1 assertions); `design/arch/pipeline-v4.md` §3 (scheduler topology); `design/arch/CLAUDE.md` Decision 30 (mutual-import deadlock — flag in audit as architectural constraint, not race); Decision 31 (per-redefinition JIT reclaim — `SharedState` audit surface).
**Acceptance**: Four sections of audit authored per /arch Phase 2 §8 split; risk register co-authored with /arch; test strategy co-authored with /qa; all three documents approved by /arch.

### /typecheck
**Task**: **Co-author** (not reviewer) of the typecheck-crate section (§8) of `design/int/concurrency-audit.md` per /arch Phase 2 §8. Decide FIXME(/typecheck) at `checker.rs:205` disposition using the A/B/C framework (see §FIXME Debt); /arch ratifies at Wave-1 gate.
**Design doc**: Authors `design/int/concurrency-audit.md` §8.
**Approach** (Phase 3a readout, 2026-04-22 — denominator counted from mechanical grep of `crates/cranelisp-typecheck/src/**`):

**Key finding: typecheck crate OWNS no shared state.** All surfaces are either (a) `&'a` borrowed references from SharedState, or (b) process-global OnceLocks used as install-once forwarding hooks. Every invariant on `TypeCheckEnv::modules` is co-owned with /int §6. This is the structural fact driving the FIXME disposition.

**§8 scope** (~8-10 rows — small):
- `checker.rs` (2 borrowed fields): `TypeCheckEnv::modules: &'a DashMap<ModuleFullPath, SymbolTable<C,L>>` (52 access sites; `ensure_module_exists` is S61 H6 site); `TypeCheckEnv::next_id: &'a AtomicU32`.
- `crates/cranelisp-typecheck/src/trace.rs` (2 OnceLocks): `SYMBOL_TABLE_ENSURE_HOOK: OnceLock<SymbolTableEnsureHook>`, test-only `TEST_HOOK_EVENTS: OnceLock<Mutex<Vec<...>>>`.
- `program.rs`, `builtins.rs`, `traits.rs`, `adt.rs`, `infer.rs`, `resolve.rs`, `unify.rs`, `scheme.rs`, `scope.rs`, `lib.rs`: **0 owned shared state** (pure functions).

Reader-class row expansion on `TypeCheckEnv::modules`: ensure-path (`atomic-by-construction` post-S61) vs lookup-path (`published-then-read` monotonic-population invariant) — 2+ rows minimum.

Expected classification distribution on §8: ~40% `atomic-by-construction`, ~40% `published-then-read`, ~15% `under-lock-L`, ~5% `invariant-unclear`.

**FIXME A/B/C preliminary choice: Option B — ratify as numbered Decision in `design/arch/CLAUDE.md`.**

Rationale: `TypeCheckEnv` is a **borrowed view**, not a home. The concurrency invariant structurally belongs to the SharedState owner (/int). Option A (formal ownership) inverts this. Option C (defer) is prohibited without a named target. Option B memorialises the /int-authors-with-/typecheck-reviews arrangement as a long-lived precedent.

**Proposed Decision text** (for /arch to finalise at Wave-1 gate):
> "Decision 3X — Co-owned invariants on borrowed SharedState maps. Where the typecheck crate exposes a `&'a` borrow of a DashMap/Atomic owned by SharedState (e.g. `TypeCheckEnv::modules`, `TypeCheckEnv::next_id`), concurrency invariants on that field are co-owned: /int authors the mechanism, /typecheck reviews before commit, invariant statement lives in `design/int/concurrency-audit.md §9`. The `checker.rs::ensure_module_exists` rewrite (S61 Wave 3 step 3e'') is the founding instance."

**Cross-cutting contributions (§9)**:
- `TypeCheckEnv::modules` ↔ `SharedState.symbol_tables` — same physical DashMap, co-owned invariants.
- `TypeCheckEnv::next_id` ↔ `SharedState`'s `AtomicU32` — monotonic TypeId allocation.
- Decision 30 disambiguation: `lookup_type_def` cross-module scan is NOT the mutual-import deadlock site; deadlock lives scheduler-side.
- Decision 31: typecheck readers do NOT assume `got_slot` stability across concurrent redefinition. Invariant committed.

**Schema acceptance**: /int's locked schema accepted unchanged. No amendments.

**Effort estimate**: ~8-10 rows + §8.FIXME + §9 bullets. Fits Wave 1 comfortably (single skill-day).

**Design refs**: S61 narrow-precedent at `design/int/heisenbug-race-closure.md §7.10`; §FIXME Debt framework in this sprint doc; `design/arch/CLAUDE.md` Decision 31 (GOT-slot atomic swap — typecheck-side observer invariant).
**Acceptance**: §8 authored to the four-label classification standard (§Scope item 1); FIXME A/B/C disposition (preliminary Option B) finalised; Decision 3X text refined and recorded in audit; /arch ratifies at Wave-1 gate.

### /arch
**Task**: Phase 2 sprint review; Phase 3a design-doc reviews for all three documents; risk register ranking approval; test strategy one-way-door assessment.
**Design doc**: Reviews all three.
**Approach**: {filled by /arch during Phase 3}
**Design refs**: `design/arch/principles.md` (esp. Principle 3, 8, 10); `design/arch/pipeline-v4.md`.
**Acceptance**: Sprint proposal approved; three documents approved; S63 handoff brief confirmed.

### /qa
**Task**: Co-author test strategy document; re-triage baseline ledger with S63 targets.
**Design doc**: `design/int/concurrency-test-strategy.md`.
**Approach**: {filled by /qa during Phase 3}
**Design refs**: `tests/plan/strategy.md`; `tests/plan/baseline.md`; `memory/feedback_failing_not_ignored.md` (constrains stress-run downgrade wording); S61 close "methodology pivot" note; `design/int/concurrent-pipeline.md` §7.1 (scheduler properties that the strategy must preserve).
**Acceptance** (per /arch Phase 2 §7 handoff brief requirements):
- Chosen framework named (one) with version.
- Every Risk Register Tier-1 and Tier-2 entry scored against the chosen framework (framework-applicable / framework-inapplicable / requires-shim).
- Worked examples for **at least three distinct audit sites** — one atomic-ordering case, one lock-protected-invariant case, one DashMap case. Skeletons must typecheck in the real workspace.
- Stress-run role in precise language: *"Stress runs are retained as weak regression guards; `/sprint` MAY run them; they are NEVER sufficient closure proof per se."*
- CI cadence specified (on-push / on-PR / nightly) with wall-clock budget.
- Audit-refresh trigger defined (grep pattern; new `#[derive]` on boundary type; field-enumeration diff detection).
- Framework-scoring worksheet included (per /arch Phase 2 R3); framework choice justified against it.
- Test strategy approved by /arch.
- Baseline ledger re-triaged (7 entries updated to S63 targets).
- `tests/CLAUDE.md §Diagnostic Logging` updated if strategy introduces new env-vars or conventions.

### /backend
**Task**: Review audit surface for any backend-side shared state the audit should include (IO trampoline trace state, cache-writer thread state, RC trace state). Feedback to /int, not separate document.
**Approach**: {filled by /backend during Phase 3}
**Acceptance**: Audit's backend-touching sections reviewed.

### /platform
**Task**: Review audit for platform DLL load + platform-registry access sites.
**Approach**: {filled by /platform during Phase 3}
**Acceptance**: Audit's platform-touching sections reviewed.

### /frontend
**Task**: Review audit for any frontend-side shared state surfaced during lazy-discovery flows.
**Approach**: {filled by /frontend during Phase 3}
**Acceptance**: Audit's frontend-touching sections reviewed (likely thin).

### /spec
**Task**: No in-sprint action. The three S62 documents live in `design/int/`, not `spec/`.
**Acceptance**: N/A.

### /review
**Task**: Assess all three documents for structural quality (not code correctness — there is no code).
**Acceptance**: Review-doc findings filed; no blockers at close.

### /sprint (self)
**Task**: Coordinate Phase 2–6; track FIXMEs; gate waves; author close report.
**Acceptance**: Sprint closed per Phase 6 checklist (with showcase waiver noted).

### /repl, /port, /stdlib, /examples, /docs
**Task**: Showcase waived. Light review role: read the test strategy document when it lands; flag any user-experience concerns (e.g. new env-vars that affect REPL, new CI cadence that affects demo replay).
**Acceptance**: Each confirms they have read the test strategy and have no blocking concerns.

## Waves

{To be organised during Phase 4 after Phase 3 plans land. Provisional sequence:}

### Wave 1 — Audit authoring
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Author `design/int/concurrency-audit.md` | pending | Lead |
| /typecheck | Review typecheck-crate audit section; FIXME disposition | pending | Co-review |
| /backend | Review backend-touching audit sections | pending | Co-review |
| /platform | Review platform-touching audit sections | pending | Co-review |
| /frontend | Review frontend-touching audit sections | pending | Co-review |
| /arch | Architectural-coherence review | pending | Gates Wave 2 |

### Wave 2 — Risk register
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int + /arch | Author `design/int/concurrency-risks.md` | pending | Co-authors |
| /arch | Ranking approval | pending | Gates Wave 3 |

### Wave 3 — Test strategy
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa + /int | Author `design/int/concurrency-test-strategy.md` | pending | Co-authors |
| /arch | One-way-door assessment; approval | pending | Gates Wave 4 |
| /repl, /port, /stdlib, /examples, /docs | Read + flag UX concerns | pending | Non-blocking |

### Wave 4 — Close
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Re-triage baseline ledger (7 entries → S63 targets) | pending | |
| /review | Review the three documents for structural quality | pending | |
| /sprint | Verify prior demos replay green; author close report | pending | Showcase waived |

## Notes

- **Showcase waived** per user approval 2026-04-22. No new `.demo` file authored. Prior demos still verified at close as a regression guard on prior sprints. Three-clause precedent for future pure-design sprints (from /arch Phase 2 §9): (a) the sprint produces no executable artefact, (b) prior-sprint demos replay green as regression guards, (c) the next implementation sprint picks up the showcase burden for the combined delivery. **Not codified in `.claude/commands/sprint.md` per user direction 2026-04-22** — recorded here as project memory only.
- **Defect 6 deferral approved** per user approval 2026-04-22. Baseline ledger targets S63. Per 3× escalation rule this is the approved extension; a 4× deferral would require further user sign-off.
- **/int burden (revised by /arch Phase 2 §8)**: author burden is **not** low. Audit authoring across four files plus runtime trace is a full-sprint effort. Mitigated by splitting audit co-authorship with /typecheck (typecheck-crate section) per /arch §8. Risk register and test strategy remain co-authored with /arch and /qa respectively.
- **Audit completeness criterion (set by /arch Phase 2 §4)**: 100% of fields typed `Arc<T>`, `Mutex<T>`, `RwLock<T>`, `DashMap<_,_>`, `AtomicX`, or `OnceLock<T>` in target crates have an entry. Every entry carries one of four labels (`atomic-by-construction`, `under-lock-L`, `published-then-read`, `invariant-unclear`). Every `invariant-unclear` entry is a Risk Register Tier-3 row automatically. `Arc<T>` cloned into worker threads requires separate entries per reader thread class when invariant differs per reader. No ratio budgeting.
- **Risk ranking methodology (set by /arch Phase 2 §5)**: lexicographic three-tier (Tier 1 Observed → Tier 2 Suspected-by-pattern → Tier 3 Unknown surface); within each tier ordered by blast radius. Not `likelihood × blast-radius`.
- **No code changes in S62.** The FIXME at `checker.rs:205` is addressed *by documentation in the audit*, not by editing the code. Any one-line FIXME removal (if /typecheck picks Option A or B per §FIXME Debt) is permitted at close; Option C leaves the comment in place with updated pointer.

### Wave-1 gate agenda (open items from Phase 3a readout, 2026-04-22)

Surfaced by /int + /typecheck during Phase 3 plan drafting. All three require /arch adjudication at the Wave-1 audit-completion gate:

1. **Phantom `OnceLock<TraceFilter>` in `crates/cranelisp-runtime/src/trace.rs`**. /arch Phase 2 §1 Required revision added this site to the audit surface, but /int's grep returns zero `OnceLock` matches in that file. Options at Wave-1 gate: (a) drop the callout (site never existed / was removed); (b) /arch points to the real site (candidates: `crates/cranelisp-runtime/src/lib.rs`, an env-parse helper elsewhere); (c) /int discovers the site mid-audit and adds it. Does not block Wave-1 audit authoring — /int proceeds with the three confirmed statics and adds `OnceLock<TraceFilter>` if/when located.

2. **`cached_modules` dual-store Principle-7 adjudication.** /int will find `SharedState.cached_modules: Mutex<HashSet<ModuleFullPath>>` AND `SchedulerState.cached_modules: HashSet<ModuleFullPath>` during §6 authoring. Is this one logical set with two physical stores (Principle-7 violation) or two legitimate stores (cache-hint + authoritative)? /typecheck confirms this does NOT touch typecheck-crate state — pure /int + /arch question. /int will audit as `invariant-unclear` (auto-Tier-3 risk register row); /arch adjudicates at gate.

3. **Decision 3X ratification — co-owned invariants on borrowed SharedState maps.** /typecheck's preliminary Option B for the `checker.rs:205` FIXME requires /arch to finalise a new numbered Decision in `design/arch/CLAUDE.md`. Draft text quoted in §Skill Plans /typecheck Approach; /arch may accept as-is, refine, or pivot /typecheck to Option A with counter-rationale (/typecheck signals Option A conflicts with the structural "borrowed view, not a home" fact).

## Outcome

**Closed mid-sprint** 2026-04-25. After Phase 3a readouts but before Wave 1 audit authoring began, `sprints/METHOD_PROPOSED.md` reframed the delivery method around a generic narrow-deployment per-crate triad (`/design` → `/dev` → `/review`), retiring the five per-crate compiler skills (`/frontend`, `/typecheck`, `/backend`, `/int`, `/platform`) this sprint had built its plan around. Continuing under the legacy skill set would have committed three more waves to a model about to be retired. The sprint was closed to clear the runway for the methodology migration arc opening at S63.

### Delivered

- **Sprint scope** — three-document decomposition (audit → risk register → test strategy), §FIXME Debt framework with disposition options A/B/C for `checker.rs:205`, completeness criterion (100% mechanical-grep coverage with four-label classification), three-tier lexicographic ranking methodology, framework-scoring worksheet requirement, audit-refresh cadence triggers, S63 handoff brief requirements.
- **/arch Phase 2 review** — APPROVE WITH REVISIONS verdict; all 6 required revisions and 2 of 3 recommended revisions applied in-place. Showcase-waiver three-clause precedent recorded.
- **/int Phase 3a plan** — full readout: scheduler ~14-18 rows, worker ~15-20 rows, session ~35-45 rows (dominant effort centre with 16 SharedState fields enumerated), runtime trace ~4-6 rows. Locked audit schema (9-column).
- **/typecheck Phase 3a plan** — key finding: typecheck crate owns no shared state (all surfaces are borrowed views from SharedState or process-global OnceLocks). §8 scope ~8-10 rows. Preliminary FIXME(/typecheck) Option B with draft Decision 3X text quoted for /arch finalisation.
- **Wave-1 gate agenda** documented (3 open items: phantom `OnceLock<TraceFilter>`, `cached_modules` dual-store, Decision 3X ratification).
- **Partial design docs** committed as work-in-progress for the post-migration concurrency sprint to pick up:
  - `design/int/concurrency-architecture.md`
  - `design/int/concurrency-audit.md`
  - `design/int/concurrency-risks.md`
  - `design/int/concurrency-test-strategy.md`
  - `design/int/concurrency/` (8 mermaid diagrams + README — structure matrix, current-state, target-state, dependency-protocol current+target, scheduler-lifecycle, symbol-publication current+target)

### Deferred (carried to post-migration concurrency sprint)

- **Wave 1 audit completion** across all 5 target surfaces (typecheck, scheduler, worker, session, runtime trace).
- **Wave 2 risk register** authoring.
- **Wave 3 test strategy** + framework choice (loom/shuttle/miri/structured-interleaving) + framework-scoring worksheet.
- **Wave-1 gate open items**:
  - Phantom `OnceLock<TraceFilter>` site (grep returns zero matches in `crates/cranelisp-runtime/src/trace.rs`; /arch to either drop the callout or identify the real site).
  - `cached_modules` dual-store Principle-7 question (`SharedState.cached_modules` vs `SchedulerState.cached_modules` — one logical set with two physical stores, or two legitimate stores).
  - Decision 3X ratification (co-owned invariants on borrowed SharedState maps; /typecheck preliminary Option B for `checker.rs:205` FIXME).
- **All 7 baseline-ledger carries** (S61-originated) re-target to post-migration concurrency sprint:
  - `sprint23::heisenbug_race_reduced_concurrent_import_pairs` (H6 residue 5-10%).
  - `sprint61_observability_io::io_trace_off_path_*_generous_ceiling` (harness ceiling).
  - 4× `sprint59_defects456_repro::d6_exemplar_*` (Defect 6 — 3× deferral approved S62 open; this is the implicit 4× deferral via methodology pivot — flag for explicit user sign-off when next concurrency sprint opens).
  - `wave6_demo_repros::exemplar_solver_*` (Defect 6 end-to-end entry).
- **FIXME(/typecheck) at `checker.rs:205`** — disposition framework pre-committed by /arch; A/B/C choice not made; carry forward unchanged. Future post-migration sprint picks up under the new triad (likely `/dev` narrow-to-typecheck consults `/design` for the disposition).
- **Defect 6 exemplar stack overflow** (5 carries → 6 carries) — orthogonal to concurrency; orthogonal to methodology migration; explicit user sign-off needed when next picked up.
- **Other deferrals** (unchanged from §Scope Out-of-scope table): FQTypeName migration, harness ceiling, S61 /review Importants (Mutex hedge, test helper consolidation, counter_non_zero), performance baseline, stdlib prelude monolith, Phase H / Tier 2 release backend.

### Findings

- **Methodology pivot rationale**: the methodology change reorganises *how skills are deployed* (one generic skill per role, narrow-deployed per crate) more than *what gets done*. The S62 plan's 12-skill cast — with Phase 3a readouts from `/int` and `/typecheck` plus four other-skill review roles — is exactly the kind of per-skill duplication the new model collapses. Re-running the same audit under `/design` (cranelisp-typecheck) + `/design` (cranelisp-runtime) + `/design` (src/) + `/design` (cranelisp-platform) etc. is structurally cleaner and produces design docs in their target home (`design/{crate}/{crate}.md`) rather than ad-hoc files under `design/int/`. The work product survives — only the framing changes.
- **Untracked-design-doc preservation policy**: when a sprint closes mid-flight, partial design artefacts authored during planning are committed in the close commit (not discarded, not left untracked). This preserves the work as input to whichever future sprint resumes the topic and makes the archive's references resolvable.
- **Implicit-deferral hazard for 3×-escalated items**: Defect 6 was 3×-deferred at S62 open with explicit user sign-off; methodology pivot now silently advances it to a 4× deferral. Logged here to prompt explicit re-approval when the post-migration concurrency sprint opens — the escalation rule (`feedback_failing_not_ignored.md` + `METHOD_PROPOSED §7.2`) is not satisfied by inheriting via methodology change.
- **Showcase waiver precedent applies**: pure-design sprints satisfying the three-clause test (no executable artefact, prior demos replay green as regression guards, next implementation sprint picks up showcase) waive showcase. S62 satisfies all three; prior demos replay status not re-verified at this close (pivot replaces the next-sprint-picks-up-showcase clause — the next *concurrency* sprint will, post-migration).
- **Phase model handled the abort cleanly**: closing between Phase 3a (planning) and Wave 1 (execution) is the cheapest possible mid-sprint stop. METHOD's seven-phase model with explicit gates made the boundary obvious; if the pivot signal had landed mid-Wave the close would have been more expensive.
- **/arch narrow-precedent hybrid ownership** (S61 origin) carries forward unresolved: `checker.rs:205` FIXME(/typecheck) still represents an undocumented cross-skill arrangement. Under the new triad the question is whether `/design` (cranelisp-typecheck) and `/design` (src/) co-own the invariant, or whether the invariant moves entirely into the binary crate's design doc. Future sprint adjudicates.
