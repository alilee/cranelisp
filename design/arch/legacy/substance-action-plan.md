# Substance + Procedural Action Plan — Sprint 64 Increment

**Status.** Authored Sprint 63 close, in-session by `/arch`. In execution.

**Progress.**
- Step 0 (register migration) — **DONE**, commit `1eeae53`.
- Step 1a (structural separation, legacy/ bucket) — **DONE**, commit `3316599`.
- Step 1b (substance commitments) — **DONE**, commits `19124fa` (Decisions 40/41/42 + LinkerSymbol rename), `9c33e0e` (types/PlatformError), `de98bf0` (runtime IoObserver + runtime_panic), `238a631` (platform PlatformError + retire dispatch), `3ccbb44` (backend compile_to_module + Code + CompilationError), `56c75a8` (frontend public surface + SymbolTables generic), `c49d094` (int SharedState/Code), `f79af54` (BCs cite Decision 40).
- Step 1c (procedural reconciliation) — **DONE**, commits `1882569` (FIXME triage — delete substance-closed 0003 + 0042), `1c8d519` (audit supersession annotations), `3247647` (cross-amendments to Decisions 0031 + 0035).
- Step 1d (acceptance gate) — **DONE** with this commit; substance-scoping/reconciliation docs move to legacy/; Step 1 closes.
- Step 2 (per-crate /design refresh), Step 3 (/qa test plan), Step 4 (per-skill implementation slices) — pending.

**Deferred from Step 1c.** `sprints/triad-shared.md` step 7 reword (per substance-scoping §1.5 — audit-role reframing) is methodology, not arch. Deferred to `/sprint` or methodology owner; not gating Step 1 close.

**Inputs.**
- `design/arch/substance-scoping.md` — substantive findings + resolutions (per-item form: Description, Symptom, Tension, Stake, Resolution, Consequences, Owner, Sequencing)
- `design/arch/reconciliation-plan.md` — procedural reorganisation plan (canonical-home table, currency sweep, audit reconciliation, decision-log evolution, FIXME triage, subordinate-doc lifecycle, sequencing waves)

**Methodology pivots adopted in execution.**
- **Delete files, rely on git for history.** When retracting Decisions, closing FIXMEs, or removing within-file historic content, just delete — git diff is the audit trail. No `superseded/`, `retracted/`, `closed/` subdirectories needed.
- **Don't fold content; move it whole.** Legacy/non-canonical docs move to `design/arch/legacy/` intact. Other skills pull back the parts they need; `/arch` does not pre-extract or re-author.
- **Top-level `design/arch/` is approved configuration only.** Working docs, queued migrations, and superseded subsystem designs go to `legacy/` — a triage bucket between top-level (re-promoted if proven load-bearing) and `archive/` (frozen).

**Output.** Sprint 64 increment scope and per-skill deliverables, sequenced through four steps. Hands off to `/sprint` for wave scheduling and to each owning skill for execution.

**In scope.** Substance commitments (~11 items) + procedural reconciliation Wave 1 + first downstream cascade (per-crate design refresh, test-plan revision, first implementation-slice plans).

**Out of scope.**
- §1.7 (Decision 14 retraction + `cranelisp-runtime` → `cranelisp-primitives` + `cranelisp-intrinsics` crate split) — separate Sprint 65+ wave with its own action plan; too large to bundle here
- §2.14 (int observability formalisation) — deferred per `/design` (int) rebuild wave; subordinate-doc currency is a systemic concern
- §2.8, §2.9 — deferred FIXMEs filed alongside the Sprint-64 commit but implementation lands later

---

## Synthesis

The substance + procedural work converges into one Sprint-64 increment, preceded by a Step 0 pre-phase that brings the three architectural registers (Decisions, Principles, FIXMEs) to 100% currency. Step 0 is non-negotiable: Step 1 files Decisions 40–42, redrafts facades that cite Principles by number, and triages FIXMEs — none of these can land cleanly on registers that are themselves stale or inconsistent. After Step 0, `/arch` lands canonical updates (Step 1, the gate for everything downstream). After Step 1, `/design` (per-crate) and `/qa` proceed in parallel: each `/design` (crate) refreshes its master design doc against the now-current canonical set and re-surfaces any new architectural questions; `/qa` revises the test plan to uplift integration + e2e infrastructure against the new contracts and pending audit findings. Step 4 closes the increment: each `/design` (crate) and `/qa` author a first-sprint implementation slice ready for `/sprint` to schedule into Sprint 65.

The shape is gates not parallelism: Step 0 gates Step 1 (registers must be sound before substance commitments file against them); Step 1 gates Step 2 + Step 3 (downstream skills cannot refresh against a moving canonical set); Step 2 + Step 3 jointly gate Step 4 (implementation plans need both architectural and test-plan currency to be coherent).

---

## Step 0 — Pre-phase: relocate registers to designed position, at 100% currency

The substance + procedural work in Steps 1–4 depends on three registers being sound, complete, AND in their canonical designed position: `design/arch/decisions/`, `design/arch/principles/`, `design/arch/fixmes/` (each one file per item). Today, Decisions live inline in `design/arch/CLAUDE.md`; Principles live as a single file `design/arch/principles.md`; FIXMEs live under `sprints/fixmes/`. Step 0 relocates all three to their designed homes AND brings each to 100% currency in the same pass — relocation without currency-check ports stale state forward; currency-check without relocation defers the structural debt.

The relocation is decided — no further choice point. Step 0 executes the move.

### 0a. Decisions: inline → `design/arch/decisions/NNNN-{slug}.md`

Extract Decisions 1–39 from `design/arch/CLAUDE.md` into one file per Decision at `design/arch/decisions/NNNN-{slug}.md`. Frontmatter + body shape per file:

```markdown
---
number: NNNN
title: Short stable title
status: operative | retracted | superseded-by-NNNN | partially-superseded-by-NNNN
filed: sprint NN
canonical_location: <path/to/code or doc>
amends: [list of Decision numbers]
amended_by: [list of Decision numbers]
---

# NNNN — Title

## Statement
[The Decision text — one or several paragraphs as today]

## Rationale
[Principles cited by name; trade-offs; rejected alternatives]

## Cross-references
[Other Decisions, facade sections, code locations]
```

**During the move, currency-check each Decision:**

- Statement + Rationale + Canonical location complete.
- Status correctly marked (7, 8, 20, 28 retracted; 9 partially superseded by 38; 14 operative through Sprint 64 then retracts in §1.7's later wave; 23, 26, 35 carry clarifications per recent sprint work).
- Cross-references rewritten as file-path links (`see [Decision 31](decisions/0031-jit-per-batch.md)`) — every link resolves.
- Numbering stable: 40, 41, 42 unallocated and reserved for Step 1 substance commitments; 43 reserved for §1.7's Sprint-65+ wave.

**`design/arch/CLAUDE.md` updates after the move:**

- "Key Decisions (Phase B)", "Key Decisions (Ring 1)", "Key Decisions (Ring 2A)", etc. sections collapse to a thin **Decisions index** — one line per Decision: `- [NNNN](decisions/NNNN-slug.md) — title (status)`.
- The canonical-documents table at the top of CLAUDE.md adds a row for `decisions/` directory.
- Auto-import in `.claude/commands/arch.md` updates: instead of (or in addition to) auto-importing `principles.md`, the arch skill auto-imports the `decisions/` index file.

**Output.** All Decisions live in `design/arch/decisions/`; CLAUDE.md carries the index; cross-references resolve; 40, 41, 42 confirmed unallocated.

### 0b. Principles: `principles.md` → `design/arch/principles/NN-{slug}.md`

Extract 13 principles from `design/arch/principles.md` into one file per Principle at `design/arch/principles/NN-{slug}.md`. Frontmatter + body shape:

```markdown
---
number: NN
title: Short stable title
filed: pre-Sprint-NN (or sprint of origin)
---

# Principle NN — Title

## Statement
[The principle text]

## Rationale
[Why this principle exists; what it protects]

## Examples
[Specific cases where this principle applies, with cross-references]

## Cited by
[Reverse index — files + sections that cite this principle]
```

**During the move, currency-check each Principle:**

- Stable numbering preserved (all 13 keep their existing numbers).
- "Cited by" section populated by sweeping all docs (overview, BCs, facades, master design docs, Decisions, `src/CLAUDE.md`, `tests/CLAUDE.md`, sprint docs) for `Principle N` references.
- Orphan citations resolved (re-cite the correct principle or remove the dangling reference).
- Editorial polish: typos and dangling clauses fixed; substantive change explicitly out of scope (substance-scoping pass found no principle needs evolving).

**`design/arch/principles.md` updates after the move:**

- Becomes a thin index — one line per Principle: `- [Principle NN](principles/NN-slug.md) — title`.
- Or deleted entirely with the index moving to `design/arch/principles/README.md` — `/arch`'s call; pick whichever produces fewer broken external references.
- Auto-import in `.claude/commands/arch.md` updates to import the index.

**Output.** All Principles live in `design/arch/principles/`; reverse-citation index lives on each Principle file's "Cited by" section; orphans resolved; auto-import functional.

### 0c. FIXMEs: `sprints/fixmes/` → `design/arch/fixmes/`

Move every `sprints/fixmes/NNNN-*.md` to `design/arch/fixmes/NNNN-*.md`. Frontmatter format unchanged (number/target/filed_by/filed_at/sprint_filed/refers_to/status). The relocation reflects that FIXMEs are cross-cutting architectural change requests, not sprint coordination artefacts — the register belongs alongside the architecture, owned by `/arch` for index-keeping while remaining write-able by any skill per the cross-skill protocol.

**During the move, currency-check each FIXME:**

- For each `status: open` FIXME, confirm: (a) target skill is current and named correctly; (b) `refers_to` references resolve; (c) the FIXME hasn't been silently closed by intervening work that didn't delete the file.
- Annotate substance-closed FIXMEs (those the Sprint-64 substance commitments will close) with `closed_by: §X.Y` so Step 1's commit can delete them in the same batch as the substance work that closes them, with traceable rationale.
- Migrate remaining inline FIXMEs: sweep the project for residual `FIXME(/skill)` in HTML comments per `CLAUDE.md`'s "OLD protocol" framing. For each: either migrate to file form (`design/arch/fixmes/NNNN-name.md`) or close as obsolete with rationale recorded in the commit message.
- Verify next-number-scan (`max + 1`) works against the new directory; pre-allocate 5–10 numbers conceptually so Step 1's filings don't race against Step 2's new-FIXME submissions.

**Ripple updates to docs that reference the old location:**

- Project root `CLAUDE.md` "Cross-Skill Changes" section: update path from `sprints/fixmes/` to `design/arch/fixmes/`.
- `sprints/METHOD.md` §3.3 (FIXME format): update path reference.
- `design/arch/CLAUDE.md` canonical-documents table: add `fixmes/` directory row; remove or update any "FIXMEs live in sprints/" framing.
- Any skill files (`.claude/commands/*.md`) that reference the old path.
- Wave-gate scan in `/sprint`'s workflow: update the directory it scans.

**Output.** All FIXMEs live in `design/arch/fixmes/`; ripple updates landed; inline-form residue migrated or closed; substance-closed items pre-marked for Step 1 deletion; next-number scan verified against the new home.

### Step 0 acceptance gate

Step 0 closes when:

- `design/arch/decisions/` directory populated; CLAUDE.md collapsed to index + canonical-doc table updated; auto-import functional.
- `design/arch/principles/` directory populated; reverse-citation index on each Principle file; orphans resolved; auto-import functional.
- `design/arch/fixmes/` directory populated; ripple updates landed across project root CLAUDE.md, `sprints/METHOD.md`, skill files, sprint workflow.
- All three registers at 100% currency in their designed position.
- User accepts before Step 1 begins.

Estimated effort: 4–6 days of `/arch` focused work. The relocation is mostly mechanical (file extraction + ripple-edit), but the currency check on each item adds judgment overhead — the Decision audit alone walks 39 entries with cross-reference verification; the Principles citation sweep is grep-able but each finding needs validation; the FIXME inline-residue sweep is the most variable in effort. Step 1 cannot begin until Step 0 closes — substance commitments landing on registers in the wrong location compound the structural debt rather than resolving it.

---

## Step 1 — `/arch` lands canonical updates

`/arch` is the sole skill that touches `design/arch/` artefacts in this step. Step 1 closes when the canonical set (overview, principles, bounded contexts, facades, decisions) reflects every accepted substance-scoping resolution AND every procedural reconciliation Wave 1 commitment.

Step 1 is sub-batched into four parts. 1a (structural separation) lands the going-forward-vs-historic split before substance commitments to ensure new work lands on a clean structure. 1b (substance) applies the substance-scoping resolutions; 1c (procedural) does the reconciliation sweep; 1d is the acceptance gate.

### 1a. Structural separation — DONE (commit `3316599`)

Non-canonical `design/arch/*.md` working/subsystem documents moved to `design/arch/legacy/`:

- `pipeline-v4.md`, `pipeline-v4-roadmap.md`, `concurrent-pipeline.md` (pipeline-v4 convergence; lessons in Decisions 21–27, 31, 36, 37)
- `fqtypename.md` (queued migration)
- `macro-resolver.md`, `traitimpl-symbol-table.md`, `super-import-arbitration.md` (subsystem designs; content may belong in facades or Decisions)
- `roadmap.md` (architectural roadmap; may dissolve into action plans or be re-authored against the post-Step-1 canonical set)
- `sequence-diagram/` (pre-Sprint-63 v4-target diagrams; superseded by `sequences/`)

`design/arch/CLAUDE.md` updated: removed "Working documents" + "Subsystem designs" sections; added "Sorting buckets" section distinguishing `legacy/` (triage bucket) from `archive/` (frozen). Top-level approved configuration is now: `bounded-contexts.md`, `CLAUDE.md`, `interfaces.md`, `overview.md`, `principles.md` + `decisions/`, `facades/`, `fixmes/`, `principles/`, `sequences/` (+ in-flight Step 1 planning docs that move to `legacy/` at end of Step 1).

### 1b. Substance commitments (from `substance-scoping.md`)

| Item | Action | Artefacts touched |
|---|---|---|
| §1.1 | File **Decision 40** (relocate `trace.rs` + `io_trace.rs` to int via `IoObserver` callback contract; runtime keeps ~50-line API). Update `bounded-contexts.md` §4 (no BC change, but reaffirm Diagnostics out-of-scope with this Decision as evidence). Redraft `facades/runtime.md` §IO observation. | Decisions, BC §4, runtime facade |
| §1.2 | File **Decision 41** (per-symbol JIT cardinality; `Code` location moves to `cranelisp-backend`; backend writes directly to shared state via mutref pattern). Amend Decisions 31 + 35 with cross-references. Redraft `facades/backend.md` §`compile_to_module` with the four-parameter signature pinned. | Decisions, backend facade |
| §1.3 | File **Decision 42** (`PlatformError` enum in `cranelisp-types` with per-variant `ErrorLocation` carriers). Redraft `facades/platform.md` §Errors. Note in Decision 42: `runtime_panic` intentionally stays flat-String per §2.10 (panics being driven to zero, not enriched). | Decisions, platform facade, types facade |
| §1.4 | Redraft `facades/frontend.md` §`SymbolTables` alias to use the generic form per Decision 32. No new Decision (Decision 32 already binds). | Frontend facade |
| §1.5 | Reword `triad-shared.md` step 7 (audit role: point-in-time opinion, not ongoing ground truth). Note in `design/arch/CLAUDE.md` "Working documents" section: existing audit files (typecheck, int, frontend, backend) carry their target-direction sections as historical context; `/review` is the continuous-audit role going forward. | `triad-shared.md`, `CLAUDE.md` working-docs section |
| §2.1 | Redraft `facades/frontend.md` §Public surface with two calls: `parse(source) -> Vec<Sexp>` and `extract_module_declarations(forms) -> (StructuralDecls, Vec<Sexp>)`, plus the per-form `build_ast(defn_sexp)` / `build_expr(sexp)` calls. No AST union. Subsumes §2.2. | Frontend facade |
| §2.4 | DEFERRED to `/dev` (typecheck) in Step 4. `/arch` scope is design/arch/ artefacts only; rustdoc on a Rust source file is per-crate work that the typecheck `/dev` slice picks up. | (out of /arch scope) |
| §2.6 | Redraft `facades/backend.md` §Linker: `Linker::get_symbol(name: &LinkerSymbol) -> Result<*const u8, LinkerError>`. **Rename `JitSymbol` → `LinkerSymbol`** in `cranelisp-types` newtypes table; update `facades/types.md`, `src/CLAUDE.md` (string-newtypes table), and every facade that referenced `JitSymbol`. | Backend facade, types facade, src/CLAUDE.md, cross-facade rename |
| §2.7 | Redraft `facades/backend.md` `compile_to_module` errors to add typed `CompilationError::SymbolNotCompilable { module, symbol }` variant. | Backend facade |
| §2.11 | Redraft `facades/runtime.md` §`runtime_panic` to truth-tell: `pub extern "C" fn runtime_panic(msg_ptr, msg_len)` + `pub fn take_runtime_error() -> Option<String>`. Note: this is facade-correctness, not enrichment — flat-String stays per §2.10. | Runtime facade |
| §2.13 | Retire `HostContext::dispatch` from `facades/platform.md` §12; replace with note pinning Decision 26's direct-GOT-lookup path as canonical. | Platform facade |

**New Decisions to file:** 40, 41, 42 (three Decisions; §1.4 / §2.1 / §2.4 / §2.6 / §2.7 / §2.11 / §2.13 are facade redrafts under existing Decisions or no-Decision corrections).

**Newtype rename ripple (§2.6):** `JitSymbol` → `LinkerSymbol` is the only non-trivial cross-doc rename in Step 1. Every facade that used `JitSymbol` updates in the same commit; rustdoc references in `cranelisp-types`, `cranelisp-backend`, `src/` follow as `/dev` work in Step 4 implementation slices.

### 1c. Procedural reconciliation (from `reconciliation-plan.md` Wave 1)

| Procedural item | Action |
|---|---|
| Canonical-home table | `design/arch/CLAUDE.md` already carries it (Sprint 63); reaffirm in Step 1 commit message that the substance commitments respect it (no canonical doc moves). |
| Currency sweep | Update `archive/` triggers for `pipeline-v4.md` if Decision 41 closes the convergence (re-evaluate in Step 1c gate). |
| Audit reconciliation | For each existing audit (typecheck, int, frontend, backend): add a Sprint-63 annotation at the top stating "target-direction sections superseded by Decisions 38, 39, 40, 41, 42" + cite each by number. Per §1.5, no full re-pass; current-state sections remain authoritative as historical observation. |
| Decision-log evolution | Step 1 keeps Decisions inline in `design/arch/CLAUDE.md`. The M3 sweep (formalise into `decisions/NNNN-*.md`) is procedural cleanup deferred to a later sprint per the reconciliation plan; not gating. |
| FIXME triage | Resolve all `sprints/fixmes/*` whose target is closed by a substance commitment (e.g. FIXMEs that would be subsumed by Decisions 40, 41, 42); leave deferred FIXMEs (§2.8, §2.9) open. |
| Subordinate-doc lifecycle | No subordinate-doc work in Step 1. Per §2.14 deferral, subordinate-doc currency is each `/design` (crate)'s rebuild responsibility in Step 2. |

### 1d. Step 1 acceptance gate

Step 1 closes when:
- All three new Decisions (40, 41, 42) filed in `design/arch/CLAUDE.md` with full body + Rationale + Canonical location.
- Decisions 31, 35 carry the §1.2 cross-amendments.
- `JitSymbol` → `LinkerSymbol` rename applied across every facade and `src/CLAUDE.md`.
- All Step-1a facade redrafts landed; each redraft cites the resolved substance-scoping item by §-number.
- Existing audits carry the Sprint-63 annotation per §1b.
- `triad-shared.md` step 7 + `CLAUDE.md` Working Documents section reflect §1.5's audit-role reframing.
- Outstanding FIXMEs that target closed work are deleted per the cross-skill protocol (`CLAUDE.md`); deferred FIXMEs (§2.8, §2.9) remain open with their resolution notes.

`/arch` commits Step 1 as one logical batch (may be multiple commits for reviewability, but conceptually one wave). User reviews per the project's review-before-enact discipline. Step 2 + Step 3 cannot start until user accepts.

---

## Step 2 — each `/design` (crate) refreshes its master design doc

After Step 1 lands, each compiler skill's `/design` role (`/design` is per-crate; e.g., `/design (frontend)`, `/design (backend)`) reads the current canonical set and refreshes its master design doc at `design/{crate}/{crate}.md`. This step also addresses subordinate-doc currency for that crate (the systemic concern §2.14 surfaced).

### Per-crate deliverables

| Crate | Master design doc | Subordinate docs | New FIXMEs expected to surface |
|---|---|---|---|
| `frontend` | `design/frontend/frontend.md` refreshes against §1.4 (SymbolTables alias) + §2.1 (parse/extract/build surface) | `macro-resolver.md`, `super-import-arbitration.md` — refresh against current expander state | Boundary tensions discovered while reconciling AST shape with int's consumption pattern |
| `typecheck` | `design/typecheck/typecheck.md` refreshes against §2.4 (ResolutionGap rustdoc), Decision 38 (SymbolTable mutability), Decision 39 (per-defn source) | `traitimpl-symbol-table.md` — refresh | Constraint-system rationale gaps; status-gating questions for Gap handling |
| `backend` | `design/backend/backend.md` refreshes against §1.2 (per-symbol JIT, direct shared-state writes), §2.6 (LinkerSymbol rename), §2.7 (typed errors), Decision 41 | (none subordinate at present) | Codegen-emit-site invariants surfaced by Decision 41's mutref-pattern; `Code` ownership at the integration boundary |
| `runtime` | `design/runtime/runtime.md` refreshes against §1.1 (relocation of trace.rs + io_trace.rs to int), §2.11 (runtime_panic truth-telling) | (none subordinate at present) | IoObserver callback contract details (event taxonomy, registration API surface, runtime-side observer-state minimisation) |
| `platform` | `design/platform/platform.md` refreshes against §1.3 (PlatformError ErrorLocation), §2.13 (HostContext::dispatch retired) | (none subordinate at present) | Per-platform error-construction patterns; manifest+DLL coupling implications |
| `int` | `design/int/int.md` refreshes against Decision 38 (SharedState formal definition), Decision 39 (per-defn source on Introspection), §1.1 (becoming the new owner of trace.rs + io_trace.rs), §1.2 (consuming Decision 41's mutref pattern) | `persistent-workers.md`, `concurrent-pipeline.md`, `pipeline-v4.md` — refresh; `observability.md` (subordinate doc updated per §2.14 deferred work, can land here or in a later wave at /design (int)'s discretion) | Integration-layer ownership of IoObserver registration; observability mode-discriminator integration with worker scheduler |

### Process per crate

1. Read updated canonical set (overview, principles, BCs, relevant facades, Decisions).
2. Cross-check master design doc against current implementation in `crates/cranelisp-{crate}/`.
3. Refresh prose: replace stale framings, cite new Decisions, align bounded-context phrasing.
4. Refresh subordinate docs (per `/design` (crate)'s judgment of which need it).
5. Re-walk the master doc for "Open questions / proposed FIXMEs" — surface any new architectural questions exposed by reconciling against the now-current canonical set + current implementation.
6. File new FIXMEs as `sprints/fixmes/NNNN-*.md` per the cross-skill protocol.

### Step 2 acceptance gate

Step 2 closes per crate when:
- Master design doc refreshed; cites all relevant new/amended Decisions by number.
- Subordinate docs refreshed (or judgment recorded that they're current).
- New FIXMEs filed for any architectural question the rebuild surfaced; FIXMEs target `/arch` (cross-crate) or other skills as appropriate.
- `/arch` triages new FIXMEs: either (a) accept and queue for next substance-scoping addendum, or (b) push back with rationale.

Step 2 closes overall when all six crate `/design` skills report completion. Per-crate work is parallel; no cross-crate gating within Step 2.

---

## Step 3 — `/qa` revises test plan

Runs in parallel with Step 2 after Step 1 lands. `/qa` reads the same updated canonical set as Step 2's `/design` skills, plus existing audit findings (now annotated per §1.5), and revises the test plan.

### Inputs

- Updated canonical set (overview, principles, BCs, facades, Decisions 38–42).
- Annotated existing audit findings (typecheck, int, frontend, backend).
- Awareness that runtime + platform have no audit; `/review` will fill these going forward (per §1.5 / §1.6 reframing).
- Current `tests/` state — what's covered, what's `#[ignore]`'d, what `// spec:` traces are in place.

### Deliverables

| Deliverable | Location | Content |
|---|---|---|
| Revised test plan | `design/qa/test-plan.md` (or equivalent — `/qa`'s call) | Coverage gaps surfaced by new contracts (Decisions 40–42, facade redrafts); spec sections that gain test-traceability targets; `[Tested]` / `[R{N} S{M}]` annotation refresh |
| Integration test infrastructure uplift | Listed as work items in the test plan | Cross-crate failure isolation harness (per `tests/CLAUDE.md` §"Isolating Cross-Crate Failures"); IoObserver test fixtures (post-§1.1 relocation); new `LinkerSymbol`-aware test helpers |
| E2E test infrastructure uplift | Listed as work items in the test plan | Coverage for `--run` vs `--link` divergence; REPL/batch parity tests; cache-hit vs fresh-build symmetry tests (per Decisions 25, 31, 37) |
| Audit-derived test targets | Listed as work items | For each annotated audit's still-relevant current-state observations: a tracing test that locks the observation in (or a FIXME naming why no test is appropriate) |

### Step 3 acceptance gate

Step 3 closes when:
- Test plan reflects every new Decision and facade redraft from Step 1.
- Infrastructure uplift items are concrete (not "improve test infra" — specific harnesses, fixtures, helpers named).
- Audit-derived targets are enumerated; coverage for runtime + platform (the un-audited crates) is explicit.
- `/arch` reviews the test plan for cross-skill coverage; user accepts.

---

## Step 4 — each `/design` (crate) + `/qa` author first-sprint implementation slice

After Steps 2 + 3 close, each `/design` (crate) and `/qa` author a Sprint-65 implementation plan: a concrete first-sprint slice of work that lands the substance commitments + the new test infrastructure.

### Per-skill deliverables

| Skill | Reads | Authors | Slice scope |
|---|---|---|---|
| `/design` (frontend) | Refreshed `frontend.md`, test plan | Sprint-65 frontend implementation plan | First-wave slice of §1.4 + §2.1 facade work; coverage tests for new public surface |
| `/design` (typecheck) | Refreshed `typecheck.md`, test plan | Sprint-65 typecheck implementation plan | §2.4 rustdoc work; any Decision-38 / 39 implementation gaps closed |
| `/design` (backend) | Refreshed `backend.md`, test plan | Sprint-65 backend implementation plan | First-wave slice of §1.2 (Decision 41 implementation) + §2.6 (`LinkerSymbol` rename) + §2.7 (typed error variant) |
| `/design` (runtime) | Refreshed `runtime.md`, test plan | Sprint-65 runtime implementation plan | §1.1 IoObserver API exposed; trace.rs + io_trace.rs ready for int to assume ownership; §2.11 `runtime_panic` facade alignment |
| `/design` (platform) | Refreshed `platform.md`, test plan | Sprint-65 platform implementation plan | §1.3 `PlatformError` migration to `ErrorLocation`; §2.13 `HostContext::dispatch` source removal |
| `/design` (int) | Refreshed `int.md`, test plan | Sprint-65 int implementation plan | Receive-side of §1.1 (trace.rs + io_trace.rs land in `src/`); receive-side of §1.2 (consume Decision 41's mutref pattern); SharedState shape per Decision 38 finalised in code |
| `/qa` | Test plan (own deliverable) | Sprint-65 test-suite implementation plan | First-wave slice of integration + e2e infrastructure uplift; coverage tests for the substance commitments landing in Sprint 65 |

### Step 4 acceptance gate

Step 4 closes when:
- All seven implementation-slice plans authored.
- `/sprint` reviews each for fit into Sprint 65's wave structure: identifies cross-skill dependencies (e.g., `/dev (runtime)` exposing IoObserver before `/dev (int)` consumes it; `/dev (backend)` `LinkerSymbol` rename before `/dev (int)` updates call sites).
- `/sprint` opens Sprint 65 with a coordinated wave plan citing each implementation slice.

---

## Sequencing summary

```
Sprint 64 — substance + procedural reconciliation increment

  Step 0: /arch register hygiene (Decisions, Principles, FIXMEs)  [~2-4 days /arch focused]
    ↓ (gate: user accepts Step 0; all three registers at 100% currency)
  Step 1: /arch canonical updates                         [~1-2 weeks /arch focused]
    ↓ (gate: user accepts Step 1 commit)
  Step 2: /design (per crate) refreshes design docs       [parallel; ~1 week each]
  Step 3: /qa revises test plan                           [parallel with Step 2; ~1 week]
    ↓ (gate: user accepts Step 2 + Step 3 outputs)
  Step 4: /design + /qa author Sprint-65 implementation plans  [parallel; ~3 days each]
    ↓ (gate: /sprint integrates into Sprint 65 wave plan)

Sprint 65 — first implementation increment (out of scope for this action plan)
  /dev (per crate) + /qa execute Sprint-65 wave per Step-4 plans

Sprint 65+ — separate wave for §1.7 (Decision-14 retraction + crate split)
  Authored under its own action plan; not bundled here
```

---

## Risks and mitigations

| Risk | Mitigation |
|---|---|
| Step 0 surfaces inconsistencies larger than expected (orphan principle citations resolving to substantive text drift; inline FIXMEs that turn out to encode open architectural questions; Decision cross-references that don't resolve) | Extend Step 0 rather than deferring findings to a later sweep; substance commitments cannot land cleanly on shaky registers. Material findings from the inline-FIXME sweep that reveal new architectural questions get filed as proper FIXMEs and feed into a substance-scoping addendum if they're load-bearing |
| Step 1 over-scopes (~11 substance items + procedural reconciliation in one wave) | `/arch` commits in reviewable sub-batches (e.g., Decisions first, facade redrafts second, rename ripple third); user reviews each sub-batch |
| `LinkerSymbol` rename touches many docs and risks search-and-replace errors | Treat rename as one focused commit; `/arch` runs `grep JitSymbol` after rename to verify zero residue (excluding archive/) |
| Step 2's per-crate refresh surfaces new architectural questions that re-open Step 1 | `/arch` triages incoming FIXMEs: small clarifications fold into a Step-1 addendum commit; large surfacings get their own substance-scoping addendum and may delay Step 4 |
| Step 3 test-plan revision uncovers spec gaps requiring `/spec` work | `/qa` files FIXMEs to `/spec`; spec gaps surfaced are queued for a future sprint, not gating Sprint 64 close |
| Step 4 plans drift in scope between authoring and Sprint 65 open | `/sprint` runs a wave-gate review of each implementation slice immediately before Sprint 65 opens; trims scope to fit the sprint envelope |

---

## Cross-references

- `design/arch/substance-scoping.md` — substantive findings + resolutions (input)
- `design/arch/reconciliation-plan.md` — procedural reorganisation plan (input)
- `design/arch/CLAUDE.md` — Decision log + canonical-doc pointer table
- `design/arch/principles.md` — architectural principles (cited by Step 1 facade redrafts)
- `design/arch/bounded-contexts.md` — surface BC statements (touched by §1.1 reaffirmation)
- `design/arch/facades/{crate}.md` — facade specs (touched by Step 1a redrafts)
- `sprints/triad-shared.md` — methodology doc (step 7 reworded per §1.5)
- `sprints/SPRINT.md` — current sprint coordination (will reference this plan when Sprint 64 opens)
- `sprints/fixmes/` — cross-skill change requests (triaged in Step 1b; new ones filed in Step 2)

— end of action plan —
