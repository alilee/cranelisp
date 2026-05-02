# Architectural Reconciliation Plan — Sprint 63 close → Sprint 64+

**Status.** Plan only. No document changes, no FIXME filing, no code changes. Authored as a meta-pass after Sprint 63's six master design docs landed and Decisions 38 + 39 reframed `SharedState` and per-symbol mutability.

**Scope.** Reconcile 9 categories of architectural source-of-truth so that the as-designed outputs become **definitive** (one canonical home per question), **viable** (internally consistent, implementation-reachable), and **clean** (obsolete views removed, not lingering).

**Deliverable shape.** Sections §1–§7 answer the seven questions in the brief. Each section gives a concrete recommendation, alternatives considered, and rationale. §8 is the dependency-ordered work breakdown, with owner skill and effort estimate per step.

---

## §1. Information architecture — canonical home per question

### Recommendation

Adopt this canonical-home table. Every architectural question routes to exactly one of these documents. Other documents may *reference*, but never *restate*.

| Reader question | Canonical home | Voice |
|---|---|---|
| What is the system, end-to-end? | `design/arch/overview.md` | newcomer narrative |
| What is each crate responsible for? | `design/arch/bounded-contexts.md` | per-surface essence |
| What is each crate's as-designed public surface? | `design/arch/facades/{crate}.md` (+ `facades/types.md`) | typed signatures |
| What architectural rule governs this? | `design/arch/principles.md` | criteria |
| What was decided that crosses crates/skills? | `design/arch/decisions/NNNN-*.md` (file-based) | one entry per decision |
| How does this crate solve its problem internally? | `design/{crate}/{crate}.md` (master design doc) | per-crate forward-looking |
| How does one feature inside the crate work? | `design/{crate}/<topic>.md` (subordinate) | feature elaboration |
| What is the current as-built state of this crate? | `audits/{crate}-YYYYMMDD.md` | temporal snapshot |
| What invariants do concurrent flows preserve? | `design/arch/sequences/concurrency-*.{mmd,svg}` | proof sketches |
| What happens in time for one execution mode? | `design/arch/sequences/exec-flow-*.{mmd,svg}` | temporal walkthroughs |
| What boundary types and traits cross crates? | `crates/cranelisp-types/` (code) + `interfaces.md` (narrative) | code + companion |
| What is the technical roadmap? | `design/arch/roadmap.md` (delivery in `sprints/ROADMAP.md`) | sequencing |
| Where does the code live? local conventions? | `crates/{crate}/CLAUDE.md` | code's voice |

### Overlaps to resolve

Three overlaps exist today and must collapse:

1. **`design/arch/CLAUDE.md` Decisions §** vs. **`design/arch/decisions/`** — the decisions log is currently inline in CLAUDE.md (Decisions 1–39). The `decisions/` directory exists but is empty. **Resolution:** §4 below; Decisions migrate out of CLAUDE.md, which becomes a navigational pointer file plus local conventions only.

2. **`design/{crate}/{crate}.md`** vs. **`audits/{crate}-*.md`** — both describe the crate's state. **Resolution:** they carry different voices and they do not overlap once disciplined: the master design doc is **forward-looking** (intent — "what should this crate be"); the audit is **backward-looking** (snapshot — "what does the code look like today"). The master design doc cites the audit for current-state and supersedes the audit's *target*-direction commentary; the audit retains current-state authority for its date. Triad-shared.md step 7 already encodes audit precedence for current-state.

3. **`design/arch/sequences/`** vs. **`design/int/concurrency/`** — both contain concurrency diagrams (the latter has compilation-cadence-batch-run, dependency-protocol-target, scheduler-lifecycle, etc.). **Resolution:** `design/arch/sequences/` carries **architectural-altitude** invariant + execution-flow diagrams (cross-crate, cadence-grain). `design/int/concurrency/` carries **int-internal** scheduler/dependency-protocol/cadence-implementation diagrams (within-int detail). The two altitudes are distinct and both retained. Cross-link from int diagrams to the architectural ones; the architectural set is the system view, the int set is the implementation view.

### Alternatives considered

- **Single grand index file.** Rejected — accretes; `MEMORY.md` already shows the failure mode at 286 lines.
- **Auto-generate the canonical-home table from frontmatter.** Premature; six categories of doc do not yet share frontmatter conventions. Manual table for now; revisit if doc count balloons.

### Rationale

`overview.md` already exists and reads as a clean newcomer entry point. Bounded contexts and facades are well-separated by altitude. The principal sources of confusion are (a) the inline-vs-file-based decisions split and (b) which of `design/{crate}/{crate}.md` / audit / facade answers a given question — both are addressable mechanically.

---

## §2. Currency sweep — every artefact classified

For each of the 9 source-of-truth categories below, every instance is classified **canonical** (definitive going forward), **archive** (preserve for history, mark superseded), or **delete** (truly obsolete).

### 2.1 Decision log (`design/arch/CLAUDE.md` Key Decisions)

| Decision | Status | Disposition |
|---|---|---|
| 1, 2, 3, 4, 5, 6 | operative | canonical; migrate to `decisions/` |
| 7 (`CompileMode`) | retracted (deleted Sprint 31) | archive entry under retracted/ — historical |
| 8 (`MacroExpander` trait) | retracted (deleted Sprint 43) | archive entry under retracted/ |
| 9 (`CompiledModule` decomposed) | partially retracted by 22, 25, 38 | archive entry; cross-reference 38 |
| 10–16, 18, 19 | operative | canonical |
| 17 | resolved Sprint 11 | annotate "resolved" status; canonical (its disposition is the current rule) |
| 20 | retracted by 24 | archive |
| 21–27, 29 | operative | canonical |
| 28 | retracted by 31 | archive |
| 30 | operative (reframed but not retracted) | canonical; reframing note inline |
| 31–37 | operative | canonical |
| 38, 39 | operative apex | canonical |

**Rule for migration**: every Decision 1–39 ships as `design/arch/decisions/NNNN-name.md` with frontmatter `status: operative | superseded | retracted | resolved` plus `superseded_by: NNNN` where applicable. The current inline `**RETRACTED…**` notes become frontmatter, not body prose.

### 2.2 Audits (`audits/`)

| File | Status | Disposition |
|---|---|---|
| `frontend-20260423.md` (+ paired diagrams) | as-built snapshot @ 2026-04-23 | canonical-for-date; annotate "Pre-Decisions-38/39; current-state ground truth at audit time" |
| `typecheck-20260423.md` | snapshot; target-direction superseded by 38 | annotate "Current-state preserved; Target-direction sections superseded by master design doc + Decisions 38/39"; canonical-for-date |
| `backend-20260423.md` | snapshot; not materially affected by 38/39 | canonical-for-date; annotate "Pre-38/39; not materially impacted" |
| `src-20260423.md` (= int) | snapshot; target-direction superseded | same as typecheck — annotate target-direction superseded |
| `runtime-*` | **does not exist** | gap — see §3 |
| `platform-*` | **does not exist** | gap — see §3 |

**Rule:** audit files do not get rewritten. Audits are temporally immutable artefacts. Annotation is a single header banner; updates land in the next-cycle audit, not the existing one.

### 2.3 Facades (`design/arch/facades/`)

| File | Status | Disposition |
|---|---|---|
| `int.md` (812 LOC) | rewritten Sprint 63 for Decisions 38/39 | canonical |
| `frontend.md` | inherits Sprint-63 lift; FIXMEs surfaced | canonical with pending FIXME closure (see §5) |
| `typecheck.md` | inherits Sprint-63 lift; FIXMEs surfaced | canonical with pending FIXME closure |
| `backend.md` | inherits Sprint-63 lift; FIXMEs surfaced (compile_to_module return shape) | canonical with pending FIXME closure |
| `runtime.md` | inherits Sprint-63 lift; FIXMEs surfaced (operator primitives, consume_*, runtime_panic, BC drift) | canonical with pending FIXME closure |
| `platform.md` | inherits Sprint-63 lift; FIXMEs surfaced (PlatformError, dispatch, non_exhaustive) | canonical with pending FIXME closure |
| `types.md` | reshape ongoing (ErrorLocation, defn_order, Introspection per 38/39) | canonical |

### 2.4 Sequence diagrams (`design/arch/sequences/`)

| File | Status | Disposition |
|---|---|---|
| `concurrency-symbol-table-entry.{mmd,svg}` | rewritten Sprint 63 for 38/39 | canonical |
| `exec-flow-compilation.{mmd,svg}` | rewritten Sprint 63 for 38/39 | canonical |
| `exec-flow-{repl,run,link,runtime}.{mmd,svg}` | not yet validated post-38/39 | review and confirm or rewrite (M-stage in §8) |
| `concurrency-{got-slot,dependency-service,repl-session,watcher-channel,jit-retention}.{mmd,svg}` | pre-38/39, but invariants survive (no `SharedState` reshape needed for these claims) | canonical with date-stamp; explicit "validated against Decisions 38/39: invariants unchanged" footer |

### 2.5 Bounded contexts (`design/arch/bounded-contexts.md`)

| Section | Status | Disposition |
|---|---|---|
| §§1, 2, 3, 5, 7 (frontend, typecheck, backend, platform, types) | canonical | unchanged |
| §4 (runtime) — explicit out-of-scope of diagnostics | canonical; **but as-built drifts** (`io_trace.rs`, `trace.rs`) | canonical; the drift is implementation-side defect (see §5: filed FIXME for runtime-diagnostics relocation) |
| §6 (Binary/int) — cadences/handoffs/windows | canonical post-Sprint-63 | unchanged |

### 2.6 Overview (`design/arch/overview.md`)

Status: **canonical**. Already names cadences/handoffs/windows; aligns with Decisions 38 + 39. No rewrite needed; spot-check at §8 step.

### 2.7 Master design docs (`design/{crate}/{crate}.md`)

All six are **canonical**, just-landed, with their FIXMEs the operative gap-list. See §5.

### 2.8 Subordinate design docs (`design/{crate}/<topic>.md`)

Per-crate breadth and rough split (master-doc-pass estimates + spot-check):

| Crate | Subordinates | Estimated current / refresh / archive |
|---|---|---|
| `frontend/` | 7 | 4 / 2 / 1 |
| `typecheck/` | 12 | 7 / 3 / 2 |
| `backend/` | 21 | 10 / 6 / 5 |
| `runtime/` | 0 | — (an RC-discipline subordinate is *missing*, proposed FIXME) |
| `platform/` | 4 | 2 / 1 / 1 (`platform-registry-removal.md` archive-worthy post-deletion; `runtime.md` rename collision) |
| `int/` | 30+ | ~12 / 10 / 8+ |

§6 below specifies the lifecycle process. Detailed per-doc disposition is **out of scope here** — this plan recommends the *process*, not the per-doc disposition.

### 2.9 FIXMEs (`sprints/fixmes/` + inline)

- 9 FIXMEs filed (0001–0009). All canonical / open.
- ~40 inline proposals across the six master design docs; not yet filed. See §5 for triage strategy.

### Archive convention

Recommend **per-crate `archive/` subdirectory** alongside the existing `design/arch/archive/`:

- `design/{crate}/archive/` for subordinate docs whose work has closed
- `design/arch/archive/` continues as today for arch-level retired material
- `design/arch/decisions/retracted/NNNN-*.md` for retracted/superseded decisions (kept inside `decisions/` so the chronological sequence is intact, but in a subdirectory so `ls decisions/` is the operative-only view)
- `audits/` already operates as immutable history — no archive subdirectory needed

Header convention for archived docs (one block at the top of every archived file):

```
---
status: archived
archived_at: YYYY-MM-DD
archived_in_sprint: NN
superseded_by: <path>   # if superseded by another doc; omitted if just retired
reason: <one line>
---
```

### Alternatives considered

- **Delete superseded decisions outright.** Rejected — the prompt forbids it ("decision-museum noise" is the failure mode, but per the root CLAUDE.md and `/arch` skill def, `archive/` is a *navigable graveyard, not a wastebasket*).
- **Keep all decisions inline forever.** Rejected — Sprint 63 already directionally moved to `decisions/` (M3 task); CLAUDE.md is approaching token-read-limit (32k tokens, exceeded). Migration is forced by mechanical pressure, not just aesthetics.
- **One central `archive/` for everything.** Rejected — per-crate archive keeps subordinate-doc retirement local to the owning skill; it reduces cross-skill diff churn and matches the file-ownership boundary.

---

## §3. Audit reconciliation

### Recommendation

**Annotate-and-defer** for existing audits; **schedule a new full audit pass** as Sprint 64 wave-0 deliverable.

Concretely:

1. **Annotate the four 2026-04-23 audits in place** with a single header banner indicating: (a) audit date; (b) "Current-state preserved as ground truth at date"; (c) "Target-direction sections — see master design doc + Decisions 38/39 for current direction"; (d) link to the relevant master design doc. **No body changes.** The audit's current-state findings remain verbatim; they are temporally immutable evidence.

2. **Author a runtime audit and a platform audit** (currently absent). Done in the next audit pass — not in-session, scheduled in §8.

3. **Schedule a new full audit pass** dated post-Decisions-38/39 implementation landing. The new pass:
   - One audit per surface, six total (frontend, typecheck, backend, runtime, platform, src/int)
   - Date-stamped (next pass would be `{crate}-YYYYMMDD.md` reflecting actual audit date)
   - Authored by `/design` per crate (the same role that wrote master design docs); `/design`'s audit-aware methodology validated in Sprint 63

4. **Cadence going forward.** Audit cadence should be triggered by **major architectural shifts** (Decisions 38/39 are the canonical example), not on a calendar. Triad's `triad-shared.md` step 7 already gives audits precedence for current-state — that rule is sufficient day-to-day; full audits exist for the moment after a pivot when the master design doc and audit need to be re-paired.

### Alternatives considered

- **Re-author the four existing audits to reflect 38/39.** Rejected — audits are *temporal snapshots*; rewriting them destroys the historical record of "what the code looked like before the pivot." The four audits are evidence, not recommendations.
- **Treat master design docs as the new audit equivalent.** Rejected — master design docs are forward-looking design intent; audits are backward-looking implementation snapshots. Conflating them loses the diagnostic value of "design said X but reality is Y" pairing (which Sprint 63 explicitly relied on per `triad-shared.md` step 7).
- **Skip audits for runtime + platform indefinitely.** Rejected — the runtime master design doc surfaced bounded-context drift (`io_trace.rs`, `trace.rs` — ~25% of LOC) precisely because there *was* no audit pinning current-state for cross-check. Audit absence creates exactly the kind of design-vs-reality blind spot the audit-aware methodology exists to close.

### Rationale

The annotate-and-defer approach respects the immutability of evidence (audits are dated for a reason — `triad-shared.md` step 7 explicitly favours the most-recent dated audit) while not pretending the post-38/39 master design docs supersede every line in the audits. The "schedule a new pass" recommendation makes the audit/master pairing **periodic** at architectural pivots, which matches the actual pattern of when audit-vs-design tension surfaces.

---

## §4. Decision log evolution

### Recommendation

**Path (a) refactored into a status-tagged file-based register** — extract Decisions 1–39 from `design/arch/CLAUDE.md` into `design/arch/decisions/NNNN-name.md`, one file per decision, with explicit `status:` frontmatter. Retracted decisions move to `design/arch/decisions/retracted/`. The CLAUDE.md "Key Decisions" section becomes a one-page index pointing into `decisions/`.

### File structure

```
design/arch/decisions/
├── 0001-seven-plus-one-crate-dag.md
├── 0002-cranelisp-types-data-only.md
├── ...
├── 0017-traits-as-cl-files.md          # status: resolved
├── 0021-tc-sourced-call-graph.md
├── ...
├── 0030-mutual-import-deadlock-constraint.md
├── 0031-jitmodule-per-batch.md
├── ...
├── 0038-shared-state-formal-definition.md
├── 0039-introspection-source-error-location.md
├── INDEX.md                             # operative-only chronological summary
└── retracted/
    ├── 0007-compile-mode-enum.md       # superseded_by: pipeline-v4 (no Decision number)
    ├── 0008-macro-expander-trait.md
    ├── 0009-compiledmodule-decomposed.md  # superseded_by: 0022, 0025, 0038
    ├── 0020-split-calling-convention.md   # superseded_by: 0024
    └── 0028-per-worker-jit.md             # superseded_by: 0031
```

### Frontmatter

```yaml
---
number: 38
title: SharedState formal definition; per-symbol mutability; mode-conditional Introspection
status: operative                  # operative | superseded | retracted | resolved
sprint_filed: 63
phase: 7-7+1                       # phase grouping label as today
supersedes: 0009                   # numbers; can be array
superseded_by:                     # set when this decision is later retracted
canonical_locations:               # files this decision binds to
  - design/arch/facades/int.md
  - crates/cranelisp-types/src/module.rs
related_principles: [7, 11, 6, 3]
---
```

The Decision body keeps current text verbatim. Migration is mechanical: extract → frontmatter → file. **No content rewrite as part of this step.** The retraction notes already inline (e.g., Decision 20's "RETRACTED (Sprint 56 Step 2c, superseded by Decision 24)") become frontmatter `status: retracted` + `superseded_by: 24`, and the body text stays.

### What CLAUDE.md becomes

After migration, `design/arch/CLAUDE.md` carries:
- Local conventions for `design/arch/`
- Pointer to `decisions/` and `decisions/INDEX.md`
- Short "How to file a Decision" (numbering rule, frontmatter, where to put retracted)
- Cross-references (already there)
- "String Newtypes" + "Conventions" sections (kept; these aren't Decisions)

Estimated post-migration CLAUDE.md size: ~80 lines (vs current 361).

### Alternatives considered

- **(b) Split into active-decisions vs decision-history.** Rejected — fragments chronological sequence; "what decision number does this reference" becomes ambiguous (which file does 0009 live in?). The retracted-as-subdirectory variant of (a) preserves the sequence intact.
- **(c) Leave inline with retraction notes everywhere.** Rejected — CLAUDE.md exceeds Read-tool token limits (32k tokens), forcing offset/limit reads. Operationally expensive every time `/arch` or any subagent touches it. Mechanical pressure forces the migration.
- **(d) Prose narrative rewrite.** Rejected — destroys retrievability by number ("Decision 38" is the project's lingua franca; flattening it into prose breaks every cross-reference).

### Consequence for new readers

After migration: a new reader visits `design/arch/decisions/INDEX.md` (~50 lines, status-tagged numerical list with one-line summaries), navigates to the specific `NNNN-*.md` for full context. Retracted decisions are reachable but out of the operative path. CLAUDE.md becomes a "where things live" pointer, not a content store.

### Rationale

The decision log is the project's most-cited reference (Decisions 25, 31, 38, 39 are named in nearly every Sprint-63 design doc). File-based gives:
- Direct tool access without offset/limit pagination
- Per-decision frontmatter for mechanical scanning (e.g., "list all operative decisions about RC")
- Clean diff history per decision
- Subdirectory split for retracted/operative without breaking numbering

The inline-with-retraction-notes status was sustainable through Decision ~30 and is now structurally over its useful life.

---

## §5. FIXME triage strategy

### Recommendation

**Three-bucket triage**, applied to each of the ~40 inline FIXMEs across the six master design docs:

- **Lift to `sprints/fixmes/`** — concrete cross-skill request, target named, scope sized for a wave.
- **Merge into existing `sprints/fixmes/`** — refines or duplicates an already-filed FIXME (0001–0009).
- **Elevate to a Decision** — the inline FIXME is asking a question whose answer should bind future work, not a one-off task.

Triage is `/sprint`'s next-up task at Sprint 64 open. `/sprint` files the lifted FIXMEs as numbered `0010+`-prefixed entries, drafts Decision proposals (which `/arch` then accepts or amends), and confirms merges with a comment in the existing FIXME file.

### Approximate triage by master doc

The ~40 inline FIXMEs were enumerated (sometimes grouped under "Open questions / proposed FIXMEs"). Per-doc estimates:

| Doc | Count | Lift | Merge | Elevate to Decision | Notes |
|---|---|---|---|---|---|
| `frontend.md` | ~6 | 4 | 1 (into 0008-shape) | 1 (`Ast = TopLevel` alias clarity) | Mostly facade silence — small lift each |
| `typecheck.md` | ~6 | 3 | 2 (into 0002, 0008) | 1 | Tight coupling to 0008/0009 already filed |
| `backend.md` | ~5 | 3 | 1 (into 0003) | 1 (`compile_to_module` return shape — facade-spec change) | The return-shape question is binding |
| `runtime.md` | ~9 | 6 | 0 | 3 (BC drift relocation, scheduling-class plumbing, runtime_panic carries ErrorLocation) | Largest concentration of facade silence + BC drift |
| `platform.md` | ~6 | 4 | 1 (into 0001) | 1 (PlatformError + ErrorLocation adoption — cross-Decision-39 binding) | One naming-collision rename |
| `int.md` | ~7 | 5 | 0 | 2 (lib.rs facade narrowing, dependency-registration consolidation) | int's are mostly process-quality |
| **Total** | **~39** | **~25** | **~5** | **~9** |

### Lift template

The 25 to-be-lifted FIXMEs follow the existing `sprints/fixmes/NNNN-name.md` shape (per `sprints/METHOD.md` §3.3). `/sprint` allocates numbers `0010` onward. Frontmatter: `target`, `filed_by: /sprint` (since `/sprint` is doing the migration), `filed_at: <date>`, `sprint_filed: 64`, `refers_to: design/{crate}/{crate}.md §<section>`, `status: open`.

### Merge template

Existing FIXMEs that absorb a master-doc inline get a `## Sprint 64 merge note` section appended, naming the master-doc section the inline came from and confirming the existing FIXME's resolution covers it.

### Decision-elevation template

The ~9 elevated proposals become Decision drafts. `/arch` is the gate: each draft Decision sits as a `decisions/proposed/NNNN-draft.md` until `/arch` accepts (move to `decisions/`), amends, or rejects (file as a regular FIXME). Examples of likely Decision elevations:
- *"Compile_to_module return shape (Arc<Jit>, HashMap<Symbol, *const u8>)"* — binds backend facade + int's `Code::Jit`/`Code::Linker` construction site.
- *"Runtime diagnostics relocation (io_trace, trace → int)"* — bounded-context boundary change; binds the runtime crate scope.
- *"PlatformError adopts ErrorLocation per Decision 39"* — cross-Decision-39 platform-side application; binds `crates/cranelisp-platform/` public surface.

### Alternatives considered

- **File all 40 as fresh FIXMEs.** Rejected — bloats the queue with items already covered by 0001–0009 (e.g., `non_exhaustive` adoption is 0001-blocked; refiling as 0010 obscures the dependency).
- **Leave inline as authoritative.** Rejected — defeats the purpose of having `sprints/fixmes/` as the protocol; per the root CLAUDE.md "Inline FIXMEs are the OLD protocol."
- **`/arch` does triage in-line.** Rejected — `/sprint` owns scope arbitration; FIXME triage is scope arbitration. `/arch` stays as Decision-gate.

### Rationale

Concentration matters: the largest cluster (runtime — 9 FIXMEs) is the surface with the most BC drift + facade silence; the lightest cluster (backend — 5) is the most-recently-decided. Triage frees the cluster work for Sprint 64 waves rather than keeping it stranded as inline prose readers must hunt for.

---

## §6. Subordinate-doc lifecycle

### Recommendation

**Three-phase lifecycle with `/design` as authoring gate, per-crate `archive/` subdirectory.**

Phase 1 — **classification** (one-shot):
- Each crate's `/design` invocation, on next narrow-deployment, runs a subordinate-doc currency sweep alongside its design work. Each subordinate gets stamped with one of:
  - **current** — referenced by master, content reflects current direction
  - **refresh-worthy** — referenced by master, content needs Decisions-38/39 update
  - **archive-worthy** — work closed; lessons folded into master or a Decision

Phase 2 — **action**:
- Current → no action.
- Refresh-worthy → `/design` revises in place during its next per-crate invocation (queued as a Sprint 65+ task).
- Archive-worthy → moves to `design/{crate}/archive/` with the archive header (see §2.9). The master design doc's pointer table is updated to reflect the move OR the pointer is removed if the doc is no longer referenced.

Phase 3 — **ongoing maintenance**:
- Per `/design` skill def §"Feature design subordinate to crate design": when a feature design changes the crate's overall shape, the master is updated FIRST; then the subordinate elaborates. This is the existing rule; it remains.
- Each `/design` invocation reviews the master's pointer table for currency at start. Stale rows are addressed in the same wave (move to archive or refresh).

### Authoring rule

`/design` (narrow per crate) is the sole authoring authority for subordinate-doc retirement. Reason: the subordinate is a per-crate concern, and `/design` is the per-crate forward-looking voice. `/arch` does not edit subordinate docs; `/dev` does not edit them.

`/sprint` does not retire subordinate docs either, but `/sprint` may schedule the per-crate `/design` retirement-sweep wave when the master design doc's pointer table shows a critical mass of stale rows.

### Per-crate archive directory convention

```
design/{crate}/
├── {crate}.md                 # master
├── topic-a.md                 # current
├── topic-b.md                 # current
├── CLAUDE.md                  # local conventions (owned by /dev)
└── archive/
    ├── topic-c.md             # archived; carries header
    └── topic-d.md
```

`design/arch/archive/` continues to host arch-level archives (existing convention).

### Special cases

1. **Naming collision: `design/platform/runtime.md` vs `design/runtime/runtime.md`.** Rename the platform-side doc to `design/platform/platform-runtime-interface.md` (per the platform master's proposed FIXME). Lift to a `sprints/fixmes/` filed by `/sprint` during triage, target `/design` for platform.

2. **Missing crate-level `CLAUDE.md`s.** The runtime master design doc surfaced that `crates/cranelisp-runtime/CLAUDE.md` is missing. Each crate's `/dev` invocation owns its `CLAUDE.md`; this is a `/dev` task per surface.

3. **`design/int/concurrency/` subdirectory.** Already has its own `archive/` per the git status diff (Sprint 63 prep). Pattern is established for int — generalise to other crates.

### Alternatives considered

- **Date-stamped supersession only (no file moves).** Rejected — leaves stale prose in the working set; readers can't tell "current direction" from "old direction" without reading every doc.
- **`/arch` retires subordinate docs.** Rejected — violates per-crate authoring discipline; `/arch` would have to know each crate's domain to judge currency.
- **Auto-archive based on last-edit date.** Rejected — design intent doesn't decay on a clock; some old docs are still correct (e.g., `traitimpl-symbol-table.md`).

### Rationale

`/design` is already the per-crate forward-looking voice and runs its own subordinate-doc pointer table. Promoting that table to a lifecycle artefact (with `archive/` move as the closing action) is a small extension of an existing rule. The per-crate archive subdirectory keeps retirement local to the owning skill and avoids a centralized graveyard that no skill maintains.

---

## §7. Sequencing

### Recommendation

Six waves, with parallelisation where the work is genuinely independent. `/sprint`-coordinated; `/arch`-arbitrated for cross-cutting; `/design` for per-crate.

```
Wave 0 — Sprint 63 close pre-archive (in-flight)
  - User reviews and accepts this plan
  - /sprint accepts plan as Sprint 64 input
  
Wave 1 — Decision log migration  ← UNBLOCKS WAVES 2, 3, 5
  - Mechanical extract → decisions/NNNN-*.md
  - One PR; /arch authors
  
Wave 2 — FIXME triage (parallel with Wave 3)
  - /sprint runs three-bucket triage on ~40 inline FIXMEs
  - Lifts ~25 as 0010+, merges ~5, drafts ~9 Decision proposals
  - /arch accepts/amends/rejects Decision drafts
  
Wave 3 — Audit annotation (parallel with Wave 2)
  - 4 existing audits get header banners
  - /arch authors banners; small mechanical pass
  
Wave 4 — Subordinate-doc currency sweep (parallel across 6 crates)
  - Each /design narrow invocation classifies subordinates
  - Archive-worthy moved; refresh-worthy queued for own-skill next wave
  - 6 parallel skills; 6 PRs
  
Wave 5 — New audit pass (post-implementation of major 38/39 follow-ons)
  - Triggered when Decisions 38/39 implementation completes
  - 6 audits authored; runtime + platform fill the gap
  - Scheduled for Sprint 64+N where N depends on landing pace of 0008/0009/etc.
  
Wave 6 — Pre-existing exec-flow sequence diagram review
  - exec-flow-{repl,run,link,runtime}.{mmd,svg} validated against post-38/39 model
  - Either confirmed (footer note) or rewritten
  - /arch executes; small wave
```

### Parallelism

- **Wave 1 must finish before Wave 2** (Decision-elevation in triage needs the file-based registry to land in).
- **Waves 2 and 3 run in parallel** (independent — FIXMEs vs audit headers).
- **Wave 4 can start once Wave 1 lands** (subordinate-doc sweep references decision numbers in archive headers).
- **Wave 5 is gated on implementation work landing** — not on this plan.
- **Wave 6 runs whenever** — independent of the others.

### Owner skill per wave

| Wave | Owner | Sub-owners | Effort |
|---|---|---|---|
| 0 | user + `/sprint` | — | minutes (review + accept) |
| 1 | `/arch` | — | ~3–4 hours (39 decisions × mechanical extract; CLAUDE.md rewrite) |
| 2 | `/sprint` | `/arch` (Decision drafts) | ~4–6 hours (40 FIXMEs × triage + ~9 draft Decisions) |
| 3 | `/arch` | — | ~1 hour (4 audits × header banner) |
| 4 | `/design` × 6 | — | ~2–3 hours per crate × 6 = 12–18 hours total, parallel |
| 5 | `/design` × 6 | — | ~4–6 hours per crate × 6 = 24–36 hours total, **scheduled separately** |
| 6 | `/arch` | `/sprint` for exec-flow review | ~2–3 hours |

### Alternatives considered

- **Sequential single-thread.** Rejected — Waves 2 and 3 are genuinely independent and Wave 4 is parallel-by-construction; serializing wastes wall-clock time.
- **Wave 5 first (re-audit before reconciliation).** Rejected — audits are a snapshot of *implementation* state; reconciling design-side artefacts shouldn't wait on implementation. Wave 5 happens when implementation has caught up to the post-38/39 design.
- **Skip Wave 4 (subordinate doc lifecycle process).** Rejected — leaves the subordinate-doc accretion problem unsolved; the very issue the methodology is trying to address.

### Rationale

The dependency edges are mostly soft (Wave 1 → 2 only because Decision drafts land in `decisions/`; could be deferred to first-elevation in Wave 2). The plan errs on the side of clean sequencing because Wave 1 is small and is `/arch`'s direct ownership, so doing it first costs little.

---

## §8. Dependency-ordered work breakdown

This is the actionable form of the seven recommendations above. Each step is sized to a single skill-invocation.

| # | Step | Owner | Depends on | Est. effort | Output |
|---|---|---|---|---|---|
| 0 | User reviews this plan; `/sprint` accepts as Sprint 64 input | user + `/sprint` | — | minutes | accepted plan |
| 1 | Create `design/arch/decisions/INDEX.md` skeleton + `retracted/` subdirectory | `/arch` | 0 | 30 min | scaffolding |
| 2 | Migrate Decisions 1–6 to `decisions/0001..0006` with frontmatter | `/arch` | 1 | 30 min | 6 files |
| 3 | Migrate Decisions 7, 8, 20, 28 to `decisions/retracted/` | `/arch` | 1 | 20 min | 4 files |
| 4 | Migrate Decision 9 (partially retracted) to `retracted/` with `superseded_by: [22, 25, 38]` | `/arch` | 1 | 10 min | 1 file |
| 5 | Migrate Decisions 10–19 (Ring 1 / Ring 2A) | `/arch` | 1 | 30 min | 10 files |
| 6 | Migrate Decisions 21–27, 29 (Pipeline v4) | `/arch` | 1 | 30 min | 8 files |
| 7 | Migrate Decisions 30–37 (large bodies — 30 mins for 31 alone) | `/arch` | 1 | 90 min | 8 files |
| 8 | Migrate Decisions 38, 39 (apex) | `/arch` | 1 | 20 min | 2 files |
| 9 | Author `decisions/INDEX.md` body — operative-only chronological listing with one-line summaries | `/arch` | 2–8 | 30 min | INDEX.md |
| 10 | Rewrite `design/arch/CLAUDE.md` — drop Key Decisions §§; replace with pointer | `/arch` | 9 | 30 min | rewritten CLAUDE.md (~80 LOC) |
| 11 | `/sprint` triages ~40 inline FIXMEs; lifts ~25, merges ~5, drafts ~9 Decision proposals | `/sprint` | 9 | 4–6 hr | ~25 new FIXME files; ~9 draft Decisions |
| 12 | `/arch` reviews ~9 draft Decisions; accepts (move to `decisions/`), amends, or rejects (file as FIXMEs) | `/arch` | 11 | 1–2 hr | ~9 accepted/amended Decisions |
| 13 | Annotate 4 existing audits with header banners (in parallel with 11–12) | `/arch` | — | 1 hr | 4 banners |
| 14 | Address `design/platform/runtime.md` rename (one of the lifted FIXMEs from step 11) | `/design` (platform) | 11 | 30 min | renamed file + cross-refs |
| 15 | Per-crate subordinate-doc currency sweep — `/design` × 6 in parallel | `/design` × 6 | 9 | 2–3 hr/crate × 6 | per-crate `archive/` subdirs populated; master pointer tables refreshed |
| 16 | Author missing `crates/cranelisp-runtime/CLAUDE.md` and any other missing per-crate CLAUDE.md | `/dev` × N | — | 30–60 min/crate | filled gaps |
| 17 | Validate exec-flow sequence diagrams against post-38/39 model (4 diagrams) | `/arch` | 9 | 2–3 hr | confirmation footers OR rewrites |
| 18 | Schedule Sprint 64+N audit pass (no work yet — milestone marker) | `/sprint` | — | minutes | sprint roadmap entry |
| 19 | Sprint 64+N: 6 new audits authored (frontend + typecheck + backend + int + new runtime + new platform) | `/design` × 6 | implementation lands | 4–6 hr/crate × 6 | post-pivot audit suite |

### Estimated total wall-clock

- Steps 0–10: **~6 hours `/arch` solo** (wave 1)
- Steps 11–14: **~6–8 hours `/sprint` + `/arch`** (waves 2–3, parallel with each other, sequential after wave 1)
- Step 15: **~12–18 hours, parallelised across 6 `/design` invocations** (wave 4) — wall clock 2–3 hours if parallelised, calendar 1–2 days
- Step 17: **~2–3 hours `/arch`** (wave 6)
- Step 19: **future — gated on implementation**

If sprints are sized to 4–6 days of D/D/R cycles, this reconciliation takes one wave gate (Sprint 64 wave 1) plus a follow-on subordinate-doc sweep (wave 2). The new-audit pass slots into a later sprint.

### Ready signals

The reconciliation is **complete** when:

1. `design/arch/decisions/` holds all Decisions; `CLAUDE.md` no longer hosts Decision bodies.
2. `sprints/fixmes/` holds the lifted FIXMEs; master design docs no longer carry "Open questions / proposed FIXMEs" sections (or those sections explicitly say "no open items").
3. Each crate has its `archive/` subdirectory populated; each master design doc's pointer table is current.
4. Existing audits carry annotation banners; new-pass audits exist for runtime and platform.
5. `overview.md` reads as the newcomer entry point with no inconsistencies against the post-38/39 model.

These five signals are independently verifiable and cumulatively prove the as-designed architecture is **definitive** (one home per question), **viable** (cross-doc consistency holds), and **clean** (obsolete views archived, not lingering).

---

## Cross-references

- `design/arch/CLAUDE.md` — current decision log + canonical-doc pointer (target of step 10)
- `design/arch/principles.md` — architectural principles (referenced by Decisions and triage criteria)
- `design/arch/bounded-contexts.md` — per-surface bounded contexts (canonical; cited by master design docs)
- `design/arch/facades/{crate}.md` — per-surface facade specs (post-Sprint-63)
- `design/{crate}/{crate}.md` — six master design docs (Sprint 63 deliverables; FIXME source)
- `audits/{crate}-20260423.md` — four existing audits (target of step 13)
- `sprints/fixmes/0001..0009-*.md` — already-filed FIXMEs (target of merges in step 11)
- `sprints/triad-shared.md` — triad procedure (audit-precedence rule at step 7 — referenced in §3)
- `sprints/METHOD.md` — methodology, FIXME format

— end of plan —
