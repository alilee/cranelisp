# Sprint 65 reshape — Phase 2 architecture review

**Status.** Phase 2 review of the *reshape* of Sprint 65 into a facade-completion-to-final-state sprint. Pairs with `design/arch/sprint-65-phase-2-review.md` (the prior Phase 2 review of the original adoption-feasibility scope; superseded as the sprint shape changed) and `design/arch/sprint-65-legacy-triage.md` (the in-session triage that surfaced the gaps which precipitated the reshape).

**Author.** `/arch`, 2026-05-06, in-session.

**Brief.** `sprints/SPRINT.md` Phase 2 calls for a `/arch` verdict on four dimensions of the reshaped sprint: scope completeness, authoring dependency graph, per-crate implementation-slice template, and endgame check ("is the facade truly final after S65?"). Phase 2 verdict gates Phase 3.

---

## 1. Scope completeness

The completeness check pairs the SPRINT.md scope against four sources of facade-load-bearing commitments: the active Decisions register, `legacy/substance-scoping.md` §1 + §2 items, `legacy/substance-action-plan.md` Step-4 per-skill slices, and the per-crate `design/{crate}/{crate}.md` master docs. Active FIXMEs and `memory/` are also crossed.

### 1.1 Active Decisions register coverage

10 active Decisions: 0010, 0011, 0027, 0030, 0031, 0035, 0040, 0041, 0042, 0043.

| Decision | Subject | Surfaces in (after S65) | In SPRINT.md scope? |
|---|---|---|---|
| 0010 | Base-pointer ABI | runtime → intrinsics.md (heap header layout); types.md (`HeapHeader`, `NULLARY_TAG_THRESHOLD`) | ✓ implicit — survives Decision 43 split; new intrinsics.md must reflect |
| 0011 | Embedded `drop_glue_ptr` in closures | intrinsics.md (drop glue + closure layout) | ✓ implicit — must surface in new intrinsics.md |
| 0027 | G8 lands before G9 | int.md (worker model — persistent workers per Decision 27); already cited in int facade §"Bounded-context invariants" #2 | ✓ already in facade (no change) |
| 0030 | Mutual-import deadlock constraint | int.md (already cited as known constraint #14); bounded-contexts §6 | ✓ already in facade (no change) |
| 0031 | One JITModule per compile batch (+ S64 per-symbol amend per Decision 41) | backend.md `Jit` type + `compile_to_module` cardinality | ✓ in scope via Decision 41 follow-through |
| 0035 | `Code` enum integration layer (S64 amended — `Code` lives in backend) | backend.md (Code type), int.md (re-export) | ✓ in scope via Decision 41 |
| 0040 | `trace.rs`/`io_trace.rs` relocate to int; runtime keeps `IoObserver` callback | runtime.md → intrinsics.md (post-D43); int.md (consumer side) | ✓ in scope (FIXME 0103 reflected) |
| 0041 | per-symbol JIT, mutref shared-state writes, `Result<(), CompilationError>` | backend.md, int.md | ✓ in scope (explicit row) |
| 0042 | `PlatformError` adopts `ErrorLocation` | types.md, platform.md | ✓ in scope |
| 0043 | Runtime split into primitives + intrinsics | new primitives.md + intrinsics.md; backend.md depends-on update; runtime.md retires | ✓ in scope (W1) |

**Verdict — Decisions:** clean. Every active Decision is reflected in the in-scope facade work. The Decisions register IS the load-bearing item set for this sprint.

### 1.2 `legacy/substance-scoping.md` §1 + §2 coverage

Scoping pass items, ordered by section:

| Item | Subject | In S65 scope? | Notes |
|---|---|---|---|
| §1.1 | Runtime BC drift — `trace`/`io_trace` relocate; `IoObserver` callback | ✓ | bounded-contexts §4 retire; FIXME 0103 facade-shape reflected. Under D43 the IoObserver lives in `cranelisp-intrinsics` (per substance-scoping §1.7's note). SPRINT.md scope for intrinsics.md says "IO observer extension point" — captures it. |
| §1.2 | `compile_to_module` per-symbol JIT, mutref, `Result<(), Err>` (Decision 41) | ✓ | backend.md + int.md row in scope. Bundles §2.6 + §2.7 per substance-scoping Chain C. |
| §1.3 | `PlatformError` adopts `ErrorLocation` (Decision 42) | ✓ | types.md + platform.md row. |
| §1.4 | Frontend `SymbolTables` alias generic form | ✓ already in current frontend.md (lines 27–46 use `SymbolTables<C, L>`) | facade landed S64; nothing more needed |
| §1.5 | Methodology — audits as point-in-time opinion | n/a | Methodology, not facade. Was deferred from action-plan Step 1c per `substance-action-plan.md` line 13; lives outside `/arch` scope this sprint. Not a gap. |
| §1.6 | Runtime + platform audit gap dissolves under §1.5 | n/a | Methodology disposition; no facade impact. |
| §1.7 | Decision 43 — runtime split | ✓ | The headline of W1. New primitives.md + intrinsics.md; runtime.md retires; bounded-contexts §4 → §4a + §4b. |
| §2.1 | Frontend public surface — parse + extract + per-form build | ✓ already landed in frontend.md (lines 16–25) | facade landed S64; SPRINT.md row `§2.1 parse(source) reshape` is redundant/already-done. **Minor**: SPRINT.md scope row could note "already landed S64; verify on review pass" — not a real gap. |
| §2.2 | Ast/TopLevel alias dissolves | n/a (subsumed by §2.1) | already resolved |
| §2.3 | MacroEnv dead-code | n/a | demoted to procedural P19 in scoping; out of facade scope |
| §2.4 | `ResolutionGap` rustdoc | ✓ | `facades/types.md` already has producer-rustdoc on each variant (lines 354–363, 579–586). Already landed S64. Not a gap. |
| §2.5 | `CheckError::Gap` partial-state | n/a | dissolved (not-an-issue) |
| §2.6 | `JitSymbol` → `LinkerSymbol` rename | ✓ already landed in types.md line 22 + backend.md line 141 | facade landed S64; SPRINT.md row "§2.6 LinkerSymbol rename" is a verify-on-review item, not new work. **Minor**: same as §2.1 — slight scope-row redundancy. |
| §2.7 | `CompilationError::SymbolNotCompilable` typed variant | ✓ already landed in backend.md lines 84–101 | facade landed S64; SPRINT.md row "§2.7 typed error variant" is verify-on-review. |
| §2.8 | Backend GOT-slot population log | ✓ via FIXME 0099 (GotObserver) — already in backend.md lines 150–166 | facade landed S64; SPRINT.md scope reaffirms FIXME 0099 reflection — fine. |
| §2.9 | Effect-node scheduling class | deferred per scoping; inline FIXME at `io.rs:174` | not in S65 scope. Not a gap. |
| §2.10 | `runtime_panic` stays flat-String | resolved (nothing to do) | not a gap |
| §2.11 | `runtime_panic` facade truth-telling | ✓ already in current runtime.md lines 159–165 | facade landed S64; carries forward into intrinsics.md under D43 |
| §2.12 | Runtime facade silence dissolves under §1.7 | absorbed by D43 (W1) | covered |
| §2.13 | `HostContext::dispatch` retire | ✓ already in platform.md lines 137 + 311 | facade landed S64; carries on |
| §2.14 | Int observability formalisation | deferred (subordinate-doc systemic) | not in S65 |

**Verdict — substance-scoping:** every load-bearing item is either (a) already landed in current facades (§1.4, §2.1, §2.4, §2.6, §2.7, §2.11, §2.13), (b) in S65 scope as new work (§1.1, §1.2, §1.3, §1.7, §2.8 via FIXME 0099, §2.12 via D43), or (c) explicitly deferred (§1.5, §1.6, §2.3, §2.5, §2.9, §2.10, §2.14). **No gaps.**

**Minor scope-rows redundancy noted.** SPRINT.md §1.2 Decision 41 / §2.1 / §2.6 / §2.7 are framed as "additions" but are already reflected in the S64 facades (commits `19124fa`, `3ccbb44`, `56c75a8`, `de98bf0`). Under the reshape, what `/arch` actually does for these in S65 is *re-validate against the now-final shape* (does the §1.2 Decision-41 wording in backend.md match exactly what int.md expects after D43's intrinsics.md lands? does §2.6 need any phrasing tightening once the bounded-contexts split lands? etc.). This is verification + light revision work, not new authoring. SPRINT.md's wording could clarify "verify + tighten" vs. "author from scratch", but the scope itself is correct.

### 1.3 `legacy/substance-action-plan.md` Step-4 retro

Step 4 (per-skill implementation slices) was never executed. SPRINT.md's "Per-crate implementation slices (Step-4 retro)" section in scope explicitly executes Step 4 against the now-final S65 facades. Eight deliverables enumerated:

> 8 docs total (frontend, typecheck, backend, runtime-retiring, platform, primitives, intrinsics, int — plus `/qa` test plan for S66).

Cross-checked against `substance-action-plan.md` lines 297–311 — Step 4's seven per-skill rows: `/design (frontend)`, `/design (typecheck)`, `/design (backend)`, `/design (runtime)`, `/design (platform)`, `/design (int)`, `/qa`. Plus the Decision-43 retiring/migrating slices: runtime *retires*, primitives + intrinsics *new*. The S65 reshape correctly inflates Step 4's seven to nine slices (frontend, typecheck, backend, runtime-retiring, platform, primitives, intrinsics, int + `/qa`). **Step-4 coverage in scope is complete.**

The action-plan Step 4 row scope items per skill:

| Action plan row | Item to capture in S65 | In S65 scope? |
|---|---|---|
| Frontend | First-wave §1.4 + §2.1 facade adoption work; new public surface tests | ✓ in `/design (frontend)` slice |
| Typecheck | §2.4 rustdoc; Decision 38/39 implementation gaps | ✓ in `/design (typecheck)` slice |
| Backend | First-wave §1.2 (D41 implementation) + §2.6 + §2.7 | ✓ in `/design (backend)` slice |
| Runtime | §1.1 IoObserver exposure; trace/io_trace relocation prep; §2.11 panic facade | ✓ in retiring `/design (runtime)` slice (calls out the migration into primitives + intrinsics) |
| Platform | §1.3 PlatformError migration; §2.13 dispatch removal | ✓ in `/design (platform)` slice |
| Int | §1.1 receive-side; §1.2 receive-side; SharedState Decision 38 finalisation | ✓ in `/design (int)` slice |
| `/qa` | First-wave integration + e2e infrastructure uplift; substance-commitment tests | ✓ in `/qa` slice |

**Verdict — Step-4 retro:** complete. The eight + qa = nine deliverables capture every per-skill scope item the action plan called for.

### 1.4 Per-crate `design/{crate}/{crate}.md` cross-check

Read all six per-crate master design docs. Findings:

| Crate | Facade-load-bearing claim | Captured in SPRINT.md? |
|---|---|---|
| frontend | FIXME 0098 Phase 2 — `expand` migrates from `src/expander.rs` into frontend; multiple lines cite this as the largest single gap | ✓ FIXME 0098 in scope (S66 implementation; facade reflects post-implementation shape per SPRINT.md "Facades reflect post-implementation shape") |
| typecheck | FIXME 0008 + 0098 Phase 3 — `check_form` free-function shape; SymbolTable mutability discipline; CheckError/ResolutionGap relocation from types→typecheck (Principle 15) | ✓ typecheck.md row mentions D38/D39 reflected, ResolutionGap rustdoc spec, CheckResult/CheckError finals; the relocation per FIXME 0100 covers Principle-15 placement |
| backend | Decision 41 follow-through; `Code` move from src/ to backend; CompilationError variants; `compile_to_module` signature; FIXME 0099 (GotObserver), FIXME 0108 (display.rs to int), FIXME 0100 (single-consumer relocations) | ✓ all in backend.md scope row |
| runtime | Decision 40 (`IoObserver`); `trace`/`io_trace` relocate per FIXME 0103; Decision 42 / `runtime_panic` stays flat-String per §2.10 | ✓ runtime *retires* under D43; covered by primitives.md + intrinsics.md scope rows |
| platform | Decision 42 / `PlatformError`; `HostContext::dispatch` retired (§2.13); `OwnedPlatformFnDescriptor` `non_exhaustive` (FIXME 0107); IO_TAG_* constants on platform's public API (R9 truth-telling correction landed `25fa73a`) | ✓ platform.md row covers all; R9 already landed |
| int | SharedState (D38); per-symbol mutability after Phase 0; receive-side of D40, D41, D42; FIXME 0103 trace/io_trace arrival; FIXME 0099 GotObserver consumer; FIXME 0108 display arrival | ✓ int.md row covers all |

**Verdict — per-crate masters:** every facade-load-bearing claim in the six per-crate master docs is reflected in SPRINT.md scope. **No gaps.**

### 1.5 `memory/` and active FIXMEs

**Memory-flagged**: `memory/project_fqtypename_priority.md` flags FQTypeName migration as next-up. SPRINT.md scope row for `types.md` says: *"FQTypeName threaded through every API that today takes bare `TypeName` — aspirational becomes binding."* Plus FIXME 0151 to be filed this sprint tracking implementation. **Captured.**

**Active FIXMEs** crossed against SPRINT.md scope (in-scope set): 0098, 0099, 0100, 0103, 0104, 0107, 0108, 0150 — every one explicitly cited in SPRINT.md scope (either as facade-shape reflection or as adoption deferral to S66). 0151 to be filed this sprint per scope. **No gap.**

Other open FIXMEs scanned for facade-load-bearing relevance:

- **Pre-S65 sprint scope** (0034, 0050, 0096, 0102, 0106) — facade-irrelevant (subsystem cleanup, doc archival, CLAUDE.md authoring). Defer.
- **Defect/repro FIXMEs** (0017–0021, 0026–0029, 0035–0042, 0044–0047, 0049–0095) — all carry-forward defect/triage items; not facade-shape.
- **Spec FIXMEs** (0005–0007, 0049, 0054, 0113, 0114, 0141) — spec-side, no facade impact.
- **Harvest FIXMEs** (0116–0149) — test reconstitution; tracked per S67+ vertical sprints.
- **Per-crate cleanup** (0033, 0109, 0142, 0140, 0121, 0122) — internal refactor; not facade-shape.

**No load-bearing FIXME falls outside SPRINT.md's in-scope/deferred treatment.**

### 1.6 Scope completeness verdict

**HIGH confidence — scope is complete.** Every active Decision, every load-bearing substance-scoping item, every Step-4 row, every facade-load-bearing per-crate claim, and every memory-flagged commitment is reflected in SPRINT.md scope. The only friction noted is **scope-row framing**: SPRINT.md presents §1.2/§2.1/§2.6/§2.7 as "additions" when they are already in the current facades from S64 substance commits. Under the reshape, the actual S65 work for those rows is verify-and-tighten against the now-final D43 shape, not author-from-scratch. This is **a minor wording revision suggestion**, not a scope gap. SPRINT.md could read: *"facades/backend.md — verify §1.2 D41, §2.6 LinkerSymbol, §2.7 typed error variants are tight against the post-D43 dependency declarations; tighten if not."* Recommend `/sprint` reflect this in Phase 3.

**Total gap count: 0 substantive gaps; 1 wording-clarity revision suggestion.** Below the >5 threshold for Phase 1 reconsideration.

---

## 2. Authoring dependency graph

The provisional wave structure in SPRINT.md (W1 D43 split + bounded-contexts; W2 types; W3 consumer facades; W4 per-crate slices + cross-cutting; W5 close gate) is sound. Confirming + refining below.

### 2.1 Wave dependency table

| Wave | Facade(s) authored / revised | Depends on | Why this order |
|---|---|---|---|
| **W1** | `facades/primitives.md` (new); `facades/intrinsics.md` (new); `facades/runtime.md` archived; `bounded-contexts.md` §4 → §4a + §4b | nothing | D43's split is foundational. After W1, the conceptual two-category model is explicit; W3's backend.md and int.md depends-on declarations point to primitives + intrinsics rather than runtime. Doing this first means W3 doesn't author against a stale dependency declaration that has to be rewritten. |
| **W2** | `facades/types.md` revised (FQTypeName threading + D42 confirmation) | W1 (because intrinsics.md may name types crossing the FFI; types.md revisions land *after* the new facades exist so cross-references are real) | types.md is the foundation that flows into every consumer. FQTypeName is the cross-cutting binding commitment — once threaded through types.md, every consumer facade in W3 inherits the threaded types and updates its consumed-surface declarations to match. |
| **W3** | `facades/frontend.md`, `facades/typecheck.md`, `facades/backend.md`, `facades/platform.md`, `facades/int.md` revised | W1 (depends-on declarations); W2 (FQTypeName + final type set) | Five consumer facades. They share W1+W2 as their input contract. Within W3 the facades are largely independent — frontend/typecheck/platform are dependency-light against each other; backend.md and int.md are tightly coupled around D41 (mutref pattern crosses both) so should be authored as one logical unit even though they're separate files. Suggest: backend.md + int.md as a paired sub-batch within W3; frontend.md + typecheck.md + platform.md in parallel sub-batches. Within `/arch`'s context budget, may collapse to serial. |
| **W4** | Per-crate implementation slices (`design/{crate}/implementation-slice-s66.md` × 8 — frontend, typecheck, backend, runtime-retiring, primitives, intrinsics, platform, int) + `/qa` test-plan slice | W1, W2, W3 (all facades final) | Each `/design (crate)` reads the now-final facade for its crate and scopes the S66 implementation work. Nothing to author in slices until facades are final. **Cross-cutting checks** also in W4 by `/arch`: every active Decision reflected; Principles 14/15 honoured; FIXME 0151 filed; FIXME inventory consistent. |
| **W5** | Close gate — no facade authoring | W4 | `/qa` reads final facades as documentation, confirms testability, authors S66 test plan. User reviews. Sprint archives. |

### 2.2 Refinements to the SPRINT.md provisional waves

The SPRINT.md provisional wave shape is correct. Two refinements:

1. **W3 sub-batching.** The five consumer facades in W3 are not equally coupled. Backend.md and int.md share Decision 41's mutref pattern across the boundary — the wording on each side must match exactly. Author them as a *sub-batch* (sequentially in one sitting, or with a paired review step). Frontend.md, typecheck.md, platform.md are decoupled and parallel-friendly. SPRINT.md says "Parallel-friendly within `/arch` if context allows; serial otherwise"; recommend clarifying that the b/i sub-batch is non-parallel internally even if the W3 batch is parallel overall.

2. **W4 cross-cutting check is a discrete deliverable.** SPRINT.md folds it into the W4 author wave but it deserves naming as a separate `/arch` step: at end of W4, `/arch` runs a single pass that reads every facade, every Decision, every Principle, and verifies cross-consistency. This pass produces a one-page checklist artefact — the explicit Phase-2-of-Phase-2 closure. Suggest reflecting in Phase 3 wave plan.

### 2.3 Wave structure verdict

**Confirm provisional wave structure.** No restructure needed. The two refinements above are tightening, not restructure.

---

## 3. Per-crate implementation-slice template

Each `/design (crate)` authors a Sprint-66 implementation slice in W4. Template specification:

### 3.1 File path convention

`design/{crate}/implementation-slice-s66.md` for the six existing crates (frontend, typecheck, backend, runtime, platform, int). For Decision-43-new crates: `design/primitives/implementation-slice-s66.md` and `design/intrinsics/implementation-slice-s66.md` (these directories don't exist yet — the slice authoring is the first thing in those directories; W1 may stub them or W4 creates them when needed). For runtime-*retiring*: `design/runtime/implementation-slice-s66-retiring.md` — distinct filename to mark the migration-out shape vs an ordinary forward-slice.

For `/qa`: `design/qa/test-plan-slice-s66.md` (or `tests/plan/s66.md` — `/qa` chooses; `/arch` accepts either as long as it's findable from `sprints/SPRINT.md` cross-reference at S66 plan time).

### 3.2 Required sections

```markdown
# Sprint 66 implementation slice — {crate}

**Status.** [draft | reviewed-by-/arch | approved-for-S66]
**Author.** /design ({crate}), {date}
**Reads.** facades/{crate}.md (final, S65 close); design/arch/decisions/* (cited Decisions); /qa S66 test plan slice (when available)

## 1. Scope from facade

Read the final `facades/{crate}.md` and enumerate the concrete delta between facade and current source. One row per delta — what changes, where in source, what FIXME closes, what acceptance criterion holds.

| Delta | Source location(s) | FIXME closed | Acceptance |
|---|---|---|---|
| ... | ... | ... | ... |

## 2. Ordering within the slice

If the deltas have internal dependencies (one must land before another), capture the ordering. If the slice is one logical unit, say so.

## 3. Estimated effort

Rough sizing: hours, days, or "single triad cycle". Specifies what /sprint can fit into a wave envelope.

## 4. Dependencies on other crates' slices

Cross-reference each other crate's slice that this slice depends on. Surfaces the cross-skill dependencies that S66's wave plan must respect.

| This slice's item | Depends on | In the other crate's slice |
|---|---|---|
| ... | ... | ... |

## 5. Test surface impact

What new test does the implementation enable? What existing test changes shape? Pairs with /qa's S66 test plan slice — if the /qa slice doesn't yet enumerate the test, this slice files a FIXME against /qa.

## 6. Open questions

If authoring the slice surfaces architectural questions the facade doesn't pin, file FIXMEs against /arch. Slice does not invent answers; surfaces the question.
```

### 3.3 Acceptance criteria for slice review

`/arch` reviews each slice against:

1. **Scope coverage.** The slice's delta table captures every difference between the final facade and current source. `/arch` cross-checks against the facade's content.
2. **Dependency completeness.** The slice's "Dependencies on other crates' slices" table is complete — for each cross-crate touch, the corresponding entry exists in the other crate's slice. (Cross-check is bilateral.)
3. **Sizing realism.** The estimated effort is consistent with the change list. Egregious mismatch (e.g., "single triad cycle" for a 10-row delta) flags a sub-divide.
4. **Open questions surfaced, not invented.** Where the facade is ambiguous, the slice files a FIXME, not a unilateral resolution.

### 3.4 How slices feed into S66 wave plan

`/sprint` reads all eight + `/qa` slices and:

1. Collates the dependency graph across slices (cross-check the bilateral tables);
2. Identifies parallel-safe vs. serial-required sequencing;
3. Sizes waves against /sprint's effort budget;
4. Produces S66 SPRINT.md with each wave naming the slice(s) that drive its work.

The contract: **slices are inputs to /sprint's wave plan; the wave plan is /sprint's output, not the slice authors'.** Slices do not pre-allocate waves; they hand /sprint the data needed to allocate.

### 3.5 Template verdict

The template above is what `/arch` requires from each `/design (crate)` in W4. SPRINT.md Phase 3 should reflect this template directly (or by reference) so /design authors invoke against a known shape.

---

## 4. Endgame check — is the facade truly final after S65?

The most important question. Walking through the second-order effects.

### 4.1 FQTypeName threading second-order effects

FQTypeName threading affects every consumer facade. The current types.md has FQTypeName committed in `Type::ADT(FQTypeName, ...)`, `TypeDefInfo.name`, `MethodResolutions.impl_type`, `ResolutionGap::Type(FQTypeName)`. SPRINT.md says *"FQTypeName threaded through every API that today takes bare `TypeName`"*.

**Inspection of the consumer facades:**

- **frontend.md**: imports `TypeName` (syntactic) AND `FQTypeName` (consumed surface line 153). No frontend API takes bare `TypeName` after threading — frontend produces `TypeExpr::Named(TypeName)` and the lift to FQTypeName happens at typecheck. **No threading change needed in frontend.md.**
- **typecheck.md**: imports both. `check_form` takes the symbol-tables map; FQTypeName resolution happens inside. `ResolutionGap::Type(FQTypeName)` already takes FQ. **Already aligned.**
- **backend.md**: backend consumes `TypeDefInfo` etc. — already FQTypeName-threaded via types.md. No bare `TypeName` in backend public API. **Already aligned.**
- **platform.md**: uses `TypeName` only inside `parse_type_sig(sig: &str) -> Result<Vec<Type>, _>` — and `Type` carries `FQTypeName` via `ADT`. The platform-fn type signature parser produces `Type` with FQTypeName already. **Already aligned.**
- **int.md**: consumes the full set; FQTypeName flows through `wait_for_typecheck_type(fqt: &FQTypeName)`. **Already aligned.**

**Finding.** FQTypeName threading is **already largely landed in the facades**. The "aspirational becomes binding" framing in SPRINT.md scope is correct — what changes in S65 is the *commitment level*, not the wording: types.md says aspirational at line 106–111, and the consumer facades already cite FQTypeName as if it were binding. S65's work is to remove the aspirational hedge in types.md and confirm the consumer facades are truly bindingly aligned (not silently divergent in some sub-corner I haven't surfaced).

**Risk.** Where facades currently silently use `TypeName` instead of `FQTypeName` in places that *should* be FQ — e.g., somewhere a `MethodResolutions` field accepts a `TypeName` rather than `FQTypeName`. This requires a systematic walk-through. **Recommend W2 explicitly: read every facade line by line and grep for `TypeName` (uppercase, not in newtype-table contexts); each occurrence is either (a) syntactic-stage and correct, or (b) resolved-stage and should be `FQTypeName`. Document each (a) classification; convert each (b) to FQTypeName.**

This is conservative but tractable. The grep pass plus per-occurrence classification fits within W2's `/arch` budget.

**Threading does NOT reveal additional moves we haven't catalogued.** No surprise.

### 4.2 D43 split second-order effects

The split touches:

- types.md `marshaling tags` and `SchedulingClass` are consumed by both primitives (no — primitives are language-callable, no marshaling needed) and intrinsics (yes — IO trampoline marshaling). Stays in types.md per Principle 3 (boundary types). **No move.**
- platform.md depends on runtime currently for `HostContext::dispatch` path — but post-D43 the IO trampoline lives in intrinsics. `bounded-contexts.md` §5 platform's "What crosses the boundary" line says *"Inward: a small set of layout types from cranelisp-types"* and *"the host callbacks reach runtime via fn pointers installed at session init"*. **Post-D43, the wording becomes "...reach intrinsics via fn pointers installed at session init"** — a small wording revision. **Recommend reflecting in W1 bounded-contexts revision.**
- backend.md current `Consumed surface` (lines 232–246) lists `cranelisp-runtime::*` extern functions backend names by string at codegen time. Post-D43:
  - User-callable conversions (`int_to_string`, `parse_int`, etc.) → primitives crate. Backend's name-keyed substitution table sees them as `add-i64`/`int-to-string` symbol names (no path).
  - All emitted-call targets (`heap_alloc`, `rc_underflow_check`, `runtime_panic`, `cranelisp_run_io`, `vec_*`, `ivar_*`, `dec_shallow_io`, etc.) → intrinsics crate.
  - The `Consumed surface` re-categorises into two lists. **Captures naturally in W3 backend.md revision.**
- int.md current `Consumed surface` line 736 says *"`cranelisp-runtime` — runtime extern functions registered with the JIT..."*. Post-D43 splits into `cranelisp-primitives` (for symbol-table seeding of `primitives/<name>` GOT slots) and `cranelisp-intrinsics` (for backend-emitted-call resolution). **Captures in W3 int.md revision.**

**No additional moves surfaced.** D43 is well-scoped in `legacy/substance-scoping.md` §1.7 and FIXME 0150's Phase plan; the facade authoring follows the same categorisation.

### 4.3 Decision 41 implementation surface questions

Decision 41 is pre-implementation. Could implementation surface design questions that force facade revision in S66+?

**Surface inspection.** D41 commits to:
1. Per-symbol JIT cardinality (one `JITModule` per `compile_to_module` call in JIT mode; per-module in object mode);
2. `Code` enum moves to `cranelisp-backend`;
3. Backend writes `Code::Jit` and `Introspection` directly via `&self` interior-mutable `write_code(&self, sym, code)`.

Implementation risks:

- **Per-symbol JIT cost.** ~50 intrinsic registrations per `JITModule::new`. If REPL session has thousands of redefinitions, the cost could be material. Mitigation: cache the registration set (the intrinsics list is static). This is *implementation* work, not facade revision.
- **`Code` move risks.** `Code` moves backend-side; typecheck/frontend stay generic. The risk is that `Code` referencing `Arc<Jit>` and `Arc<Linker>` requires backend-private types to be exposed via `pub` — all already done in current backend.md. No risk.
- **Mutref pattern risk.** `compile_to_module` takes `&DashMap<ModuleFullPath, SymbolTable<Code, ()>>` and a `Option<&DashMap<FQSymbol, Introspection>>`. Five parameters. If implementation discovers it needs additional shared-state references (e.g., a callees observer for cross-crate call-graph extraction), the parameter list grows. Mitigation: bundle into a `CompileContext { ... }` struct if/when it becomes necessary. **Facade-revisable, but only if/when implementation actually needs it.** Forward risk: low (the ~5 parameters are stable conceptually; bundling is a future cosmetic).

**No facade revision foreseen for D41 in S66.** Implementation may surface FIXMEs against `/arch` for narrow tightening, but no facade rewrite.

### 4.4 Adoption-time facade churn risk

The reshape's whole rationale is "S66 adoption against a stable target with no throwaway." After S65, will S66 actually need zero facade changes?

**Risks identified:**

1. **Tightening-language ambiguities.** A facade may be technically correct but lose its semantic edge during S66 implementation, requiring a wording sharpening. Example: backend.md says `compile_to_module` writes `Introspection` "iff `introspection.is_some()`". S66 implementation might surface "yes, but also iff the symbol's entry has `kind == DefKind::UserFn`, not for primitives". This kind of edge case requires facade wording revision but not interface revision. **Likely; small.**
2. **Cross-skill type-name drifts.** Not all type names are settled. E.g., is it `IoEvent` or `IoTraceEvent`? `GotEvent` or `GotPopulationEvent`? Where the facades say one thing and implementation prefers another, S66 may file `target: /arch` FIXMEs for cosmetic renames. **Likely 1–3 such fix-ups.**
3. **Genuine design holes.** Could S66 implementation surface a load-bearing question the facade does not pin — e.g., "what's the contract when two workers concurrently call `compile_to_module` on the same symbol from different threads?" If the facade doesn't pin atomicity at that boundary, S66 implementation hits the question late and files an `/arch` FIXME. **Possible. Forward-risk mitigation: W4's cross-cutting check explicitly surfaces concurrency / atomicity / orderings questions at every public-API boundary.**

**Endgame confidence: MEDIUM-HIGH.** The structural commitments are sound. Wording-level revisions in S66 should be expected and tolerable (1–3 small `/arch` FIXMEs with quick turn-around). A genuinely load-bearing facade hole is unlikely (the facades have been hardened over S63 + S64 substance commits) but not impossible.

**Recommendation:** Accept that S66 may need 1–3 narrow facade adjustments and document the tolerance in SPRINT.md "Hard constraints" #1 — *"Once a facade lands here, it is binding for S66+ adoption. Items deferred from the facade are explicit deferrals with rationale, not omissions. Narrow editorial revisions surfaced by S66 implementation that don't change interface shape are accepted via target: /arch FIXMEs and a same-sprint /arch revision; structural revisions require returning to the facade-completion phase."*

This calibration is honest and operationally useful.

---

## Verdict

- [ ] APPROVE — Phase 3 may proceed
- [x] APPROVE WITH REVISIONS — Phase 3 may proceed after the listed revisions are reflected in `sprints/SPRINT.md`
- [ ] PAUSE — sprint scope is wrong; return to Phase 1 reconsideration

Required revisions (small; reflect in `sprints/SPRINT.md` Phase 3 advance):

1. **Scope-row framing tightening.** SPRINT.md scope rows for `frontend.md` (§2.1), `backend.md` (§1.2/§2.6/§2.7), `platform.md` (§2.13), `runtime.md` (§2.11) currently read as new authoring; they are *verify-and-tighten against the post-D43 final shape*. Reword to *"verify §X against the post-D43 final shape; tighten if needed"*. Avoids implying duplicate authoring vs S64 commits.

2. **W3 sub-batching note.** Reflect the §2.2 finding: backend.md + int.md are a sequential sub-batch within W3 (D41 mutref wording must match exactly across both); frontend.md + typecheck.md + platform.md are parallel-friendly within `/arch`'s context budget. Update SPRINT.md "Waves (Phase 4)" provisional shape to clarify.

3. **W4 cross-cutting check named as discrete `/arch` step.** Reflect §2.2 finding: the cross-cutting check (every active Decision reflected; Principles 14/15 honoured; FIXME inventory consistent; FIXME 0151 filed) is a separately-named W4 deliverable, not folded into per-crate slice authoring. Update SPRINT.md "Waves (Phase 4)" Wave 4 line.

4. **FQTypeName grep pass explicit in W2.** Reflect §4.1 finding: types.md revision in W2 includes a deliberate grep-and-classify pass over every facade for `TypeName` occurrences. Reword the SPRINT.md `types.md` scope row: *"FQTypeName threaded through every API that today takes bare `TypeName` — aspirational becomes binding. W2 includes a deliberate grep-and-classify pass over every facade: each `TypeName` occurrence classified as syntactic-stage (correct) or resolved-stage (convert to `FQTypeName`)."*

5. **Endgame tolerance commitment.** Reflect §4.4 finding: SPRINT.md "Hard constraints" #1 acknowledges narrow editorial revisions in S66 are tolerated (with rationale + same-sprint `/arch` turnaround). Sharpens what "facade IS the target" means in practice.

6. **Per-crate slice template referenced explicitly.** Reflect §3 finding: SPRINT.md "Skill plans (Phase 3)" `/design (per crate touched)` line references `design/arch/sprint-65-reshape-phase-2-review.md §3` for the slice template. Avoids each `/design (crate)` re-deriving structure independently.

None of these revisions changes the sprint shape or scope. They are tightening + cross-reference + commitment-clarification.

---

## Cross-references

- `sprints/SPRINT.md` — current sprint plan (this review's subject)
- `design/arch/sprint-65-phase-2-review.md` — original Phase 2 review (predates the reshape; historical record)
- `design/arch/sprint-65-legacy-triage.md` — in-session legacy triage that surfaced the gaps motivating the reshape
- `design/arch/legacy/substance-scoping.md` — substance findings + resolutions (the source of §1 + §2 items)
- `design/arch/legacy/substance-action-plan.md` — Step-4 retro source
- `design/arch/CLAUDE.md` — Decisions register + canonical document table
- `design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md` — D40
- `design/arch/decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md` — D41
- `design/arch/decisions/0042-platform-error-adopts-error-location.md` — D42
- `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md` — D43
- `design/arch/fixmes/0098-*` through `0108-*`, `0150-*` — in-scope FIXMEs whose facade-shape this sprint reflects
- `memory/project_fqtypename_priority.md` — FQTypeName memory flag (informs §4.1)
