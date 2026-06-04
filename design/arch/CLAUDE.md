# design/arch/

Architecture deliverables for the Cranelisp reimplementation. Owned by `/arch`.

Per `sprints/METHOD_PROPOSED.md` §14.1, this `CLAUDE.md` carries domain-local content only — local conventions, the in-progress Decisions-drain backlog, and pointers to canonical documents. Methodology rules live in `METHOD_PROPOSED.md`; architectural principles live in `principles.md`; skill workflows live in `.claude/commands/arch.md`. **Architectural commitments manifest at their natural home in the permanent set** (facades / BC / principles / sequences); no separate Decision log is authored — see `.claude/commands/arch.md` §"The manifestation-site question".

## Canonical documents (the target documentation set)

| File | Purpose |
|---|---|
| `overview.md` | Bridge document — the newcomer entry point. How the language is realized through the surfaces, tested by `/qa`'s integration suite, embodied in the crates. |
| `principles.md` | Architectural principles — index. Each Principle is one file at `principles/NN-{slug}.md`. Auto-imported by `.claude/commands/arch.md`. |
| `principles/` | Architectural Principles register; one file per Principle; index in `principles.md`. |
| `bounded-contexts.md` | Per-surface bounded-context full statements (Frontend, Typecheck, Backend, Runtime, Platform, Binary/int, plus types crate). |
| `facades/{crate}.md` | Per-surface facade specs — as-designed public surface. One file per surface. **Eight retired**: `facades/types.md` (S69 Sub 42); `facades/frontend.md` (S70 Phase B group B3-C); `facades/platform.md` (S71 Wave 4); `facades/typecheck.md` (S72 Wave 5); `facades/intrinsics.md` (S74 Wave 3 → BC §4b + source rustdoc); `facades/primitives.md` (S74 Wave 3 → BC §4a + source rustdoc); `facades/backend.md` (S75 Wave 5b → BC §3 + source rustdoc); `facades/backend-cache.md` (S75 Wave 5b → **cache submodule source rustdoc only**, an implementation detail of backend — NOT promoted to a BC entry; no §3a). For the seven crate-shaped retirees, source rustdoc (crate-root `//!` + per-item `///`) is the canonical surface and cross-surface narrative lives in `bounded-contexts.md` (§7 for types, §1 for frontend, §5 for platform, §2 for typecheck, §4b for intrinsics, §4a for primitives, §3 for backend); for `backend-cache` — backend's persistence half — the canonical home is the cache submodule rustdoc (`crates/cranelisp-backend/src/cache/mod.rs` `//!` + per-submodule `//!` + per-item `///`), with **no** bounded-contexts entry, because the cache is an implementation detail of the backend bounded context, not a context of its own. The only remaining live facade is `facades/int.md` (int — the last crate). |
| `interfaces.md` | Narrative companion to `crates/cranelisp-types/`. |
| `tracing.md` | Subsystem design for the `(trace ...)` execution-trace feature — **TARGET STATE (user-decided 2026-06-04)**: tracing encapsulated in the trace keyword-node + `cranelisp-intrinsics` (the 12 bodies + table + nested-trace runtime guard) + backend (codegen + display-descriptor baking + discovery-in-codegen, swap-all-symbol-tables), with **no int runtime involvement**. `trace_format` is a pure intrinsic over codegen-baked self-contained `DisplayDescriptor`s (survives `.o` caching). Works in ALL modes incl. `--link`. D40's trace-half (REPL/`--run`-only + relocate-to-int) RETRACTED; io_trace half stands. §7 is now a compact History appendix (the proposal was enacted). Cited by BC §3 (backend emits/bakes/discovers) + §4b invariant 12 (intrinsics hosts) + §6 (int deletes). |
| `fixmes/` | FIXMEs register; one file per FIXME (`design/arch/fixmes/NNNN-name.md`). |
| `sequences/` | Current target sequence diagrams (`.mmd` + rendered `.svg`). |

## Sorting buckets

| Directory | Purpose |
|---|---|
| `decisions/` | **Draining.** Existing Decision files migrate into the facade / BC / principle section where they manifest, then delete. No new Decisions authored — see `.claude/commands/arch.md` §"No separate Decision log". When the directory is empty it is removed. |
| `legacy/decisions/` | **Draining.** Same as above for outcome-fully-embodied Decisions kept for narrative continuity. Same disposition: migrate substance into the manifestation site (if not already there), delete the file. |
| `legacy/` | Documents not part of the approved configuration but kept for reference. `/arch` and the per-crate `/design` skills pull back content (or re-author from it) when needed; otherwise files here are triaged into top-level (if they prove still load-bearing) or down to `archive/` (if confirmed superseded). Not a permanent home. |
| `archive/` | Frozen historical content — superseded by canonical work, kept for context only. See "## Archive" below. |

## Archive (`archive/`)

Historical pipeline designs (v1, v2, v3) and superseded migration artefacts. Reference only — not the target architecture.

- `archive/v1/` — v1 architecture, interfaces, pipeline orchestration, sketch audit
- `archive/pipeline-v2.md` — v2 pipeline design (stages, unified multi-pass check)
- `archive/pipeline-v3.md`, `archive/pipeline-v3-roadmap.md` — v3 migration (complete)
- `archive/pipeline-convergence-review.md` — Sprint 26 dual-pipeline defect analysis (origin of principles 11–13)
- `archive/pipeline-convergence-playbook.md` — convergence execution plan
- `archive/session-restructure.md` — session restructure target data model (phases A–F complete)
- `archive/per-module-got-cleanup.md` — GOT unification design
- `archive/sprint-40a-design.md` — cancelled Sprint 40a design
- `archive/codegen-convergence.md` — Sprint 54 Wave 3a; superseded by Decisions 22, 23, 25 (S63 archive)
- `archive/ast-annotation-examples.md` — Sprint 55 Step 1b annotation spec (S63 archive)
- `archive/pipeline-v4.md`, `archive/pipeline-v4-roadmap.md`, `archive/concurrent-pipeline.md` — v4 scheduler-driven pipeline design + roadmap; superseded by per-crate `design/{crate}/{crate}.md` and Decisions 21–27, 31, 36–41 (S65 Phase 2 legacy triage)
- `archive/reconciliation-plan.md` — Sprint 63 close procedural reconciliation plan; substance + procedural waves executed (S65 Phase 2 legacy triage)
- `archive/roadmap.md` — pre-S63 ring-by-ring architectural roadmap; delivery tracked by `sprints/ROADMAP.md`; per-crate intent in `design/{crate}/{crate}.md` (S65 Phase 2 legacy triage)
- `archive/substance-scoping-brief.md` — input brief for the substance-scoping pass; pass executed and resolved into Decisions 40–43 (S65 Phase 2 legacy triage)
- `archive/macro-resolver.md` — Sprint 50 macro resolver design; superseded by FIXME 0098 (Decision 8 retracted; `MacroResolver` trait drops in favour of direct `&SymbolTables<C, L>` lookup) (S65 Phase 2 legacy triage)
- `archive/traitimpl-symbol-table.md` — Sprint 51 ImplRegistry-deletion design; landed in source (`ModuleEntry::TraitImpl` exists; `ImplRegistry` deleted per `crates/cranelisp-typecheck/src/{checker,traits}.rs` source comments) (S65 Phase 2 legacy triage)
- `archive/sequence-diagram/` — pre-S63 v4-target sequence diagrams; superseded by `sequences/` (S65 Phase 2 legacy triage)
- `archive/facades-runtime.md` — pre-D43 runtime facade; content migrated to the primitives + intrinsics surfaces (S65 W1 — Decision 43 crate split). Both successor facades subsequently retired (S74 Wave 3); their canonical homes are now `bounded-contexts.md` §4a (primitives) / §4b (intrinsics) + the crate-root source rustdoc.

## Decisions drain backlog

**This register is being drained.** Per `.claude/commands/arch.md` §"The manifestation-site question", each Decision's substance migrates into the facade / BC / principles section where a reader expects to find it. The Decision file deletes once migrated. New architectural commitments are NOT filed here; they go directly to their manifestation site.

**Per-Decision target identification format:** As each Decision is queued for drain, mark it `[→ {manifestation-site}]` inline. Then in a follow-up fire: migrate substance, sweep cross-references, delete the file, strike the line here. When the section hits zero lines it is removed.

Current backlog:

- [0010](decisions/0010-base-pointer-abi.md) — Base-pointer ABI (environmental — captures rejected interior-pointer alternative)
- [0011](decisions/0011-embedded-drop-glue-ptr-in-closures.md) — Embedded drop_glue_ptr in closures (environmental — captures rejected side-table alternative + cross-module closure constraint)
- [0027](decisions/0027-g8-lands-before-g9.md) — G8 lands before G9 (environmental — borrow-checker sequencing rationale)
- [0030](decisions/0030-form-by-form-scheduler-mutual-imports.md) — Form-by-form scheduler deadlocks on mutual imports (environmental — coordination constraint future readers will hit)
- [0035](decisions/0035-code-enum-integration-layer.md) — `Code` enum location (operative; amended Sprint 64 per Decision 41 — Code now in `cranelisp-backend`; amended Sprint 66 — variants slim to lifecycle owner only `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)`. The S66 unification (`b09ec76`) briefly relocated the per-entry `ptr` to a sibling `ModuleEntry::Def.fn_ptr` field; the same-day rollback `1dc57ae` removed that field as redundant with the per-module `GotTable`. **Post-rollback canonical statement: GOT is the single source of truth for callable addresses; `ptr` lives in `SymbolTable.got()` indexed by `ModuleEntry::Def.got_slot`. No per-entry pointer field.**)
- [0040](decisions/0040-runtime-trace-io-trace-relocate-to-int.md) `[trace half RETRACTED 2026-06-04 → tracing.md §§1–6 + BC §3/§4b-inv-12/§6; io_trace half STANDS → BC §4b + §6]` — **(trace ...) half retracted by the 2026-06-04 user ruling**: the 12 trace bodies relocate BACK to `cranelisp-intrinsics` (publish via `intrinsics_table()`), trace works in ALL modes incl. `--link`, discovery + descriptor baking move to backend codegen, nested trace is a runtime error. The `io_trace`/`IoObserver` half STANDS (ring buffer → int; ~50-line registration API → intrinsics). See the PARTIAL-RETRACTION BOX atop the D40 file + `tracing.md` §7. `IoObserver` callback registration API resides in `cranelisp-intrinsics` post-Decision-43 (originally specified to remain in runtime; the registration-site host moved with the D43 split — see `bounded-contexts.md` §4b + the `cranelisp-intrinsics` crate-root `//!` rustdoc §"Int-owned intrinsics" / `io_observer` module rustdoc; `facades/intrinsics.md` retired S74 Wave 3). BC §4b carries the contract. Amended 2026-05-16 (S67 W4) to Path B1 (full deletion; user-arbitrated) — supersedes the earlier B2-flavoured §"Shape" reading. Pre-implementation; tracked by FIXME 0103 + cascading FIXMEs 0197–0202.
- [0041](decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md) `[→ bounded-contexts.md §3 invariant 3 + crates/cranelisp-backend/src/{lib,code}.rs rustdoc]` — `compile_to_module` per-symbol JIT cardinality; `Code` moves to `cranelisp-backend` (backend *names* it); backend writes the **GOT slot** directly (#2), the **caller composes `Code`** (#1 — both `Code::Jit` and `Code::Linker`; S75 W2 Finding-A correction — backend only borrows `&mut M`, never owns the `Arc<Jit>`, so cannot construct `Code::Jit`; symmetric with the existing Linker path); returns `CompilationArtifacts`; `produce_disasm(fq, code_size, symbol_tables)` is a separate on-demand fn with a **caller-supplied `code_size`** + capstone raw-bytes disasm (S75 W2 Finding-C correction). Amends 31, 35. **Corrected substance now lives in `bounded-contexts.md` §3 + the backend source rustdoc** (`facades/backend.md` retired S75 W5b → BC §3 + `lib.rs`/`code.rs` rustdoc; per "No separate Decision log"); D41 file annotated with an S75 correction box for drain-consistency.
- [0042](decisions/0042-platform-error-adopts-error-location.md) — `PlatformError` is a `cranelisp-types`-hosted enum with `ErrorLocation` carriers per variant; surfaces via `CranelispError::Platform` (pre-implementation)
- [0043](decisions/0043-runtime-split-into-primitives-intrinsics.md) — `cranelisp-runtime` splits into `cranelisp-primitives` + `cranelisp-intrinsics`; backend has no trait knowledge (retracts 14, reframes 15; pre-implementation; tracked by FIXME 0150)
- [0044](decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md) — Cluster-atomic typecheck via orchestrator-owned staging; `View<'_, C, L>` newtype; reframes 0038's per-form check_form shape (pre-implementation; filed by FIXME 0166; **amended Sprint 66 Phase 3 by FIXME 0167** — Approach B + `SymbolTableAccess` introduction (originally named `ClusterContext`; renamed in the post-S72 facade-coherence pass — "Cluster" privileged one of two modes, "Context" was contentless); pass signatures take `&mut SymbolTableAccess` and return `Result<(), CheckError>`; staging mutation flows through the existing `current_symbol_table_mut` accessor so the 91 register-call sites in typecheck do not change individually; invariant 2 revised — passes are pure with respect to live state, may mutate orchestrator-handed staging via the same accessor used in committed-mode; **further amended Sprint 66 Phase 3 by FIXME 0168** — Sequencing splits Wave 3a into α — locality-correctness refactor — before β — triad re-fire — per Decision 0046; **further amended 2026-05-13 third amendment** — the two-pass facade split (`check_form_signatures` + `check_form_body`) collapses into a single `check_forms(parsed: Vec<ParsedEntry>, ctx: &mut SymbolTableAccess, symbol_tables: &SymbolTables) -> Result<(), CheckError>` free function; internal two-pass discipline + Pass-1-to-Pass-2 working state are internal to the call frame; `ModuleCheckAccumulator` retired from both typecheck and `int` public surfaces — cross-symbol bookkeeping migrates onto `ProcessedCluster` fields; state-threading hole closed by construction)
- [0045](decisions/0045-traitimpl-storage-in-trait-defining-module.md) — `ModuleEntry::TraitImpl` is written to the **trait's defining module**; importers discover impls by chain-following the trait reference (per-symbol `Import`/`Reexport`) back to its home module and probing for `impl$FQTypeName$FQTraitName`; pattern (b) selected over (a)/(c)/(d) on chain-follow simplicity (no closure walk; no cycle detection) + Principle 7 + Principle 17 grounds; user-arbitrated 2026-05-10 (Sprint 66 Wave 3a-α post-mortem); α's first pass `ab068e2` embodied pattern (a) and is rolled back + redone (filed by FIXME 0168; pre-implementation)
- [0046](decisions/0046-wave3a-locality-refactor-precedes-triad.md) — Wave 3a splits into α — locality-correctness refactor across `crates/cranelisp-typecheck/src/{checker,infer,traits,builtins}.rs` per Principle 17 — before β — cluster-atomic triad implementation per Decision 44 (amends 0044; pre-implementation; ~3–5d α + ~3–4d β; filed by FIXME 0168)
- [0047](decisions/0047-fqtypename-binding-at-resolved-stage-boundaries.md) — FQTypeName is binding as the cross-crate boundary type for resolved-stage type identifiers; two exceptions named (reverse-lookup; receiver-pinned). Closes FIXME 0151 at S67 W5 acceptance. Filed Sprint 67 (Phase 3 W0 — second user-challenge scope amendment).
- [0048](decisions/0048-primitives-static-symboltable-and-got-in-crate.md) — `cranelisp-primitives` owns a statically-constructed `SymbolTable` + `Arc<GotTable>` referenced from CompilerSession at startup; from session-init onward primitives dispatch is functionally equivalent to any other module (pre-implementation, S68; **A2 reversed 2026-05-31 (S73 Phase 2, FIXME 0244)** — `Code::Primitive` marker dropped; primitives entries carry `code: None` (the `ModuleEntry::def(..).build()` default), primitive-ness read from `kind: DefKind::Primitive`; **dep-ban → bidirectional severance 2026-05-31 (S73 Phase 2 top-up)** — `cranelisp-primitives ⟂ cranelisp-backend`: with `code: None` everywhere primitives never names `Code`, builds `SymbolTable<(), ()>`, drops `cranelisp-backend` from its manifest; `int` concretizes to `<Code, ()>` via `into_concrete` at the session mount; primitives-side lands S73, backend-side cleanup deferred to a future backend sprint; motivates Principle 18).

Legacy Decisions (outcome fully embodied in architecture; preserved in `legacy/decisions/` for narrative continuity) — `0001`–`0006`, `0008`–`0009`, `0012`–`0013`, `0016`, `0018`–`0019`, `0021`–`0026`, `0029`, `0032`–`0034`, `0036`–`0038`. Retracted/superseded Decisions deleted (rely on git for history): `0007`, `0014` (retracted by 43; commit `754d525`), `0015` (reframed by 43; commit `754d525`), `0017`, `0020`, `0028`, `0031` (substance fully amended into 0041 at Sprint 64; Cranelift `Memory::drop` evidence + safety invariant + callback support forward commitment relocated to 0041 at S69 Phase 3 — per-symbol JIT cardinality is the operative model; D31's stale "per batch" title was a confusion source), `0039` (commitment fully cascaded into `repl/spec.md` §15.4 + `facades/types.md` §"Symbol table" + `cranelisp-types/src/module.rs` at S69 Phase 3 — per-entry `seq: u64` + `next_seq` + `StructuralDeclEntry` upgrade; D39's `defn_order: Vec<Symbol>` shape obsoleted).

## Cross-References

- `principles.md` — architectural principles (index; per-Principle bodies in `principles/NN-*.md`; auto-imported by `.claude/commands/arch.md`)
- `bounded-contexts.md` — per-surface full statements
- `facades/{crate}.md` — per-surface facade specs (as-designed)
- `overview.md` — newcomer entry point bridging spec ↔ tests ↔ design ↔ code
- `sprints/METHOD_PROPOSED.md` — methodology
- `.claude/commands/arch.md` — `/arch` skill definition (the workflow layer)
- `sprints/reimplementation.md` — full reimplementation strategy (historical; M11 considers archive)
- `src/CLAUDE.md` — cross-cutting source conventions (error handling, code structure, naming)
- `sketch/audits/*.md` — structural debts to avoid (59 findings: 15 HIGH, 23 MEDIUM, 21 LOW)
- `sketch/src/` — prototype source as reference oracle (solutions to language-level problems, NOT pipeline structure — the sketch has the same dual-pipeline debt)
- `archive/pipeline-convergence-review.md` — dual-pipeline defect analysis (origin of principles 11–13)

## Architectural Principles

Extracted to `principles.md` (S63). That file is the single canonical home and is auto-imported by `.claude/commands/arch.md`. Cite principles by name from `principles.md`; do not re-summarise the list here.

## String Newtypes

**Hard rule**: All identifier fields in boundary types MUST use the appropriate newtype, never bare `String`. This prevents accidental mixing of identifiers across semantic categories (e.g., passing a module path where a symbol name is expected).

| Newtype | Semantic meaning | Examples |
|---|---|---|
| `Symbol` | Local identifier — variable, function, operator, constructor name | `"foo"`, `"+"`, `"Some"`, `"_"` |
| `TypeName` | Type name (uppercase) — ADT, builtin, constructor | `"Int"`, `"Option"`, `"Color"` |
| `TraitName` | Trait name (uppercase) | `"Num"`, `"Display"`, `"Eq"` |
| `ModuleName` | Single module component (no dots) | `"core"`, `"option"`, `"math"` |
| `ModuleFullPath` | Dotted module path | `"core.option"`, `"user"` |
| `LinkerSymbol` | JIT linker name (mangled) | `"add$Int+Int"` |
| `FQSymbol` | Fully qualified: module + symbol | `{ module: "core.option", symbol: "Some" }` |

**When in doubt**: if a `String` field identifies something in the language (a name, a type, a module), it should be a newtype. The only bare `String` fields allowed are:
- Error messages
- Documentation strings
- Source text
- User-visible descriptions (e.g., `SpecialForm.description`)

All newtypes are generated via `string_newtype!()` which derives the standard trait set and implements `Deref<Target=str>`, `From<String>`, `From<&str>`, `AsRef<str>`, `Display`.

## Conventions

- All types in `cranelisp-types` derive `Serialize` + `Deserialize` for module caching

## Baseline-diff discipline (Sprint 67 close)

The S67 edge-settlement sprint established `cargo-public-api` baselines (`crates/cranelisp-{crate}/public-api.txt`) as the frozen contract at every crate edge. Future edge changes — anything that touches a crate's `public-api.txt` baseline — must, in the SAME change-set:

1. **Regenerate** the affected crate's `public-api.txt` via the canonical command `cargo public-api --omit blanket-impls,auto-derived-impls -p <crate> > crates/<crate>/public-api.txt` — mechanical and reproducible. The `--omit blanket-impls,auto-derived-impls` flags strip auto-generated noise (`::into`/`::borrow`/`::from`/`::clone`/`::Owned = T`/Debug etc.) that carries no semver signal; auto-trait impls (`impl Send/Sync/Freeze/Unpin/RefUnwindSafe for ...`) are deliberately KEPT because they are a real semver signal (e.g. a `Mutex` field flipping a type to `!Freeze`/`!Sync` is exactly the regression the baseline diff must catch).
2. **Update** the corresponding `facades/{crate}.md` to name + disposition each added/changed/removed item. For retired-facade crates, the canonical surface is the source rustdoc instead: per-item `///` + crate-root `//!` name the boundary, and the cross-surface narrative + invariants live in `bounded-contexts.md` (the cache submodule's surface lives in `crates/cranelisp-backend/src/cache/` rustdoc — it has no facade and no BC entry, being an implementation detail of backend). The only crate still carrying a `facades/{crate}.md` is `int`.
3. **Include the diff** in the commit, side-by-side with the source change that produced it. Reviewers (`/review`, the user) read the baseline diff alongside the facade diff to assess whether the change is a legitimate edge evolution or accidental surface leakage.

The facade compliance test scaffolded in S67 Wave 0 (`/qa`) asserts that every pub-api line in the baseline is named in the corresponding facade (or marked internal-but-exposed with rationale). Skipping the facade update breaks the test; skipping the baseline regeneration breaks the next baseline-diff check at PR time. The two-update discipline is the durable enforcement mechanism — no edge change is "done" until both files have caught up.

Skill responsibility split: `/dev` (per crate) regenerates the baseline as part of the implementing change-set; `/design` (per crate) updates the facade to match; `/review` confirms both are present in the same diff at PR time.
