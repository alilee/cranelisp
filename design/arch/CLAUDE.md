# design/arch/

Architecture deliverables for the Cranelisp reimplementation. Owned by `/arch`.

Per `sprints/METHOD_PROPOSED.md` §14.1, this `CLAUDE.md` carries domain-local content only — local conventions, the Decisions index, and pointers to canonical documents. Methodology rules live in `METHOD_PROPOSED.md`; architectural principles live in `principles.md`; skill workflows live in `.claude/commands/arch.md`.

## Canonical documents (the target documentation set)

| File | Purpose |
|---|---|
| `overview.md` | Bridge document — the newcomer entry point. How the language is realized through the surfaces, tested by `/qa`'s integration suite, embodied in the crates. |
| `principles.md` | Architectural principles — index. Each Principle is one file at `principles/NN-{slug}.md`. Auto-imported by `.claude/commands/arch.md`. |
| `principles/` | Architectural Principles register; one file per Principle; index in `principles.md`. |
| `bounded-contexts.md` | Per-surface bounded-context full statements (Frontend, Typecheck, Backend, Runtime, Platform, Binary/int, plus types crate). |
| `facades/{crate}.md` | Per-surface facade specs — as-designed public surface. One file per surface. |
| `interfaces.md` | Narrative companion to `crates/cranelisp-types/`. |
| `decisions/` | Decisions register; one file per Decision; index in this CLAUDE.md (see "## Decisions" below). |
| `fixmes/` | FIXMEs register; one file per FIXME (`design/arch/fixmes/NNNN-name.md`). |
| `sequences/` | Current target sequence diagrams (`.mmd` + rendered `.svg`). |

## Sorting buckets

| Directory | Purpose |
|---|---|
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
- `archive/facades-runtime.md` — pre-D43 runtime facade; content migrated to `facades/primitives.md` + `facades/intrinsics.md` (S65 W1 — Decision 43 crate split)

## Decisions

Each Decision is one file at `decisions/NNNN-{slug}.md`. Index:

The active register holds Decisions whose outcome is NOT yet fully embodied in the architecture (facade + BC + sequence diagrams + Principles). Once a Decision's commitment lands fully into the architecture, the Decision becomes vestigial and moves to `legacy/decisions/` (or deletes if also retracted/superseded). The principle: re-derivation from the canonical set + Principles should be sufficient for fully-landed work; explicit Decisions persist only for environmental constraints, pre-implementation commitments, and forward handoffs.

- [0010](decisions/0010-base-pointer-abi.md) — Base-pointer ABI (environmental — captures rejected interior-pointer alternative)
- [0011](decisions/0011-embedded-drop-glue-ptr-in-closures.md) — Embedded drop_glue_ptr in closures (environmental — captures rejected side-table alternative + cross-module closure constraint)
- [0027](decisions/0027-g8-lands-before-g9.md) — G8 lands before G9 (environmental — borrow-checker sequencing rationale)
- [0030](decisions/0030-form-by-form-scheduler-mutual-imports.md) — Form-by-form scheduler deadlocks on mutual imports (environmental — coordination constraint future readers will hit)
- [0031](decisions/0031-one-jitmodule-per-compile-batch.md) — One `JITModule` per compile batch; `Arc<Jit>` on `ModuleEntry::Def.code`; custom `Drop` calls `unsafe free_memory()` (environmental — Cranelift `Memory::drop` evidence; amended Sprint 64 per Decision 41)
- [0035](decisions/0035-code-enum-integration-layer.md) — `Code` enum location (operative; amended Sprint 64 per Decision 41 — Code now in `cranelisp-backend`; amended Sprint 66 — variants slim to lifecycle owner only `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)`. The S66 unification (`b09ec76`) briefly relocated the per-entry `ptr` to a sibling `ModuleEntry::Def.fn_ptr` field; the same-day rollback `1dc57ae` removed that field as redundant with the per-module `GotTable`. **Post-rollback canonical statement: GOT is the single source of truth for callable addresses; `ptr` lives in `SymbolTable.got()` indexed by `ModuleEntry::Def.got_slot`. No per-entry pointer field.**)
- [0040](decisions/0040-runtime-trace-io-trace-relocate-to-int.md) — `(trace ...)` is a REPL/`--run`-only special form; `trace.rs` and `io_trace.rs` relocate **in full** (bodies + symbol registrations) to int; `--link` mode rejects the form at compile time. `IoObserver` callback registration API resides in `cranelisp-intrinsics` post-Decision-43 (originally specified to remain in runtime; the registration-site host moved with the D43 split — see `facades/intrinsics.md` §"IO observation"). BC §4b carries the contract. Amended 2026-05-16 (S67 W4) to Path B1 (full deletion; user-arbitrated) — supersedes the earlier B2-flavoured §"Shape" reading. Pre-implementation; tracked by FIXME 0103 + cascading FIXMEs 0197–0202.
- [0041](decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md) — `compile_to_module` per-symbol JIT cardinality; `Code` moves to `cranelisp-backend`; backend writes shared state directly; `Result<(), CompilationError>` (pre-implementation; amends 31, 35)
- [0042](decisions/0042-platform-error-adopts-error-location.md) — `PlatformError` is a `cranelisp-types`-hosted enum with `ErrorLocation` carriers per variant; surfaces via `CranelispError::Platform` (pre-implementation)
- [0043](decisions/0043-runtime-split-into-primitives-intrinsics.md) — `cranelisp-runtime` splits into `cranelisp-primitives` + `cranelisp-intrinsics`; backend has no trait knowledge (retracts 14, reframes 15; pre-implementation; tracked by FIXME 0150)
- [0044](decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md) — Cluster-atomic typecheck via orchestrator-owned staging; `View<'_, C, L>` newtype; reframes 0038's per-form check_form shape (pre-implementation; filed by FIXME 0166; **amended Sprint 66 Phase 3 by FIXME 0167** — Approach B + `ClusterContext` introduction; pass signatures take `&mut ClusterContext` and return `Result<(), CheckError>`; staging mutation flows through the existing `current_symbol_table_mut` accessor so the 91 register-call sites in typecheck do not change individually; invariant 2 revised — passes are pure with respect to live state, may mutate orchestrator-handed staging via the same accessor used in committed-mode; **further amended Sprint 66 Phase 3 by FIXME 0168** — Sequencing splits Wave 3a into α — locality-correctness refactor — before β — triad re-fire — per Decision 0046; **further amended 2026-05-13 third amendment** — the two-pass facade split (`check_form_signatures` + `check_form_body`) collapses into a single `check_forms(parsed: Vec<ParsedEntry>, ctx: &mut ClusterContext, symbol_tables: &SymbolTables) -> Result<(), CheckError>` free function; internal two-pass discipline + Pass-1-to-Pass-2 working state are internal to the call frame; `ModuleCheckAccumulator` retired from both typecheck and `int` public surfaces — cross-symbol bookkeeping migrates onto `ProcessedCluster` fields; state-threading hole closed by construction)
- [0045](decisions/0045-traitimpl-storage-in-trait-defining-module.md) — `ModuleEntry::TraitImpl` is written to the **trait's defining module**; importers discover impls by chain-following the trait reference (per-symbol `Import`/`Reexport`) back to its home module and probing for `impl$FQTypeName$FQTraitName`; pattern (b) selected over (a)/(c)/(d) on chain-follow simplicity (no closure walk; no cycle detection) + Principle 7 + Principle 17 grounds; user-arbitrated 2026-05-10 (Sprint 66 Wave 3a-α post-mortem); α's first pass `ab068e2` embodied pattern (a) and is rolled back + redone (filed by FIXME 0168; pre-implementation)
- [0046](decisions/0046-wave3a-locality-refactor-precedes-triad.md) — Wave 3a splits into α — locality-correctness refactor across `crates/cranelisp-typecheck/src/{checker,infer,traits,builtins}.rs` per Principle 17 — before β — cluster-atomic triad implementation per Decision 44 (amends 0044; pre-implementation; ~3–5d α + ~3–4d β; filed by FIXME 0168)
- [0047](decisions/0047-fqtypename-binding-at-resolved-stage-boundaries.md) — FQTypeName is binding as the cross-crate boundary type for resolved-stage type identifiers; two exceptions named (reverse-lookup; receiver-pinned). Closes FIXME 0151 at S67 W5 acceptance. Filed Sprint 67 (Phase 3 W0 — second user-challenge scope amendment).

Legacy Decisions (outcome fully embodied in architecture; preserved in `legacy/decisions/` for narrative continuity) — `0001`–`0006`, `0008`–`0009`, `0012`–`0013`, `0016`, `0018`–`0019`, `0021`–`0026`, `0029`, `0032`–`0034`, `0036`–`0039`. Retracted/superseded Decisions deleted (rely on git for history): `0007`, `0014` (retracted by 43; commit `754d525`), `0015` (reframed by 43; commit `754d525`), `0017`, `0020`, `0028`.

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

1. **Regenerate** the affected crate's `public-api.txt` via `cargo public-api --diff-git-checkouts ... > crates/.../public-api.txt` (or equivalent — keep the regeneration mechanical and reproducible).
2. **Update** the corresponding `facades/{crate}.md` (or `facades/backend-cache.md` for the cache submodule) to name + disposition each added/changed/removed item.
3. **Include the diff** in the commit, side-by-side with the source change that produced it. Reviewers (`/review`, the user) read the baseline diff alongside the facade diff to assess whether the change is a legitimate edge evolution or accidental surface leakage.

The facade compliance test scaffolded in S67 Wave 0 (`/qa`) asserts that every pub-api line in the baseline is named in the corresponding facade (or marked internal-but-exposed with rationale). Skipping the facade update breaks the test; skipping the baseline regeneration breaks the next baseline-diff check at PR time. The two-update discipline is the durable enforcement mechanism — no edge change is "done" until both files have caught up.

Skill responsibility split: `/dev` (per crate) regenerates the baseline as part of the implementing change-set; `/design` (per crate) updates the facade to match; `/review` confirms both are present in the same diff at PR time.
