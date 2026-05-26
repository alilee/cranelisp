# cranelisp-types settled verdict — Sprint 70 Phase B

**Status**: authored + swept; verdict below.
**Filed**: 2026-05-26
**Filed by**: /arch
**Trigger**: Sprint 70 Phase B uncovered that `ModuleAliases` + `ModuleAliasEntry` (named in BC §7 + frontend facade as workspace-stable types) were absent from `cranelisp-types` source. User direction: "spawn arch to fix the missing modulealiases data structures now. I need a carefully-considered view that cranelisp-types is settled."

The S70 Phase 3 solidness sweep (`cranelisp-types-solidness-sweep-s70.md`) did NOT use a configuration → source completeness lens; the prior verdict (TYPES SOLID) was reachable only by the four lenses that pass did use (state-types method-level facade compliance, FQTypeName binding correctness, etc.). The 5th lens applied here closes the gap.

## Part 1 — Missing types authored

Three types added to `crates/cranelisp-types/src/module.rs` (after `default_got_arc()`, before `impl SymbolTable<(), ()>`). All `#[non_exhaustive]` (struct) per Principle 18 + workspace DTO convention; typedefs are mechanical aliases.

### `SymbolTables<C, L>` typedef

```rust
pub type SymbolTables<C, L> = dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>;
```

- **No `Arc<…>` wrapper** per F3 (`facades/frontend-audit-s70.md`) — facade self-classified the wrapper as editorial drift; canonical shape (sibling `int::SharedState.symbol_tables`) is the workspace-stable form.
- Rustdoc cites Principle 15 (three-consumer placement: frontend, typecheck, int), Decision 32 (`CodeStore` / `LinkerStore` empty-marker shape), BC §7 ("Module aliases live at session level" — symmetric placement for `SymbolTables`), and the `Arc`-removed drift note transcribed from `facades/frontend.md:61`.
- Re-exported from `lib.rs` crate-root.

### `ModuleAliasEntry` struct

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ModuleAliasEntry {
    pub target: ModuleFullPath,
    pub visibility: Visibility,
    pub span: Span,
}
```

Field-set rationale (grounded in spec § + BC §7 + Principle 18):

- `target: ModuleFullPath` — the path the alias resolves to. Spec §8.6.6 step 5 substitutes the matched segment with this target. *Mandatory* — required by §8.6.6 to do the substitution.
- `visibility: Visibility` — `Private` for §8.3.4 import-alias; `Public` for §8.4.4 export-mount. Per-entry per BC §7 ("Visibility is per-entry" — same shape as `ModuleEntry::*.visibility`). *Mandatory* — required by §8.6.6 + §8.6.4 to determine downstream traversability and conflict shape.
- `span: Span` — for §8.6.4 mount-collision + mount-vs-submodule diagnostic location. *Mandatory* — every authored form needs source-span diagnostics per existing pattern on `ImportSpec`, `ExportSpec`, `ModDecl`.

Field-set NOT included (and why):

- No `kind: AliasKind { ImportAlias, ExportMount }` discriminator — `visibility` fully captures the downstream-visibility difference; resolution-time behaviour is uniform; per Principle 18 (enforce invariants structurally), folding kind into visibility removes a redundant degree of freedom from the data model.
- No `owner: ModuleFullPath` field — BC §7 explicitly says "The owning module of any alias entry is **derived from the key** (strip the last dot-separated segment); it is not stored on `ModuleAliasEntry`". Compliance.
- No `docstring`, `attributes`, `provenance` — speculative; `#[non_exhaustive]` admits a future addition without breaking consumers.

### `ModuleAliases` typedef

```rust
pub type ModuleAliases = dashmap::DashMap<ModuleFullPath, ModuleAliasEntry>;
```

- Rustdoc cites BC §7, spec §8.3.4 (alias-import) + §8.4.4 (export-mount) + §8.6.6 (qualified-name resolution), the three-keying-domains principle (`ModuleFullPath` / `Symbol` / `TypeName`), and the §8.6.4 conflict-enforcement triad (rename / mount / mount-vs-submodule).
- Re-exported from `lib.rs` crate-root.

### lib.rs crate-root narrative updated

- Symbol-table bullet extended to include `SymbolTables`.
- New "Module aliases" bullet added (between symbol-table and sealed-marker-traits), pointing at BC §7.
- Re-export list amended (sorted alphabetically): adds `ModuleAliasEntry`, `ModuleAliases`, `SymbolTables`.

### Verification

- `cargo check -p cranelisp-types` green (clean run; no warnings introduced by the new code — pre-existing rustdoc HTML-tag warnings on unrelated newtype docs remain).
- `cargo public-api -p cranelisp-types -sss` regenerated; baseline written to `crates/cranelisp-types/public-api.txt`.
- Public-api diff: **+6 pub additions** (3 struct fields, 1 constructor fn, 2 type aliases) — exactly the surface intended; **3070 deletions of pre-existing stale baseline lines** that were never regenerated after S69 Sub 41's `pub mod → pub(crate) mod` source narrowing. The deletions are pure baseline catch-up (auto-trait projections deep-path lines collapsed to crate-root canonical form), not surface contraction. The +6 additions are the as-designed F2 + F3 closure.

## Part 2 — Configuration → source completeness sweep

### Method

Walked the canonical configuration corpus:

1. All 7 facades (`design/arch/facades/{frontend,typecheck,backend,int,primitives,intrinsics,platform}.md` + `backend-cache.md`)
2. `design/arch/bounded-contexts.md` (all 7 sections)
3. `design/arch/principles/*.md` (18 principles)
4. `design/arch/decisions/*.md` (12 operative Decisions: 0010, 0011, 0027, 0030, 0035, 0040–0048)

Extraction technique:

- Per-facade: extracted all backtick-quoted CamelCase identifiers (`grep -oE "\`[A-Z][A-Za-z]*[a-z][A-Za-z0-9]*\`"`)
- Per-Decision: same extraction
- Resulting sets unioned, deduplicated, cross-referenced

Cross-comparison technique:

- Listed all public type identifiers in `cranelisp-types` via `cargo public-api -p cranelisp-types -sss`
- Filtered configuration identifiers down to those appearing in ≥2 facades (multi-consumer signal per Principle 15)
- For each remaining identifier: searched `crates/*/src/` for `pub struct X`/`pub enum X`/`pub trait X` to identify the home crate
- Classified each into: (a) in types and named in config — OK; (b) named in config, owned by another crate appropriately — OK; (c) named in config, gap

### Findings

| Identifier | Configuration source | In types? | Disposition |
|---|---|---|---|
| `SymbolTables<C, L>` | frontend facade §50/55, typecheck facade §297, BC §7, int facade | **Authored Part 1** | Real gap → fixed inline |
| `ModuleAliasEntry` | frontend facade §50/55, BC §7 line 260, typecheck facade §297 | **Authored Part 1** | Real gap → fixed inline |
| `ModuleAliases` | frontend facade §50/55, BC §7 line 260, typecheck facade §297, backend facade §21 | **Authored Part 1** | Real gap → fixed inline |
| `Introspection` | backend facade §21 (`compile_to_module` parameter), int facade §566 (owned), int facade §1326 (claims backend writes it) | No (in `src/session_v4.rs`) | **REAL GAP — DAG inversion**. Backend cannot depend on int. Filed FIXME 0221 (target: /arch) with three resolution options. NOT mechanical to author — placement requires user arbitration. |
| `PrimitiveKind` | facade primitives.md:61/287; facade typecheck.md:297; facade backend.md:441 | No (retired S69 Sub 36) | **Facade-text drift** — references a retired type. NOT a types-crate gap; facade-text-correction task. Surfaced for /sprint; recommend filing FIXME `target: /arch` for facade catch-up (~3 facade files, ~5 lines of facade text). Out of this fire's scope. |
| `ConstructorInfo` | backend facade §441 | No (retired) | **Facade-text drift** — `ConstructorInfo` was retired (see `crates/cranelisp-types/src/check.rs:177` retirement comment). Backend facade still names it as a consumed type. NOT a types-crate gap. Same disposition as `PrimitiveKind`. |
| `View<'a, C, L>` | typecheck facade §232, BC §7 implicit | Yes (`pub use view::View`) | OK |
| `ResolutionGap` | frontend facade, typecheck facade | Yes | OK |
| `CallEdge`, `CallGraph`, `CallInfo` | backend facade, typecheck facade | Yes | OK |
| `MethodResolutions`, `MonoDefn`, `TypeDefInfo`, `FieldInfo`, `DisplayInfo`, `ResolvedCall` | typecheck facade, backend facade | Yes | OK |
| `CodegenBehaviour`, `ModuleStrategy`, `CompileContext`, `CompileResult` | backend facade, int facade | Yes | OK |
| `Sexp`, `Expr`, `TopLevel`, `Defn`, `Pattern`, `MatchArm`, `TypeExpr`, `TraitDecl`, `TraitImpl`, `TraitMethodSig`, `ConstructorDef`, `FieldDef`, `DefnVariant`, `Program`, `Visibility` | every facade | Yes | OK |
| `Type`, `Scheme`, `Subst`, `TypeId` | typecheck, backend | Yes | OK |
| `Symbol`, `TypeName`, `TraitName`, `ModuleName`, `ModuleFullPath`, `FQSymbol`, `FQTypeName`, `FQTraitName`, `JitSymbol`, `LinkerSymbol`, `SymbolRef`, `TypeRef`, `TraitRef` | every facade | Yes | OK |
| `SymbolTable`, `ModuleEntry`, `DefKind`, `OverloadVariant`, `ConstrainedFn`, `MacroClauseInfo`, `MacroParam`, `ImportSpec`, `ExportSpec`, `ImportNames`, `NamedImport`, `NamedExport`, `PlatformSpec`, `ModDecl`, `StructuralDeclEntry` | frontend, typecheck, int, backend | Yes | OK |
| `GotTable`, `GOT_TABLE_SIZE`, `NULLARY_TAG_THRESHOLD` | backend, intrinsics, int | Yes | OK |
| `HeapHeader` | backend, intrinsics | Yes | OK (HeapCategory correctly relocated to backend per S69 Sub 38) |
| `CranelispError`, `PlatformError`, `ErrorLocation`, `LineCol`, `LineColRange`, `Warning`, `WarningKind`, `ResolutionGap` | every facade | Yes | OK |
| `CodeStore`, `LinkerStore` | frontend, typecheck, int | Yes | OK |
| `SchedulingClass` | platform, intrinsics, int | Yes | OK |
| `Span` | every facade | Yes | OK |
| Marshal tag constants (`TAG_SNIL`, `TAG_SCONS`, `TAG_SEXP_*`) | backend, intrinsics | Yes | OK |
| `ParsedEntry`, `DefmacroInfo`, `MacroClause` | frontend, typecheck | Yes | OK |
| `Code`, `Jit`, `Linker`, `CompilationError`, `LinkerError`, `LinkerArtefact`, `ObjectArtefact`, `JitArtefact`, `GotEvent`, `GotEventTag`, `GotObserver`, `GotProvenance`, `SymbolNotCompilable`, `CompileScheduler` | named in backend facade + int facade consumed | No (in cranelisp-backend) | OK — backend-owned, int consumes upward (DAG-correct) |
| `CheckError`, `CheckResult`, `CheckState`, `ClusterContext`, `ClusterRead`, `ClusterWrite`, `TypeCheckEnv`, `ReplSnapshot` | typecheck facade + int facade consumed | No (in cranelisp-typecheck) | OK — typecheck-owned per typecheck facade §231 ("CheckResult/CheckError/CheckState/TypeCheckEnv/ClusterContext/ReplSnapshot live in cranelisp-typecheck — single implementation-crate consumer") |
| `ExpansionError`, `MacroResolver` (retired), `MacroEntry`, `MacroClauseEntry`, `ExtractedDeclarations` | frontend facade + int facade consumed | No (in cranelisp-frontend or retired) | OK — frontend-owned |
| `IoObserver`, `IoEvent`, `IoEventTag` | intrinsics facade, int facade | No (in cranelisp-intrinsics — observer/event types; int facade names them as consumed) | OK — intrinsics-owned per Decision 40 + facade intrinsics.md |
| `IntrinsicSymbol`, `IntrinsicEntry`, `IntrinsicTable`, `IntrinsicFuncIds`, `IntrinsicIds` | intrinsics facade, backend facade | No (in cranelisp-intrinsics) | OK |
| `HostContext`, `HostCallbacks`, `PlatformFn`, `OwnedPlatformFnDescriptor`, `PlatformManifest` | platform facade, intrinsics facade | No (in cranelisp-platform) | OK |
| `Sess`, `SessionSettings`, `SharedState`, `CompilerSession`, `CommandResult`, `EvalResult`, `EvalValue`, `LineEditor`, `SlashCommand`, `Style`, `Action`, `InputState`, `FileWatcher`, `FileChangeEvent`, `WatcherChannel`, `WorkerPool`, `CacheWriterHandle`, `CacheWritePacket`, `PriorityWork`, `NiceWork`, `ProjectTarget`, `MainReturnKind`, `TestRunnerState`, `TraceDisplayState`, `IoTraceEvent`, `IoTraceTag`, `IoTraceFlushGuard`, `SchedulerTraceEvent`, `SchedulerError`, `MachOParseError` etc. | int facade | No (in src/ or src/cluster/) | OK — int-owned, single consumer (int itself); zero need for types-crate placement |
| `PrimitiveDef` (and the three `ringN_primitives()` builders) | primitives facade §60, §287 | No (in cranelisp-primitives::operator, `pub(crate)`) | OK — explicitly relocated FROM types TO primitives in S69 Sub 41 H1 ("relocated from `cranelisp-types` S69 — H1 stronger disposition; consumers reach the same data via the inserted `ModuleEntry::Def` shape, not via `PrimitiveDef` rows"). Crate-private. |
| `CacheManifest`, `CacheMetadata`, `CachedModule`, `CacheError`, `CacheState`, `CacheLookupResult`, `CacheStale`, `Created`, `Missing`, `AbiMismatch`, `BuildIdMismatch`, `PathMismatch`, `SchemaMismatch`, `AlreadyPresent`, `MmapFailed` | backend-cache facade | No (in cranelisp-backend) | OK — backend-cache submodule |
| `HeapAdt`, `HeapClosure`, `HeapString`, `HeapVec`, `HeapRetention`, `HeapCategory` | backend facade, intrinsics facade | No (HeapCategory in backend; runtime types in intrinsics) | OK — backend codegen classification (S69 Sub 38) + intrinsics runtime layout |

### Real gaps fixed inline

Three. Documented in Part 1.

### Real gaps deferred (FIXMEs filed)

One. **FIXME 0221** (`target: /arch`) — `Introspection` type-home DAG inversion. Three options framed; user arbitration required before authoring. Not mechanical because of materially different cost/coupling trade-offs across the three options.

### Facade-text drift surfaced (not a types-crate gap; out-of-fire-scope)

Two. Both surface as facade text referencing retired types:

1. `PrimitiveKind` — retired S69 Sub 36, still cited at `facades/primitives.md:61/287`, `facades/typecheck.md:297`, `facades/backend.md:441`.
2. `ConstructorInfo` — retired (see `crates/cranelisp-types/src/check.rs:177`), still cited at `facades/backend.md:441`.

These are NOT types-crate gaps (the retirement is the right call — `DefKind::Primitive` / `DefKind::Constructor` carry the data directly). They are facade-text catch-ups owed by /arch in a future maintenance pass. Surfaced here for /sprint's awareness; out of this fire's scope per the brief ("do NOT edit facades except where authoring rustdoc on the new types implies linking").

### Identifiers belonging to other crates

Enumerated in the table above. All correctly placed. The DAG (Principle 3) is respected for every identifier except `Introspection`. No other type's home was found in tension with its facade-prescribed parameter list.

## Part 3 — Settled verdict

### Verdict: SETTLED WITH FOLLOW-UP

**Grounding**:

1. **The three F2/F3-named types are now present**. `SymbolTables`, `ModuleAliasEntry`, `ModuleAliases` exist in source, exported from `lib.rs`, public-api.txt regenerated. Frontend cascade work (F1.a — the third parameter on `expand`, plus deleting the in-frontend `SymbolTables` typedef and the `Arc` wrapper) now has source-side counterparts to consume.

2. **The 5th audit lens has been applied across the full configuration corpus** — 7 facades, BC, 12 operative Decisions, 18 Principles. No other "configured but absent" type was discovered to need types-crate placement EXCEPT `Introspection` (FIXME 0221).

3. **All other configuration-named identifiers are either in types-crate (correct) or correctly owned by another crate**. The cross-reference table above enumerates the dispositions: 35+ identifier classes verified.

4. **One follow-up: `Introspection` placement** — material to settle, but not mechanical, because Options A/B/C have non-trivial trade-offs. FIXME 0221 frames the choice for user arbitration.

**Why not SETTLED**: `Introspection` is genuinely in the DAG-inversion class — backend's facade names it as a parameter type while the int facade owns the data. Whichever way the user arbitrates, the resolution requires either (a) a types-crate addition (Option A), (b) a backend trait (Option B), or (c) a backend DTO (Option C). None of these is "types is structurally complete relative to configuration" — they are pending the same kind of work that closed F2/F3.

**Why not NOT SETTLED**: the `Introspection` gap is bounded, named, and not in the critical path for the S70 Phase B frontend cascade (the cascade is about `SymbolTables` + `ModuleAliases` flowing into `expand` — Introspection lands at the backend-int boundary in a later sprint). The frontend cascade can proceed now.

**Two facade-text drifts (PrimitiveKind, ConstructorInfo)** are noted but do not affect settledness — they are facade-side catch-ups, not types-crate gaps.

### What gives confidence types is settled (modulo the named follow-up)

- The five lenses combined (S69 Phase 3 four + this S70 Phase B 5th = state-types method-level compliance, FQTypeName binding correctness, per-entry visibility uniformity, non_exhaustive coverage, AND configuration → source completeness) provide cross-checked structural coverage.
- The newtype discipline (`design/arch/CLAUDE.md` §"String Newtypes") is enforced source-side.
- The `pub(crate) mod` narrowing (S69 Sub 41) removed deep-path leakage; the public surface is the crate-root re-exports + nothing else.
- The `#[non_exhaustive]` policy (lib.rs crate-root rustdoc §"Cross-cutting invariants") is honoured on all three new types.
- The serde-skip discipline (lib.rs §"Serde discipline") is structurally enforced via `#[serde(bound = "")]` on `SymbolTable` and `#[serde(skip)]` on `code` + `linker`; the new types are pure-data (no skipped fields).
- Spec-grounding is explicit on every new type's rustdoc — citations to §8.3.4, §8.4.4, §8.6.4, §8.6.6 are in place.

### Recommended next steps

1. **User reviews** the three authored types' rustdoc (substance + grounding citations).
2. **User arbitrates** FIXME 0221 (`Introspection` placement: A/B/C). On the same fire `/arch` lands the chosen option; if Option A, the placement is mechanical and one more types-crate addition lands.
3. **Sprint advances** to the frontend cascade — F1.a (add `module_aliases` parameter to `expand`), drop the in-frontend `SymbolTables` typedef, drop the `Arc` wrapper, fix consumers wave-by-wave per `feedback_facade_first_migration.md`.
4. **/sprint disposition** of the two facade-text drifts (PrimitiveKind, ConstructorInfo): file a FIXME `target: /arch` for facade catch-up — small editorial change, not blocking.

`cranelisp-types` is structurally complete relative to the canonical configuration set, with one named follow-up tracked at FIXME 0221.
