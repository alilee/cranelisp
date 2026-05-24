# cranelisp-types — Sprint 69 facade audit (per-item analysis, design-intent grounded)

**Audit triple**: `crates/cranelisp-types/src/lib.rs` (declared surface, 82 LOC) × `design/arch/facades/types.md` (binding contract, 1038 LOC) × `crates/cranelisp-types/public-api.txt` (live boundary, 3772 LOC).

**Date**: 2026-05-19 (S69 Phase 3 Wave 1 — re-author #2)
**Auditor**: /design (cranelisp-types narrow deployment)
**Inputs frozen at**: post-S68 close (`9516dfc`).
**Discipline**: per `memory/feedback_audit_per_item_analysis.md` (2026-05-19 amendment). Each finding carries five explicit blocks: (1) facade expects, (2) source does, (3) **design intent** — the architectural-configuration grounding of the facade element; (4) difference implies, (5) disposition. **The default disposition when the facade is target-stating per Decision / Principle / FIXME is *source moves*** — because the facade IS the binding intent. "Facade moves" is correct only when a later Decision retracts the facade element, the facade authoring was sloppy with no Decision grounding, or source has evolved past the facade and a retroactive Decision update would be appropriate.

This file overwrites the prior re-author (2026-05-18) which failed the new discipline: it dispositioned the SymbolTable concurrency complex (S-DRIFT-19/20/21 + H3/H5/H7 + C-HOLE-5) as "Requires /arch arbitration" or "Source moves" piecemeal, while missing that the broader pattern — Decisions 31, 32 (Clone super-bound rationale), 41 (`write_code(&self, …)`), 44 (cluster-atomic + `View`), 48 (`Code::Primitive`), and the `concurrency-symbol-table-entry.mmd` sequence diagram all explicitly target-state DashMap inner storage with per-entry locks, `&self` interior-mutable writes, encapsulating methods, atomic GOT swap — converges on **source moves** as the unambiguous disposition. The same misframing recurred across FQTypeName-binding fields (S-DRIFT-13, parts of H8), Decision-48 `Code::Primitive` (S-DRIFT-17), and Decision-39 spans on `ImportSpec`/`ExportSpec` (H11). This re-author re-grounds each item.

---

## 0. Summary up front

Structural invariant pass: zero `cranelisp_*` re-exports of other workspace crates' items (Principle 3 clean); the boundary remains data-only; every identifier field uses a newtype (Principle 15). The bottom-of-DAG hygiene continues to hold.

What the architectural configuration grounds, and which side of every drift carries the binding intent:

- **`SymbolTable` per-entry concurrency** (H3, H5, H6, H7, S-DRIFT-19/20/21, C-HOLE-5). Facade target-states `DashMap<Symbol, ModuleEntry<C>>` + `&self` writes via `insert_or_update` / `write_code` / `install_import_bindings` / `write_structural_decls` / `append_defn_order` + `AtomicUsize next_got_slot`. **Three independent Decisions ground this**: 0032 (Clone super-bound rationale: "DashMap iteration semantics. Several read-by-value access paths through `SymbolTable.symbols` (`DashMap<Symbol, ModuleEntry<C>>`) call `.clone()` on the entry to escape the lock guard's lifetime"); 0041 ("`symbol_tables: &DashMap<ModuleFullPath, SymbolTable<Code, ()>>`" + "`write_code(&self, sym, code)` — Decision 38's interior-mutable signature"); 0044 ("drained per-entry under inner-DashMap locks"). And the canonical sequence diagram `design/arch/sequences/concurrency-symbol-table-entry.mmd` is the explicit target state: PWa / PWb concurrently take `Ref[SymbolTable]` shared shard reads + inner-DashMap per-entry writes; `write_structural_decls` is a phase-0 brief `&mut`; `insert_or_update` and `write_code` are `&self`. **Source is un-migrated — HashMap + `&mut self`.** The disposition for this entire complex is **source moves**, not arbitration.

- **~~Macro callable shape~~** (S-DRIFT-5, U4) — **RESOLVED (Submission 13)**. Unified to `Def { kind: DefKind::Macro { clauses_meta, sexp, source } }` parallel to D49's `Def { kind: Constructor }` migration. The multi-clause-dispatch shape resolves structurally: per-clause GOT-callable via mangled-variant `UserFn` Defs (`{macro-name}$clause-{N}`), parallel to multi-sig fn variants (`add$Int+Int`). Parent metadata entry holds no own body; expansion-time dispatch walks `clauses_meta` then GOT-dispatches to the matched clause's variant Def. `MacroEnv` sidecar retires. See `facades/types.md` §"DefKind" `DefKind::Macro` for the manifestation site + dispatch story + three rejected alternatives (sibling-variant kept, entry-level trampoline, sexp/source at Def level).

- **FQTypeName binding** (S-DRIFT-1 partial, S-DRIFT-9, S-DRIFT-13 partial, H8 type). Decision 47 names `FQTypeName` as binding at resolved-stage boundaries with two narrow exceptions. The `Scheme.constraints: HashMap<TypeId, Vec<FQTraitName>>` in source IS the post-D47 shape (the facade's `Vec<TraitName>` is pre-D47 stale text). The `ResolvedCall::TraitMethod { trait_name: FQTraitName, …, impl_type: FQTypeName }` in source IS the post-D47 shape. **But this means the facade has stale text** at line 354 and at the §"Item-by-item disposition" `TraitMethod` row — the prior audit correctly called these "facade moves" but did not surface that the moves are **D47-mandated**, not editorial.

- **Decision 48 `PrimitiveKind { Inline | Extern | PlatformEffect }`** (S-DRIFT-17). **RESOLVED Submission 36 — scope-extended ModuleEntry settlement.** The original re-author's "facade moves to source's 3-variant split" framing held this fire's first read; user-questioning during the walk-through surfaced four convergent changes that retired the enum entirely instead. Settlement: (1) `PrimitiveKind` retired (Inline/Extern vestigial — verified by grep that no production consumer reads them; backend dispatches via GOT uniformly per D48; inline-eligibility encoded per-call-site in `ResolvedCall::BuiltinFn { name }`). (2) `jit_name: Option<JitSymbol>` retired from `DefKind::Primitive` (symbol-table key IS the JIT linker name uniformly per `src/CLAUDE.md` §"JIT Symbol Names"). (3) `PlatformEffect { scheduling_class }` promoted to `DefKind` sibling variant (Decision 26 invariant preserved at the new level). (4) `SpecialForm` promoted to `ModuleEntry` sibling variant (4-of-11 fields used; parallels Submission 30 `IntrinsicType` shape; per user direction "we want to settle ModuleEntry"). Reclassified D → "RESOLVED — scope-extended cluster correction." Audit-discipline lesson recorded in calibration table §7.

- **Per-name spans on imports/exports** (H11, S-DRIFT-4, S-DRIFT-12, U9, U10, U11). Facade names `NamedImport { name, span }` / `NamedExport { name, span }` + per-field span on `FieldDef`. Source has `Vec<Symbol>` + no per-field span. **The grounding is Decision 39** (per-defn source coordinate system; ErrorLocation per Decision 42). The facade's per-name spans are the structural prerequisite for the diagnostic-quality bar Decision 39 names. The prior audit framed this as "requires /arch arbitration on whether Decision 39 lands in S70" — but **Decision 39 isn't pending; it's already grounded in `ErrorLocation` (facade lines 759–804) and the per-defn-source plumbing**. The facade is target-stating per Decision 39. Disposition: **source moves**. Schedule is a separate question and is acceptable to defer; the disposition is not.

- **`get_type` return type** (H8). Facade: `Option<&TypeDef>`. Source has no `get_type` method. There IS a `TypeDefInfo` struct in source `check.rs`. The facade's name "`TypeDef`" without further qualification is a facade-text artefact — there is no Decision authoring a separate `TypeDef` newtype distinct from `TypeDefInfo`. **Disposition split**: source adds the method (per Decision 47 exception 2 — receiver-pinned); facade aligns the return type to source's `TypeDefInfo` (mechanical facade fix; no Decision authorising a separate `TypeDef`).

- **`SymbolTable.next_got_slot`** (S-DRIFT-21). Facade: `AtomicUsize`; source: `usize`. **Decision 32's Clone super-bound rationale + the concurrency sequence diagram + Decision 44's "per-entry under inner-DashMap locks" all premise concurrent slot allocation.** The atomic IS the target. Disposition: **source moves**, bundled with S-DRIFT-19.

- **`HeapCategory::classify` signature** (U22). Facade silent. Source declares `classify<C, L>(ty, Option<&DashMap<…, SymbolTable<C, L>>>)`. **Configuration check**: no Decision either authorises or retracts this surface. The function exists; backend consumes it. The facade silence is a documentation gap. Disposition: **facade moves** — but this is purely documentary catch-up, not a structural question. **Submission 38 update**: this framing was scope-incorrect — consumer trace surfaced a bounded-context violation (zero non-backend production consumers); reclassified to **RESOLVED by relocation** (HeapCategory moves cranelisp-types → cranelisp-backend; facade entry migrates to `backend.md` §"Heap classification"). See §"Finding U22" body for full closure.

Disposition class counts (59 findings):

| Class | Count | Meaning |
|---|---|---|
| **Source moves** (facade is target-stating per Decision / Principle / FIXME) | **27** | Source migration is owed. Wave 3+ source work. (Reduced by 1 in S31 — S-DRIFT-8 RESOLVED in-place by source-side promotion of `MethodResolutions` type alias to `#[non_exhaustive]` struct; direction "source moves" stood, landed in S31; ~10 typecheck consumer cascade sites deferred to wave-3. Incremented by 1 in S34 — S-DRIFT-10 reclassified from bucket C "arbitration genuine" to "source moves" + RESOLVED in-place by source-side rewrite of `View` from `pub enum` to `pub struct` with private fields per Decision 44 + Principle 18; typecheck ClusterContext pattern-match consumer cascade deferred to wave-3.) |
| Facade moves (facade text is stale, was sloppy, or source has evolved with retroactive Decision agreement) | 7 | Mechanical facade updates. Wave 2 facade-doc work. (Reduced by 4 across S23/S25/S26/S27 reclassifications + 2 more in S30 — S-DRIFT-2 + S-DRIFT-3 reclassified from "Facade moves" to "RESOLVED by deletion" when the S69 /spec fire surfaced that the reverse-lookup bridge was spec-violating, not just facade-misaligned + 1 more in S32 — S-DRIFT-9 reclassified to "RESOLVED — facade self-reconciliation + source `#[non_exhaustive]` catch-up"; facade line 513 was correct since D47 authored, lines 512 + 1792 were un-cascaded stale text, not source-facade drift. Submission 33 closed U12 + U13 + U14 + U15 in-place (facade-only catch-up; source already at target shape) — count decremented by 4. Reduced by 1 in S35 — S-DRIFT-6 reclassified from "Facade moves" to "Both move" — source narrowed `ast: Option<Defn>` → `Option<DefnVariant>` per minimum mechanism + Principle 7; facade catches up to the narrowed shape rather than ratifying the prior wider source. S-DRIFT-7 RESOLVED in-place as "Facade moves" — facade catch-up to source's `Box<DefKind>` per Principle 6. Reduced by 1 in S36 — S-DRIFT-17 reclassified from "Facade moves" to "RESOLVED — scope-extended cluster correction"; original "facade catch-up to D48-mandated 3-variant split" superseded by ModuleEntry settlement that retired `PrimitiveKind` entirely + retired `jit_name` field + promoted `PlatformEffect` to `DefKind` sibling + promoted `SpecialForm` to `ModuleEntry` sibling. Neither the facade-stale 2-variant nor the source-stale 3-variant shape was the target.) |
| **RESOLVED by deletion / self-reconciliation / scope-extended cluster correction** (audit's framing was superseded by a spec/Decision fire revealing the source was wrong, not the facade — or facade internal inconsistency where one location was correct and others were stale — or user-questioning surfaced a structural cluster opportunity that the original mechanical disposition missed) | 4 | S-DRIFT-2 + S-DRIFT-3 (S69 Submission 30 — `Type::from_name` / `Type::type_name` deleted; new `ModuleEntry::IntrinsicType` variant); S-DRIFT-9 (S69 Submission 32 — facade lines 512 + 1792 self-reconciled under Decision 47; line 513 was already correct; source `#[non_exhaustive]` policy catch-up bundled); S-DRIFT-17 (S69 Submission 36 — scope-extended ModuleEntry settlement: `PrimitiveKind` enum retired + `jit_name` field retired + `PlatformEffect` promoted to `DefKind` sibling + `SpecialForm` promoted to `ModuleEntry` sibling; original "facade catch-up to D48 3-variant split" framing superseded by user-questioning that surfaced the four convergent changes). |
| Both move | 9 | Each side adjusts; neither is wholly correct. (S-DRIFT-11 S23, S-DRIFT-12 S25, S-DRIFT-14 S26, S-DRIFT-13 S27 reclassifications + 4 prior + S-DRIFT-6 reclassified S35 — scope-correction from "facade moves" to "both move"; source narrowed `Option<Defn>` → `Option<DefnVariant>` per minimum mechanism, facade catches up.) |
| Arbitration — genuine cross-skill question the configuration does not ground | 0 | A2 closed by Submission 13 (see "Macro callable shape" bullet above). A5 (View enum-vs-struct opacity) RESOLVED (Submission 34) — source moved to struct with private fields per Decision 44 opacity intent + "newtype" terminology + Principle 18 (enforce invariants structurally); the bucket-C "arbitration genuine" framing was superseded by user direction — the discipline pattern that emerged through Group A/B (facade-as-target + Principle 18 when both options exist) settled the arbitration. |
| No action (auto-trait noise, already-covered) | 6 | Per audit discipline still gets a one-sentence rationale. |

**Prior re-author disposition flips**: 23 of the prior audit's "facade moves" recommendations are flipped to **source moves** under design-intent grounding. The calibration table in §7 enumerates them.

The configuration is unambiguous on the SymbolTable concurrency complex, on FQTypeName binding, on Decision 48's primitives uniform-module model (the original PrimitiveKind framing was superseded by Submission 36's ModuleEntry settlement — see S-DRIFT-17 closure), and on Decision 39's per-name spans. The audit names them as source-moves, and the wave-gate question for /sprint is only **scheduling** (S69 wave-3, S70, or later), not **direction**. The configuration is genuinely ambiguous in only two places (A2, A5).

**Calibration (S69 Phase 3, 2026-05-21 — Submission 14).** The audit's "facade-field-enumeration catch-up" frame is wrong for state types. Many findings of the form "source has field X, facade doesn't list it" are not field-gaps — they're consumers reaching past the facade because no accessor encapsulates the data. For each remaining finding, re-evaluate:

- Is the field part of the consumer contract (data-record DTO — `NamedImport`, `ImportSpec`, `ExportSpec`, `ModDecl`, `PlatformSpec`, `Span`, `FQSymbol`, `FQTypeName`, `TypeDefInfo`, etc.) or implementation detail behind an accessor (state type — `ModuleEntry`, `DefKind`, `SymbolTable`)?
- If implementation detail: the disposition is "facade names the accessor method, not the field." Field shape stays out of the facade. (Calibrating example: U5 — `param_names` is private storage; `ModuleEntry::arity()` is the contract, delegating to the data-owning `Type::fn_arity()`.)
- If data-record DTO field: the facade lists the field as part of the public surface.

The state-type-vs-DTO distinction is durable in `facades/types.md` §"Bounded-context invariants" #11; this calibration prompts the audit-side re-evaluation of any remaining U-findings still framed as "field-listing catch-up" against state-type hosts.

---

## Triage register (Submission 20)

After 19 walk-through submissions, the audit's per-finding dispositions have drifted from where the walk-through has been. Each remaining finding has been classified into one of four buckets. Bucket A findings are closed in-place by this fire; Bucket B / C / D findings carry an inline tag at the top of their body.

| Finding | Bucket | Rationale |
|---|---|---|
| H1 | A | Walk row 342 approved D48 cascade — `git mv operator.rs` into primitives crate + facade §"Operator / primitive registry" deletion; ring{0,1,3}_primitives retire. |
| H2 | A | Walk row 343 approved `io_inner_type → unwrap_io(&self) → &Type` rename + signature flip + 3-site consumer cascade. |
| H3 | A | Walk row 344 — H3+H4+H9+H10 bundle resolved with `next_seq: AtomicU64` + per-entry `seq: u64` replacing `defn_order` (D39 reconciliation). |
| H4 | A | Bundled in walk row 344 (H3+H4+H9+H10 bundle). |
| H5 | A | In /dev concurrency-cluster brief (SPRINT.md row 53 — Category A). Source-side method-add scheduled. |
| H6 | A | In /dev concurrency-cluster brief (SPRINT.md row 53). Walk row 345 retired D31 + relocated substance to D41. |
| H7 | A | In /dev concurrency-cluster brief (SPRINT.md row 53). |
| H8 | A | Walk row 346 — facade editorial fix (Option<&TypeDef> → Option<Ref<…>>); source-side method-add folds into concurrency cluster. |
| H9 | A | Bundled in walk row 344. |
| H10 | A | Bundled in walk row 344 (StructuralDecls replaced by StructuralDeclEntry-append). |
| H11 | A | Walk rows 347+348+349+350 — ImportNames locked to 5 spec-grounded variants; NamedImport gains rename; source migration in concurrency-cluster brief. |
| U1 | A | Walk row 341 — D49 (Constructors-as-Defs + `Expr::ConstrADT`) retired `ModuleEntry::Constructor`; `DefKind::Constructor` is the manifestation. |
| U3 | D | **No action (S69 Sub 40 confirms)** — audit's "No action — already aligned" disposition holds; documentation parity exists; `visibility: Visibility` field is informational stub for variant uniformity per `is_public` uniform check. |
| U10 | A | Walk row 348 — `U10 + alias-symmetry` resolved; `ExportSpec` gains `alias` + structurally identical to `ImportSpec`. |
| U11 | A | Bundled with H11 (walk row 347). |
| U12 | D | **RESOLVED (Submission 33)** — facade `linker: Option<L>` field added to §"Symbol table" shape summary with Decision 35 grounding (reserved-for-future-Linker-retention rationale). |
| U13 | D | **RESOLVED (Submission 33)** — facade `new_with_params(path)` enumerated in §"Symbol table" `impl<C, L, D>` block with Decision 35 instantiation-pattern grounding + Rust-default-type-param-inference rationale. |
| U14 | D | **RESOLVED (Submission 33)** — facade `into_concrete` enumerated on both `impl SymbolTable` (concrete `<(), (), ()>`) and `impl ModuleEntry<()>` blocks with Decision 35 cache-restore grounding. |
| U15 | D | **RESOLVED (Submission 33)** — facade `GotTable::new()` signature corrected to no-arg (matching source); fixed-capacity `GOT_TABLE_SIZE` paragraph added citing Decisions 23 + 48 (no Decision authorises a configurable surface). |
| U16 | D | **RESOLVED (Submission 39)** — facade enumerates three `ErrorLocation` constructors per Decisions 39 + 42 with producer-side guidance; dead fields `fq`/`line_col`/`context` retained as forward-looking suggestive surface (~357 total constructor calls traced; cleanup deferred until proven unfillable). |
| U17 | D | **RESOLVED (Submission 39)** — facade enumerates `LineCol::new` / `LineColRange::new` (bundled with U16). Zero call sites outside the type definitions; types exist as the typed shape of `ErrorLocation.line_col`. |
| U18 | D | Audit's disposition is "No action — auto-derive Default::default() = Sequential". |
| U19 | D | **RESOLVED (Submission 39)** — facade enumerates `PlatformError::location() -> &ErrorLocation` (no Option) per Decision 42 + Principle 7 symmetry with `CranelispError::location()`. |
| U20 | D | **RESOLVED (Submission 39) — facade enumeration + scope-extended structural narrowing** — three accessors (`message`/`span`/`location`) enumerated; `CranelispError::location()` signature narrowed from `Option<&ErrorLocation> → &ErrorLocation` per Principle 7 + Principle 18 + Decisions 39/42 invariant. Wave-3 cascade: 1 site (`src/main.rs:91`). |
| U21 | D | **RESOLVED (Submission 39) — audit's "No action" overridden** — facade names `impl From<PlatformError> for CranelispError` with one-line Decision-42 grounding per S67 baseline-diff discipline (every pub-api line named in the facade). |
| U22 | RESOLVED by relocation | **RESOLVED (Submission 38) — reclassified D→RESOLVED by relocation.** Original "facade moves" disposition was scope-incorrect: bounded-context violation surfaced by consumer trace (zero non-backend production consumers); `HeapCategory` relocated `cranelisp-types` → `cranelisp-backend`; facade entry migrates from `types.md` §"Heap layout" to `backend.md` §"Heap classification". `HeapHeader` retains as the genuine cross-crate layout contract. |
| S-DRIFT-1 | A | Walk rows 339+340 — (a) source-side `vars → type_vars` rename + (b) facade-side `Vec<TraitName> → Vec<FQTraitName>` both approved and applied. |
| S-DRIFT-2 | D | **RESOLVED (Submission 30 — closed by deletion)** — `Type::from_name` deleted from source; new `ModuleEntry::IntrinsicType { ty: Type, visibility: Visibility }` variant added for uniform intrinsic-type registration. The audit's "facade moves to source's `&str`" framing was superseded — the bridge was spec-violating per S69 /spec fire (FIXME 0216 — spec §3.1 / §8.9.1 / §8.11.4 sharpening: bare `:Int` requires prelude or explicit import). |
| S-DRIFT-3 | D | **RESOLVED (Submission 30 — closed by deletion)** — `Type::type_name` deleted from source; structural replacement via `ModuleEntry::IntrinsicType` (same as S-DRIFT-2). Audit's "facade catch-up" framing superseded — bridge was spec-violating, not just facade-misaligned. |
| S-DRIFT-4 | A | Bundled with H11 (walk row 347). |
| S-DRIFT-6 | D | **RESOLVED (Submission 35) — both move (scope-corrected from prior "facade moves")** — source narrowed `ast: Option<Defn>` → `Option<DefnVariant>` per minimum mechanism (discipline #4) + Principle 7 (single source of truth — Def's own `name`/`docstring`/`visibility`/`seq` fields are canonical for that metadata; the outer `Defn` wrapper duplicated them post-decomposition). Decision 22 (codegen-compilable predicate `ast.is_some()`) preserved — the predicate is indifferent to the payload type. Facade catches up to the narrowed shape. Wave-3 cascade: ~30-50 backend + typecheck consumer sites — `defn.params()` → `variant.params`; `defn.variants[0].body` → `variant.body`. |
| S-DRIFT-7 | D | **RESOLVED (Submission 35) — facade moves.** Adjusted facade to `kind: Box<DefKind>` with inline note citing Principle 6 (size discipline; pattern-match through `Box` is transparent). Editorial — no Decision specifically authors the boxing. |
| S-DRIFT-8 | D | **RESOLVED (Submission 31)** — source moves: `pub type MethodResolutions = HashMap<Span, ResolvedCall>` promoted to `#[non_exhaustive] pub struct MethodResolutions { pub resolved_calls: HashMap<Span, ResolvedCall> }` with `Default` derive + `new()` constructor. Grounded by facade §"`#[non_exhaustive]` policy" (binding) + Principle 8 (no interim implementations) + Principle 13 (`cargo-public-api`-gateable) + BC invariant 11 (data-record DTO — `resolved_calls` field IS the contract). Wave-3 cascade: ~10 consumer migration sites in `cranelisp-typecheck/src/{checker,infer}.rs` (mechanical `.X` → `.resolved_calls.X` rewrite; no semantic shift). |
| S-DRIFT-9 | D | **RESOLVED (Submission 32)** — facade self-reconciliation under Decision 47 + source `#[non_exhaustive]` policy catch-up (scope-extended per user direction to avoid revisiting this data structure). Facade line 512 misattribution corrected (`MethodResolutions.impl_type` → `ResolvedCall::TraitMethod.impl_type`); §"Item-by-item disposition" PIF row at line 1792 rewritten with correct 4-field `TraitMethod` shape (`trait_name: FQTraitName, method_name: Symbol, impl_type: FQTypeName, mangled_name: JitSymbol`) per D47 + `trait_resolution` moved to AutoCurry attribution. Source: added `#[non_exhaustive]` to `ResolvedCall` enum per facade §"`#[non_exhaustive]` policy" (no field-set changes — source already at D47-target 4-field shape). Wave-3 cascade: ~5-10 pattern-match sites on `ResolvedCall` in typecheck + backend need `_ =>` arms (mechanical). Cross-reference: line 512 misattribution flagged in Submission 31 closure also resolved here. |
| S-DRIFT-10 | **RESOLVED (Submission 34) — source moves** | Direction: source moves from `pub enum View { Single, Union }` to `pub struct View { staging: Option<&'a SymbolTable>, live: &'a SymbolTable }` with private fields per **Decision 44** opacity intent + **"newtype" terminology** + **Principle 18** (enforce architectural invariants structurally where possible — struct-with-private-fields is the structural option that prevents consumer-side staging-vs-live observation by construction). The audit's prior "arbitration genuine" framing (bucket C) was superseded by user direction — the discipline pattern that emerged through Group A/B (facade-as-target + Principle 18 when both options exist) settled the arbitration. Internal encoding: `staging: Option<&'a SymbolTable<C, L>>` (`Some` = cluster mode, `None` = committed mode); `live: &'a SymbolTable<C, L>` unconditional. Wave-3 cascade: typecheck ClusterContext consumers that pattern-match View variants migrate to `view.lookup(name)` / `view.iter()` method calls. **Closes Group C.** |
| S-DRIFT-11 | RESOLVED (Submission 23) | Both move — fused `params: Vec<(Symbol, Option<TypeExpr>)>` shape per Principle 18 (lockstep invariant folded into the type) + spec §5.1.1 EBNF (per-param independently-optional annotation) + spec §5.1 L41 (no return-type annotation syntax). User-arbitrated 2026-05-22; revises the prior audit's "facade moves" framing. |
| S-DRIFT-12 | A | RESOLVED Submission 25 — facade editorial (`name: Symbol`, `type_expr`) + source-side `span: Span` field add per Decision 39; Option A (`TypeExpr` unconditional, synthesised-`TypeVar`-for-bare convention) user-arbitrated 2026-05-22. Consumer cascade /dev wave-3. |
| S-DRIFT-13 | RESOLVED (Submission 27) | **Both move** — 5-field `pub struct TraitImpl { trait_name: TraitRef, target: TypeExpr, type_constraints: Vec<(Symbol, TraitRef)>, methods, span }` + new syntactic-stage newtypes `TraitRef { module: Option<ModuleFullPath>, name: TraitName }` and `TypeRef { module: Option<ModuleFullPath>, name: TypeName }` (in `cranelisp-types::newtype`) capture as-written qualification structurally. `TypeExpr::Named(TypeName)` / `Applied(TypeName, …)` cascade to `TypeRef` payloads. Two scope-corrections vs. prior framing: (1) source's `trait_name: TraitName` was wrong — `(impl fmt/Display ...)` requires qualification structurally; (2) the `target_type + type_args` split had no Decision-level grounding — spec §5.4 EBNF treats target as one grammatical unit. See finding closure below. |
| S-DRIFT-14 | RESOLVED (Submission 26) | Both move — target `pub struct TraitMethodSig { name, docstring, params: Vec<(Symbol, TypeExpr)>, ret_type, span, hkt_param_index, default_body: Option<Expr> }` (7 fields). Facade is target — source's `Option<Sexp>` had no Decision-level grounding after the Principle 11 misattribution was removed (Submission 23); per `feedback_hold_to_facade_default.md` default is source-moves. Per Principle 18 + spec §5.3 EBNF, `default_param_names` retired — names belong with params, not default body — fused into `params.0`. See finding closure below. |
| S-DRIFT-15 | RESOLVED (Submission 21) | Form-record narrow + platform-module architecture per spec §2.2.9 + §10.9 + §8.9.3 — `PlatformSpec` aligned to form-record shape; `ModuleEntry::PlatformDecl` retired; DLL handle on platform module's own `SymbolTable.dll` via `D: DllStore` generic. A7 closed by form-record framing. See finding body below for closure pointer. |
| S-DRIFT-16 | D | **RESOLVED (Submission 40) — source narrowing + facade enumeration + FIXME-cascade** — (1) `is_private: bool → visibility: Visibility` source narrowing per Principle 7 + Principle 18 (ModDecl was sole bool outlier in decl/entry family); (2) facade shape summary updated to 4 fields honestly enumerating `inline_body: Option<Vec<Sexp>>` with lifecycle note; (3) FIXME 0217 filed against `/int` for spec §8.2.2 step 2 (parent-file rewrite) implementation gap. Wave-3 cascade: ~15 consumer sites across frontend/worker/save (mechanical `.is_private` → `.visibility == Visibility::Private`). |
| S-DRIFT-17 | D | **RESOLVED (Submission 36) — scope-extended ModuleEntry settlement.** Original framing "facade catch-up to D48-mandated 3-variant split" was superseded by user-questioning that surfaced four convergent changes: (1) `PrimitiveKind` enum retired (Inline/Extern vestigial — verified by grep; backend dispatches uniformly via GOT per D48); (2) `jit_name: Option<JitSymbol>` retired from `DefKind::Primitive` (symbol-table key IS the JIT linker name uniformly per `src/CLAUDE.md` §"JIT Symbol Names"); (3) `PlatformEffect { scheduling_class }` promoted from `PrimitiveKind` sub-variant to `DefKind` sibling variant (cross-crate-load-bearing payload; Decision 26 invariant preserved at the new level); (4) `SpecialForm` promoted from `DefKind` variant to its own `ModuleEntry::SpecialForm` variant (4-of-11 fields used; parallels Submission 30 `IntrinsicType` shape). Wave-3 cascade ~100+ sites — typecheck builtins / worker / backend / primitives / runtime renames / tests. |
| S-DRIFT-18 | D | **RESOLVED (Submission 28)** — facade moves: `SYNTHETIC` flipped to associated-const idiom; scope-extension to document `Default` derive (Sub-25) + always-public `new()` / `merge()`. |
| S-DRIFT-19 | A | In /dev concurrency-cluster brief (SPRINT.md row 53). |
| S-DRIFT-20 | A | In /dev concurrency-cluster brief (bundled with S-DRIFT-19). |
| S-DRIFT-21 | A | In /dev concurrency-cluster brief (bundled with S-DRIFT-19). |
| S-DRIFT-22 | D | **RESOLVED (Submission 29)** — facade moves: scope-extended from audit's "no action" — applied three editorial sharpenings (factual error correction "atom/list/bracket" → 8 variants named including `Comment`; phrasing "preserves source spans" → "each carries Span"; document public methods `span()` / `format_flat()` / `format_indented()` / `Display`). Opacity policy preserved per Principle 15 (variant payload destructuring stays in source rustdoc). **Closes Group A.** |
| C-HOLE-1 | D | Mechanical /qa enhancement — add `pub use` set assertion in compliance test. |
| C-HOLE-2 | D | Mechanical /qa enhancement — per-critical-field PIF rows for D47-binding fields. |
| C-HOLE-3 | D | Audit's disposition is "No action — Wave 2 /qa orphan-filter refinement". |
| C-HOLE-4 | D | Mechanical source-side change to `string_newtype!` macro (drop `pub` on inner `String`). |
| C-HOLE-5 | A | In /dev concurrency-cluster brief (SPRINT.md row 53). |
| C-HOLE-6 | D | Mechanical source-side narrow `pub mod → pub(crate)` for submodules (low priority; schedule deferral acceptable). |

---

## 1. Hidden surface (facade names; source does not implement)

The eleven hidden-surface findings together constitute the SymbolTable encapsulation discipline + a small number of independent items. The disposition for the eleven cannot be evaluated independently of the concurrency complex (see Arbitration A1 retired below — there is no arbitration; the configuration grounds source moves).

### Finding H1 — RESOLVED (Submission 11 — walk row 342).

D48 cascade resolved structurally: `git mv crates/cranelisp-types/src/operator.rs → crates/cranelisp-primitives/src/operator.rs` (demoted to `pub(crate)`); `cranelisp-types/src/lib.rs` drops `pub mod operator;` + `pub use operator::{…}` re-export; `facades/types.md` §"Operator / primitive registry" deleted; `facades/primitives.md` §"Static-init contract" item 1 + §"Versioning policy" + §"Consumed surface" name the now-crate-private operator module as the constructor-input home. Source-side `ring{0,1,3}_primitives()` retirement tracked by FIXMEs 0182 + 0191 (D48 source-side completion).

---

### Finding H2 — RESOLVED (Submission 11 — walk row 343).

Source-side rename + signature flip applied: `crates/cranelisp-types/src/types.rs:63` renamed `io_inner_type → unwrap_io(&self) -> &Type`; tests `test_io_inner_type → test_unwrap_io` (lines 491–506) updated to compare against `&Type::Int` etc. 3 consumer cascade sites (`src/pipeline.rs:238`, `src/session_v4.rs:3793,4132`) tracked for /dev (int).

---

### Finding H3 — RESOLVED (Submission 11 — walk row 344).

H3+H4+H9+H10 bundle resolved with user-arbitrated D39 reconciliation: `defn_order: Vec<Symbol>` retired in favour of per-entry `seq: u64` (eliminates side-table drift). `SymbolTable.next_seq: AtomicU64` + `ModuleEntry::Def.seq: u64` land in `facades/types.md` §"Symbol table"; `StructuralDecls` stays 4-field (imports/exports/platforms/submodules); new `StructuralDeclEntry` enum + `append_structural_decl(&mut self, StructuralDeclEntry)` method added for REPL append. Source-side write_structural_decls method-add folds into the in-sprint concurrency-cluster /dev brief.

---

### Finding H4 — RESOLVED (Submission 11 — walk row 344).

Bundled with H3 closure — `defn_order` retired structurally; `append_defn_order` superseded by `append_structural_decl(StructuralDeclEntry)` for REPL-append of structural items (imports/exports/platforms/submodules) and by `next_seq.fetch_add(1)` for per-defn `seq` allocation at defn registration.

---

### Finding H5 — RESOLVED (in /dev concurrency-cluster brief).

Source-side `install_import_bindings(&self, from: &ModuleFullPath, names: &ImportNames)` method-add scheduled in SPRINT.md row 53 (Category A — SymbolTable concurrency cluster). Receiver `&self` per the concurrency-complex grounding (Decisions 31/32/41/44 + sequence diagram). Schedule promoted to in-sprint S69 per user direction 2026-05-20.

---

### Finding H6 — RESOLVED (Submission 11 — walk row 345 + concurrency-cluster brief).

D31 retracted (substance fully amended-into D41); facade verification sweep landed across `facades/{types,backend}.md`, `bounded-contexts.md`, sequence diagrams. Source-side `write_code(&self, …)` method-add scheduled in SPRINT.md row 53 (Category A) per Decision 41 + canonical `concurrency-symbol-table-entry.mmd` sequence diagram.

---

### Finding H7 — RESOLVED (in /dev concurrency-cluster brief).

Source-side `insert_or_update(&self, sym: Symbol, entry: ModuleEntry<C>)` method-add with carry-forward semantics (code + seq) scheduled in SPRINT.md row 53 (Category A). Receiver `&self` per Decision 32 Clone super-bound rationale + canonical sequence diagram lines 60–64. Migration at the `current_symbol_table_mut` accessor layer (Decision 44).

---

### Finding H8 — RESOLVED (Submission 11 — walk row 346 + concurrency-cluster brief).

Facade editorial fix landed at `facades/types.md` line 470 — return type flipped from phantom `Option<&TypeDef>` → `Option<Ref<'_, Symbol, ModuleEntry<C>>>` (mirrors `get()` return shape; `TypeDefInfo` stays inside `ModuleEntry::TypeDef` variant payload). Source-side `get_type` method-add folds into in-sprint SymbolTable concurrency cluster (SPRINT.md row 53); body is `self.symbols.get(name.as_ref()).filter(|e| matches!(**e, ModuleEntry::TypeDef { .. }))`.

---

### Finding H9 — RESOLVED (Submission 11 — walk row 344).

Bundled with H3 closure. `defn_order(&self) -> &[Symbol]` accessor retired structurally; source-regeneration consults per-entry `seq: u64` ordering via DashMap iteration + sort (or equivalent — `repl/spec.md` §15.4 names the consumer pattern).

---

### Finding H10 — RESOLVED (Submission 11 — walk row 344).

Bundled with H3 closure. `StructuralDecls { imports, exports, platforms, submodules }` stays 4-field (no `defn_order` — replaced by per-entry `seq`). Source-side struct + `write_structural_decls(&mut self, StructuralDecls)` + new `StructuralDeclEntry` enum + `append_structural_decl(&mut self, StructuralDeclEntry)` method scheduled in concurrency-cluster /dev brief.

---

### Finding H11 — RESOLVED (Submission 11 — walk rows 347+348+349+350).

Resolved via spec authoring + facade lockdown: `/spec` authored §8.3 EBNF extensions + new §8.3.10 (Accessibility After Import) 4-row matrix + §8.4 export-side symmetry + module-mounting + renaming forms. Facade locks `ImportNames` to 5 variants {Specific, Glob, MemberGlob, AliasOnly, Null}; `NamedImport { name, span, rename: Option<Symbol> }` carries both bare/dotted/rename; `ExportSpec` gains `alias: Option<ModuleName>` for symmetry; `NamedExport` retired (NamedImport used both sides). Source-side migration in /dev concurrency-cluster brief (SPRINT.md row 53 — concurrency cluster).

---

## 2. Unannounced surface (source declares; facade silent)

### Finding U1 — RESOLVED (Submission 11 — walk row 341).

Resolved structurally by Decision 0049 (Constructors-as-Defs + `Expr::ConstrADT` AST node): `ModuleEntry::Constructor` retired; `DefKind::Constructor` is the manifestation site (constructor metadata + scheme live inside `ModuleEntry::Def { kind: DefKind::Constructor }`). Cascade landed across `crates/cranelisp-types/src/{ast,module,check,heap,lib}.rs` + `facades/{types,backend,typecheck,frontend}.md`. ~34 ModuleEntry::Constructor pattern-match sites queued for /dev cascade.

---

### Finding U3 — `ModuleEntry::Ambiguous`

**Triage bucket: D — mechanical.** Audit's "No action — already aligned" disposition holds.

**Facade expects.** §"Item-by-item disposition" §"Enum variants" already names `ModuleEntry::Ambiguous` ("Sentinel for the bare-name-resolves-to-multiple-imports case").

**Source does.** Matches. `module.rs:760-768`.

**Design intent.** Already aligned. No drift. The `visibility: Visibility` field is informational stub for variant uniformity (every other ModuleEntry variant has visibility; `is_public` at module.rs:827 matches uniformly across all variants including Ambiguous, returning `*visibility == Visibility::Public`). The variant is load-bearing as a sentinel for the bare-name-clash case in Ring 2 — created by frontend/resolver when bare-name imports clash; consumed by name-resolution + REPL display. Sub 36's ModuleEntry settlement correctly retained it.

**Disposition.** **No action (S69 Sub 40 confirms audit call).** Documentation parity exists at `facades/types.md` §"Item-by-item disposition" §"Enum variants". `visibility: Visibility` field is informational stub for variant uniformity — `is_public` (module.rs:827) matches uniformly across all ModuleEntry variants including Ambiguous. Sub 36's ModuleEntry settlement correctly retained the variant + field. No structural question opened; variant uniformity is the right pattern for the sentinel-marker case (created by frontend/resolver on bare-name clash; consumed by name-resolution + REPL display).

---

### Finding U4 — RESOLVED (Submission 13)

Closed by Submission 13 (`ModuleEntry::Macro` sibling-variant retirement + macro unification). The `sexp` + `source` fields now live inside `DefKind::Macro { clauses_meta, sexp, source }` — see `facades/types.md` §"DefKind" `DefKind::Macro` for the unified shape and dispatch story. The §"Symbol table" `ModuleEntry::Macro` variant is removed; `DefKind::Macro` is the manifestation site for both the facade-text + the source-side migration tracked in the concurrency-cluster /dev brief. Bundled with S-DRIFT-5.

---

### Finding U5 — RESOLVED (Submission 14)

Closed by Submission 14 (field-level → method-level reframing on state types). Investigation found `param_names: Vec<Symbol>` has exactly two read sites — `arity_in_module` (backend) and zero-arg `test-*` discovery (`session_v4.rs`) — both of which read `.len()` / `.is_empty()` only; no site indexes into the Vec for names. The data IS arity, masquerading as a name list; `scheme.ty` (when `Type::Fn(params, _)`) already carries it.

**Disposition (revised).** Method-level accessor lands at the data owner: `Type::fn_arity(&self) -> Option<usize>` on `Type`; `ModuleEntry::arity(&self) -> Option<usize>` on `ModuleEntry` (delegating to `scheme.ty.fn_arity()` for `Def` variants; `None` for non-Def + multi-legged-parent + declarative kinds). `param_names` is private storage, slated for deletion in the in-sprint `/dev` concurrency-cluster wave-3 brief after the two consumer migrations land. The original "facade moves — add `param_names` to the variant summary" disposition is retracted; the field is implementation detail, not a consumer contract.

Manifestation: `facades/types.md` §"Type" (`Type::fn_arity` accessor); §"Symbol table — the single store" (`ModuleEntry::arity` impl block + storage-detail note adjacent to the `Def` variant); §"Bounded-context invariants" #11 (field-level access discouraged on state types). See also the calibration note at the head of this file (§0 below) for the framing this reframing established for the rest of the audit.

---

### Finding U6 — `Pattern::Constructor.bindings: Vec<Symbol>`

**Finding U6 — RESOLVED.** Pattern enum shape lands in `facades/types.md` §"AST" matching spec §6.2 (3 variants). Spec §6.6 exclusion note inline.

---

### Finding U7 — `Expr::Var` and `Expr::Let`

**Finding U7 — RESOLVED.** Expr enum consolidated into `facades/types.md` §"AST" — 14 variants enumerated with spec cross-references. Duplicating disposition table row deleted. The audit's "add Var/Let to table" frame was superseded by single-source-of-truth consolidation.

---

### Finding U8 — RESOLVED (Submission 18)

`EnsureOutcome` enumerated as canonical pub enum block in `facades/types.md` §"Symbol table — the single store" §"Module lifecycle primitives" (alongside `ensure_module_exists` / `install_module` signatures). Disposition-table prose simplified to bundling-narrative only.

---

### Finding U9 — RESOLVED (stale)

Audit's framing predated Submission 9's spec-§8.3 extension + facade alignment. `ImportNames` is 5-variant per spec §8.3.2 / §8.3.3 / §8.3.5 / §8.3.6 / §8.3.7 with `NamedImport` carrying optional rename; canonical at `facades/types.md` lines 1144-1158 area. MemberGlob is spec-authorized (§8.3.3), not pending arbitration. None/AliasOnly are distinct (§8.3.6 vs §8.3.7), not equivalent. Source migration is in the /dev wave-3 concurrency-cluster brief.

---

### Finding U10 — RESOLVED (Submission 11 — walk row 348 + module-alias submissions).

Resolved structurally via `U10 + alias-symmetry` submission: `ImportSpec` and `ExportSpec` made structurally identical (both carry `module_path` + `alias: Option<ModuleName>` + `names` + `span`); spec §8.4 made symmetric with §8.3 (full mount + rename + module-mounting on export). Source-side `ExportSpec.alias` field-add + chain-follow + conflict checks fold into in-sprint concurrency-cluster /dev brief.

---

### Finding U11 — RESOLVED (Submission 11 — walk rows 347+348).

Bundled with H11 + U10 closures. Per walk row 348 facade lockdown, `ExportSpec` and `ImportSpec` are structurally identical (both use the same `NamedImport`-typed name list); `NamedExport` retired. Source-side migration in concurrency-cluster /dev brief.

---

### Finding U12 — RESOLVED (Submission 33) — `SymbolTable.linker: Option<L>` field

**Closure.** Facade §"Symbol table" shape summary updated: `linker: Option<L>` field added alongside `dll: Option<D>` with full rustdoc citing **Decision 35** (`Code` enum location): `L = ()` integration-side because per-symbol `Code::Linker.linker: Arc<Linker>` retention covers every current case; `L` is **reserved per Decision 35** for future scenarios where a Linker must outlive its construction without any `Code::Linker` referencing it — reactivating the slot then would not require further generics churn. `#[serde(skip)]` discipline preserved (runtime state, cache-hit re-derives by re-loading the `.o`). Parallel-lifecycle-owner narrative with `dll: Option<D>` documented on both fields. The `dll` field's pre-S33 docstring referring to "linker's docstring lives on `SymbolTable<C, L>`'s pre-existing `LinkerStore` field" tightened to "Parallel to `linker: Option<L>` above (per Decision 35)" — the docstring now lives ON the field, not elsewhere. **Source side**: already at target shape — `linker: Option<L>` field exists at `crates/cranelisp-types/src/module.rs:229` with `#[serde(skip)]` and full rustdoc citing Decisions 32 + 35 since the field was added in Sprint 58. **No source migration owed.** Closes U12.

---

### Finding U13 — RESOLVED (Submission 33) — `SymbolTable::new_with_params` constructor

**Closure.** Facade §"Symbol table" `impl<C: CodeStore, L: LinkerStore, D: DllStore>` block updated: `pub fn new_with_params(path: ModuleFullPath) -> Self` added at the head of the block with inline rustdoc citing **Decision 35** instantiation pattern + the Rust-default-type-param-inference rationale ("default type parameter inference does not propagate to associated function calls; integration-layer call sites like `SymbolTable::<Code, ()>::new_with_params(path)` need the generic form even when `SymbolTable::new(path) -> SymbolTable<(), (), ()>` exists for the default-pinned case"). Both constructors produce identical structural state (empty maps, fresh GOT, `code: None` / `linker: None` / `dll: None`); they differ only in the type parameters Rust infers — clarified inline. **Source side**: already at target shape — `pub fn new_with_params(path)` exists on the generic `impl<C: CodeStore, L: LinkerStore>` block at `crates/cranelisp-types/src/module.rs:368` since Sprint 58 Wave 3b. **No source migration owed.** Closes U13.

---

### Finding U14 — RESOLVED (Submission 33) — `SymbolTable::into_concrete` + `ModuleEntry::into_concrete`

**Closure.** Facade `into_concrete` enumerated on both shape summaries:

- §"Symbol table" `impl SymbolTable` block (the concrete `<(), (), ()>` instantiation): `pub fn into_concrete<C2: CodeStore, L2: LinkerStore, D2: DllStore>(self) -> SymbolTable<C2, L2, D2>` with inline rustdoc citing **Decision 35** cache-restore role ("cache deserialises a `<(), (), ()>`-flavoured table because `code` / `linker` / `dll` are all `#[serde(skip)]`, the serialised form is parameter-independent; the integration layer installs it as a `<Code, (), ()>`-flavoured table for its session via `into_concrete`; mechanically copies fields, threading the new type parameters through — every entry's `code: Option<()>` becomes `None::<C2>` and `linker` / `dll` likewise; field-by-field, no work beyond type-parameter conversion").
- §"Symbol table" new `impl ModuleEntry<()>` block: `pub fn into_concrete<C: CodeStore>(self) -> ModuleEntry<C>` with rustdoc citing Decision 35 + the per-variant mechanical-copy contract ("`code: None::<C>` on the `Def` variant — the only field that depends on `C`; all other variants are parameter-independent and carry over as-is; called by `SymbolTable<(), (), ()>::into_concrete` during cache-restore").

**Source side**: both `into_concrete` methods already exist at target shape — `SymbolTable<(), ()>::into_concrete` at `crates/cranelisp-types/src/module.rs:288` (signature `<C: CodeStore, L: LinkerStore>` — facade documents the target `<C, L, D>` shape including the `D` parameter per the post-D-introduction target); `ModuleEntry<()>::into_concrete` at `module.rs:314`. The source signatures lack the `D2` parameter on `SymbolTable::into_concrete` because the source-side `D: DllStore` rollout is in-flight (per the `dll: Option<D>` field cascade); the facade names the post-cascade target shape. **No source migration owed for the U14 surface itself**; the `D2` parameter trails the broader `D` rollout. Closes U14.

---

### Finding U15 — RESOLVED (Submission 33) — `GotTable::default()` and `GotTable::new()` (no capacity arg)

**Closure.** Facade §"GOT" updated:

- `pub fn new(capacity: usize) -> Self` → `pub fn new() -> Self` (no capacity parameter).
- `pub fn default() -> Self` added (structurally equivalent; `Default` derive on the source side per `crates/cranelisp-types/src/got.rs` — observable in `public-api.txt` line 683).
- Struct-shape summary updated: `slots: Vec<AtomicPtr<()>>` → `slots: Box<[AtomicPtr<u8>; GOT_TABLE_SIZE]>` (matches source `got.rs:27`).
- `pub const GOT_TABLE_SIZE: usize` line annotated: "1024 slots — see `crates/cranelisp-types/src/pipeline.rs:39`" (the constant's canonical home).
- New paragraph below the code block: **"Capacity is fixed at compile time per the `GOT_TABLE_SIZE` constant (1024 slots; canonical home at `crates/cranelisp-types/src/pipeline.rs:39`; surfaced in §"Constants"). Decisions 23 (two-GOT model) and 48 (primitives static GOT in `cranelisp-primitives`) both specify fixed-capacity GOTs as a structural choice — avoids dynamic-sizing semantics + the AtomicPtr-vector growth question (a growing `Vec<AtomicPtr<_>>` would invalidate `base_ptr()` on resize, breaking JIT-generated code that holds the base pointer as a compile-time relocation). No Decision authorises a configurable surface; the constructor takes no capacity argument."**

**Source side**: already at target shape — `pub fn new() -> Self` at `got.rs:38` (no args); `Default` derive present (observable at public-api line 682); `GOT_TABLE_SIZE = 1024` at `pipeline.rs:39`. **No source migration owed.** The pre-S33 facade `(capacity: usize)` parameter was sloppy facade authoring with no Decision grounding (confirmed by the audit's design-intent block — Decisions 23 + 48 both name fixed-capacity); the disposition is firmly facade-moves. Closes U15.

---

### Finding U16 — `ErrorLocation::{from_span, from_span_file, unknown}`

**Triage bucket: D — mechanical.** Facade-side enumeration: name the three constructors in §"Errors and warnings" with one-line guidance per Decisions 39 + 42.

**Facade expects.** Not enumerated.

**Source does.** Three `pub` constructors per pub-api.

**Design intent.** **Decision 39** (per-defn source coordinates) + **Decision 42** (`PlatformError` adopts `ErrorLocation`) ground the `ErrorLocation` carrier shape. The three constructors discriminate the producer-side context: parser has file in hand → `from_span_file`; typecheck has only span → `from_span`; runtime error from synthetic source → `unknown`. The constructors are load-bearing for the consumer-side dispatch in the int formatter (per facade lines 757–823). Facade enumeration gap is documentation only.

**Difference implies.** Consumer call sites need to know which constructor to use for which case. Facade silence leaves the choice opaque.

**Disposition.** **RESOLVED by facade enumeration (S69 Sub 39).** Three constructors enumerated in `facades/types.md` §"Errors and warnings" with producer-side guidance per `unknown` / `from_span` / `from_span_file` cases. Trace results recorded: ~357 total constructor calls; `from_span` is the workhorse (typecheck/codegen); `from_span_file(span, None)` heavily used in frontend (structurally equivalent to `from_span(span)`); `from_span_file(span, Some(path))` legitimately used by int's session/worker at dependency/load construction; `unknown` correctly used at cranelisp-platform sites. Dead fields `fq`, `line_col`, `context` retained as forward-looking suggestive surface per user framing — pedagogical for future producers per the parallel to Sub 37's `SchedulingClass::Default` retention. Cleanup deferred until proven unfillable.

---

### Finding U17 — `LineCol::new(line, col)` + `LineColRange::new(start, end)`

**Triage bucket: D — mechanical.** Bundled with U16; same facade-side enumeration.

**Disposition.** **RESOLVED by facade enumeration (S69 Sub 39).** `LineCol::new` and `LineColRange::new` enumerated in `facades/types.md` §"Errors and warnings". Trace results recorded: zero call sites outside the type definitions; types exist as the typed shape of `ErrorLocation.line_col: Option<LineColRange>` (the forward-looking field retained under U16). Bundled with U16's suggestive-surface logic.

---

### Finding U18 — `SchedulingClass::default()`

**Triage bucket: D — mechanical.** Audit's "No action — auto-derive Default::default() = Sequential" disposition holds.

**Facade expects.** §"Scheduling" describes the enum; no `default()` method.

**Source does.** Derived `Default` impl.

**Design intent.** Per facade `SchedulingClass.from_u32(v) -> Self` (line 749), the `Sequential = 0` variant is the canonical default for cross-DLL ABI-version drift. `Default::default() = Sequential` is the same value. **No Decision arbitrates the auto-derive.** Per audit discipline this still gets a one-sentence rationale.

**Disposition.** RESOLVED by docstring expansion (S69 Sub 37). Original audit reading was correct that `Default::default()` is auto-derived noise with no production callers (consumer trace: only the in-crate self-test). Walk-through reframing surfaced the real finding: the *docstring* was the problem, not the trait impl. Pre-walk docstring explained what SchedulingClass controlled but not how to pick a variant. Replaced with a decision guide (Sequential = conservative default; Commutative = independent; ResourceSerial = per-token). `Default` derive retained as a small courtesy for forward-compat (future builders / serde-defaulted fields); pedagogy now carried by the docstring where authors actually encounter it. No facade or public-API change.

---

### Finding U19 — `PlatformError::location()` accessor

**Triage bucket: D — mechanical.** Facade-side enumeration: add `pub fn location(&self) -> Option<&ErrorLocation>` to `PlatformError` per Decision 42 + symmetry with `CranelispError::location()`.

**Facade expects.** Per Decision 42, `PlatformError` carries `ErrorLocation` per variant; the `int` formatter consumes via `CranelispError::Platform(PlatformError)`. No `location()` accessor named.

**Source does.** `pub fn location()` accessor per pub-api.

**Design intent.** **Decision 42** (`PlatformError` adopts `ErrorLocation`) names the `ErrorLocation` carry-discipline; the symmetric `location()` accessor matches `CranelispError::location()` (named at facade line 822) per Principle 7 (uniform consumer surface). The accessor is grounded by Decision 42 + the facade's existing `CranelispError::location()` shape.

**Disposition.** **RESOLVED by facade enumeration (S69 Sub 39).** `PlatformError::location(&self) -> &ErrorLocation` enumerated in `facades/types.md` §"Errors and warnings". Returns `&ErrorLocation` (no `Option`) — every variant carries location per Decision 42's variant shape. Public for cross-crate use: `cranelisp-platform/src/lib.rs:614` returns `Result<_, PlatformError>` directly; external consumers need the accessor for display before wrapping into `CranelispError`. Principle 7 symmetric with `CranelispError::location` after Sub 39's U20 narrowing.

---

### Finding U20 — `CranelispError::{message, span}` accessors

**Triage bucket: D — mechanical.** Facade-side enumeration of formatter-convenience accessors.

**Facade expects.** §"Errors and warnings" names `location()` only.

**Source does.** `pub fn message`, `pub fn span` additional accessors per pub-api.

**Design intent.** Formatter convenience accessors per the int-side consumer pattern (per `facades/int.md`); accessing fields without per-variant pattern-matching. Editorial enumeration gap; no Decision-level question.

**Disposition.** **RESOLVED by facade enumeration + structural narrowing (S69 Sub 39).** Three accessors (`message`, `span`, `location`) enumerated in `facades/types.md` §"Errors and warnings". Scope-extended structural narrowing: `CranelispError::location()` signature narrowed from `Option<&ErrorLocation> → &ErrorLocation`. User-arbitrated rationale: every `CranelispError` variant carries an `ErrorLocation` per the type's invariant established by Decisions 39 + 42; the `Option` hid the structural invariant and created Principle 7 asymmetry with `PlatformError::location()`. Consumer trace: only one `CranelispError` consumer site at `src/main.rs:91` (`let Some(loc) = err.location() else { ... }`) where the else-branch is dead (impl returned `Some` on every arm). Wave-3 cascade simplifies `main.rs:91` to `let loc = err.location();` and removes the dead else-branch fallback. Parallel to Sub 35's `Option<Defn> → Option<DefnVariant>` narrowing — edge-walk corrects vestigial `Optionality` based on what the variants actually carry. Aligns with Principle 7 (single source of truth — accessor surface matches invariant) + Principle 18 (enforce invariants structurally where possible).

---

### Finding U21 — `CranelispError::From<PlatformError>` impl

**Triage bucket: D — mechanical.** Audit's "No action — auto-trait noise per Decision 42 variant" disposition holds.

**Design intent.** Decision 42's `CranelispError::Platform(PlatformError)` variant implies the `From` impl by Rust idiom (`?` operator from `Result<…, PlatformError>` to `Result<…, CranelispError>`). Auto-trait surface; no Decision-level question.

**Disposition.** **RESOLVED by facade enumeration (S69 Sub 39) — audit's 'No action' disposition overridden.** `impl From<PlatformError> for CranelispError` enumerated in `facades/types.md` §"Errors and warnings" with one-line note grounding it in Decision 42's `Platform(PlatformError)` variant shape. Override rationale: per the S67 baseline-diff discipline at `design/arch/CLAUDE.md`, every pub-api line in the baseline is named in the corresponding facade; the `From` impl is in `public-api.txt` regardless of auto-trait-feel. Conservative coverage move.

---

### Finding U22 — `HeapCategory::classify<C, L>(ty, Option<&DashMap<…>>)`

**Triage bucket: D — mechanical (RESOLVED — reclassified).** Originally "facade-side enumeration: add the full `classify` signature to §"Heap layout"". Consumer trace in Submission 38 surfaced this was a bounded-context violation, not a documentation gap.

**Facade expects.** §"Heap layout" describes `HeapCategory { NeverHeap | AlwaysHeap | Mixed }`. No `classify` function.

**Source does.** `heap.rs:55–78`: classification function consulting symbol tables for ADT ctor layout.

**Design intent.** No Decision specifically authors `classify`'s signature, but its two-mode behaviour (with/without tables → conservative `Mixed` vs exact) is grounded by **Principle 6** (complexity has a budget — conservative default) + the backend consumer pattern (RC discipline). Source is the producer-of-record; facade silence is a documentation gap. Note `Option<&DashMap<…>>` confirms the **DashMap target shape** of the symbol tables — corroborating evidence for the SymbolTable concurrency complex (the classify signature is consistent with the facade's DashMap target state, not source's HashMap as-built).

**Disposition.** **RESOLVED by relocation (S69 Sub 38).** Original "D — mechanical, facade moves" disposition was scope-incorrect: the finding wasn't a documentation gap, it was a bounded-context violation that the audit's mechanical bucket couldn't see. Consumer trace surfaced that `HeapCategory` has zero production consumers outside `cranelisp-backend` (single non-backend reference is a documentation comment at `cranelisp-types/src/check.rs:153`). The type is backend-internal codegen classification, not a cross-crate substrate. Relocation: enum + `classify` + `classify_adt` + `classify_from_type_def_info` + gated-out test module move from `crates/cranelisp-types/src/heap.rs` to `crates/cranelisp-backend/src/heap.rs`. `HeapHeader` + offset constants + compile-time assertions retain in cranelisp-types as the genuine cross-crate layout contract shared with cranelisp-runtime. Re-export `pub use heap::{HeapCategory, HeapHeader}` shrinks to `pub use heap::HeapHeader`. The U22 facade-text addition the audit proposed never lands in `facades/types.md` — the section migrates to `facades/backend.md` §"Heap classification". Aligns with Principle 3 (cranelisp-types depends on nothing — narrower BC) + Principle 7 (single source of truth — codegen concern in codegen crate) + Decision 48 §"Structural invariant — backend dep-ban" (relocation preserves the invariant: classifier walks `SymbolTables` abstraction, never crate-deps cranelisp-primitives). Pending structural cascades (ctor-as-Def rebuild; Type-variant unification; two-mode contract retirement) named in `facades/backend.md` §"Heap classification".

---

## 3. Shape drift (facade and source both present; details diverge)

### Finding S-DRIFT-1 — RESOLVED (Submission 11 — walk rows 339+340).

(a) Source-side `vars → type_vars` rename approved at `crates/cranelisp-types/src/types.rs:135` (~109 sites across 8 files cascaded to /dev). (b) Facade `Vec<TraitName> → Vec<FQTraitName>` editorial fix applied at `facades/types.md:354` per Decision 47 FQ-binding mandate.

---

### Finding S-DRIFT-2 — RESOLVED (Submission 30 — closed by deletion)

**Triage bucket: D — RESOLVED Submission 30.** Closed by deletion + structural replacement, not facade-text catch-up.

**Closure summary.** `Type::from_name(&str) -> Option<Type>` deleted from `crates/cranelisp-types/src/types.rs` (lines ~33–41 retired). The in-file test `test_from_name` (lines ~373–379) deleted alongside.

**Why deletion is the correct disposition (scope-correction vs. prior framing).** The audit's "facade moves to source's `&str`" disposition was superseded by today's /spec fire (S69 — FIXME 0216 + spec §3.1 / §8.9.1 / §8.11.4 sharpening). User-confirmed reading: bare `:Int` requires either prelude re-export or explicit `(import [primitives [Int]])`. Fully-qualified `:primitives/Int` always works. **Without prelude / explicit import, bare `:Int` is a compile-time "unknown type" error**. The `Type::from_name` helper made bare `:Int` always available regardless of imports — a spec violation. The bridge was not just facade-misaligned (the prior framing); it was structurally wrong for the spec semantics.

**Structural replacement.** New `ModuleEntry::IntrinsicType { ty: Type, visibility: Visibility }` variant added to `ModuleEntry` in `crates/cranelisp-types/src/module.rs` (positioned after `TypeDef`, before `TraitDecl`). Compiler-intrinsic scalar types (Int, Bool, Float, String) register into the `primitives` module's SymbolTable like any other entry; resolution returns `ty.clone()` directly without FQTypeName special-casing. Wave-3 cascade lands `cranelisp-typecheck::register_primitives` extension + `resolve_named` simplification + 6 `Type::from_name` call-site fixups in `traits.rs` (+ the one in `resolve.rs`).

**Grounding.**
- Spec §3.1 + §8.9.1 + §8.11.4 (S69 /spec fire sharpening) — bare-name access requires prelude or explicit import.
- FIXME 0216 — primitive-type-import-conformance, filed today.
- `memory/feedback_facade_walk_no_interior.md` — within-crate match-arm additions (`is_public`, `into_concrete`) in scope for the walk; cross-crate consumer cascade deferred to wave-3.

**Manifestation pointers.**
- Source: `crates/cranelisp-types/src/types.rs` (deletion); `crates/cranelisp-types/src/module.rs` (new variant + match-arm additions in `is_public` + `into_concrete`).
- Facade: `design/arch/facades/types.md` §"Resolved type system" `impl Type` block (deletion + replacement comment); §"Symbol table" `ModuleEntry::IntrinsicType` variant block; §"Resolved type system" Decision 47 exception-1 retirement callout; §"Item-by-item disposition" §"Enum variants" `ModuleEntry::IntrinsicType` row.
- Audit: this closure block + triage register row.

**Discipline footer.** Walk-through fire per `memory/feedback_facade_walk_no_interior.md` — facade + within-crate source aligned; cross-crate consumer cascade (6 call sites in typecheck) deferred to /dev wave-3. No workspace `cargo check`. No `public-api.txt` baseline regen. No consumer crate edits.

---

### Finding S-DRIFT-3 — RESOLVED (Submission 30 — closed by deletion)

**Triage bucket: D — RESOLVED Submission 30.** Closed by deletion + structural replacement (bundled with S-DRIFT-2).

**Closure summary.** `Type::type_name(&self) -> Option<&'static str>` deleted from `crates/cranelisp-types/src/types.rs` (lines ~44–52 retired). The in-file test `test_type_name` (lines ~381–385) deleted alongside.

**Why deletion is the correct disposition (scope-correction vs. prior framing).** Same as S-DRIFT-2 — the audit's "facade catch-up" framing was superseded. `Type::type_name` is the inverse of `from_name`; both formed the reverse-lookup bridge that made bare `:Int` always available regardless of imports. The bridge was spec-violating per the S69 /spec fire (FIXME 0216 + spec §3.1 / §8.9.1 / §8.11.4 sharpening), not just facade-misaligned.

**Structural replacement.** Same as S-DRIFT-2 — `ModuleEntry::IntrinsicType` variant carries the bare `Type` for backend codegen efficiency; the fully-qualified form lives in the SymbolTable key. Reverse-lookup (Type → display name) is no longer needed as a `Type`-method bridge: display naming flows through `Type::Display` (already in source) using either the bare-variant rendering (`Type::Int` → "Int") or the FQ ADT rendering (`Type::ADT(fqtn, args)` → `fqtn` formatting). Backend's primitive-codegen consults the per-module SymbolTable entry — same lookup path as any other identifier.

**Grounding.** Same as S-DRIFT-2.

**Manifestation pointers.** Same as S-DRIFT-2 (resolved as a single submission, bundled in source/facade/audit edits).

**Discipline footer.** Same as S-DRIFT-2.

---

### Finding S-DRIFT-4 — RESOLVED (Submission 11 — walk row 347).

Bundled with H11 closure. `ImportNames` locked to 5 spec-grounded variants {Specific, Glob, MemberGlob, AliasOnly, Null} (per spec §8.3.1–§8.3.6); `ExportSpec.names` decoupled from import enum and made structurally symmetric. Source-side migration in concurrency-cluster /dev brief.

---

### Finding S-DRIFT-5 — RESOLVED (Submission 13)

Closed by Submission 13 (`ModuleEntry::Macro` sibling-variant retirement + macro unification under `DefKind::Macro`). The arbitration A2 question — "can multi-clause macro dispatch live behind a single GOT slot per macro?" — was answered structurally: not through one slot at the parent entry, but through **N GOT slots one-per-clause-body** under mangled names `{macro-name}$clause-{N}`, parallel to multi-sig fn variants (`add$Int+Int`). The parent `Def { kind: Macro { clauses_meta, sexp, source } }` is metadata-only (`got_slot` unused, `code: None`); each clause body is its own `Def { kind: UserFn, got_slot, code: Some(_), … }`. `MacroEnv` retires; clause-body lookup is the same GOT-dispatch path as any other callable.

See `facades/types.md` §"DefKind" `DefKind::Macro` for the full shape, dispatch story, and three rejected alternatives (sibling-variant kept, entry-level trampoline, sexp/source at Def level). Source-side retirement of the `ModuleEntry::Macro` sibling variant tracked in the concurrency-cluster /dev brief (sprints/SPRINT.md).

---

### Finding S-DRIFT-6 — `ModuleEntry::Def.ast` type — **RESOLVED (Submission 35) — both move**

**Triage bucket: D — RESOLVED Submission 35.** Source narrowed (`Option<Defn>` → `Option<DefnVariant>`); facade catches up.

**Closure direction.** **Both move — scope-correction from prior "facade moves" framing.**

**Scope-correction vs. prior audit.** The prior audit framed this as "facade moves to source's `Option<Defn>`" on the rationale that "Decision 22's predicate + backend's consumer pattern require the wider `Defn` shape." On user-questioning, that framing missed a real smell: by the time a Def reaches backend, multi-sig has already been **decomposed into per-mangled-name Defs** (`add$Int+Int`, `add$Float+Float`), each carrying a synthesised single-variant `Defn`. The outer `Defn` wrapper at the Def level carries:

- `Defn.name` — duplicates the symbol-table key,
- `Defn.docstring` — duplicates the Def's own `docstring` field,
- `Defn.variants` — always `.len() == 1` post-decomposition (single-element `Vec` wrapping the meaningful payload),
- `Defn.visibility` — duplicates the Def's own `visibility` field,
- `Defn.span` — redundant with the variant's own `span`.

The meaningful payload IS the single `DefnVariant`. Carrying the full `Defn` wrapper is vestigial at this layer.

**Target shape (now source-canonical at `crates/cranelisp-types/src/module.rs:534`).**

```rust
ast: Option<DefnVariant>,
```

**Grounding (corrected vs prior audit).**

- **Decision 22** (legacy: `defined-symbols-shared-predicate.md`) preserved — the `is_some()` predicate is indifferent to the payload type. `ast.is_some() AND kind is UserFn/Constructor/etc.` reads identically against `Option<DefnVariant>`.
- **Minimum mechanism** (audit discipline #4) — `DefnVariant` is what consumers actually read post-decomposition; `Defn` carries duplicate fields at this layer.
- **Single source of truth (Principle 7)** — the Def's own `name`/`docstring`/`visibility`/`seq` fields are the single source; the outer `Defn` wrapper duplicates them.
- **`Defn` continues to exist as the frontend AST node** (parser output, pre-decomposition). Typecheck's multi-sig decomposition splits the frontend `Defn` → multiple `DefnVariant`s, each landing in its own `ModuleEntry::Def.ast`. The outer `Defn` wrapper retires from the runtime model.

**Internal within-crate consumer migration (Submission 35 scope).** Five within-crate test sites in `crates/cranelisp-types/src/module.rs` migrated:

- `mk_def` test-helper parameter `ast: Option<Defn>` → `Option<DefnVariant>`.
- New `trivial_variant(name) -> DefnVariant` helper alongside `trivial_defn(name) -> Defn` — the former feeds the narrowed `ast` field, the latter remains for `ConstrainedFn { defn: Defn, .. }` constructions (frontend AST node use).
- Seven `Some(trivial_defn(...))` call sites on `mk_def` / direct `ast:` struct-field initialisers rewritten to `Some(trivial_variant(...))`. The lone `defn: trivial_defn("template")` inside `ConstrainedFn` retained — `ConstrainedFn.defn: Defn` is unchanged (frontend AST node, not the post-decomposition payload).
- Doc-comment sweep in module.rs (lines 333–337, 655–660, 813–816): "synthesised `Defn` bodies" → "synthesised `DefnVariant` bodies" with S69 Submission 35 narrative pointer.

**Manifestation pointers.**

- Source: `crates/cranelisp-types/src/module.rs:534` — `ast: Option<DefnVariant>` field declaration + ~40-line rustdoc citing Decision 22 + minimum mechanism + Principle 7 + frontend-Defn-vs-runtime-DefnVariant decomposition narrative.
- Facade: `design/arch/facades/types.md` §"Symbol table — the single store" `ModuleEntry::Def` shape summary — `ast: Option<DefnVariant>` with inline note citing Decision 22 preserved-predicate + minimum mechanism + multi-sig decomposition reality + Principle 7 single-source-of-truth.
- Facade sibling sweep: line 1215 (`ModuleEntry::Constructor` retirement comment), line 1330 (`DefKind::Constructor` rustdoc), line 1569 (`ConstructorInfo.fields[i].span` migration comment), line 431 (`ParsedEntry::Constructor` rustdoc) — all updated to "synthesised `DefnVariant`" with Submission-35 narrative pointer.
- Audit: this closure block; triage register row 97 updated; per-finding RESOLVED marker.

**Wave-3 cascade (deferred to /dev).** ~30-50 consumer sites in backend + typecheck:

- Backend `lib.rs`, `compiler/mod.rs` (~10+ sites): `defn.params()` → `variant.params`; `defn.variants[0].body` → `variant.body`; `defn.variants[0].span` → `variant.span`; the post-decomposition `defn: Defn` collection pattern `defns.push(defn.clone())` becomes a `(Symbol, DefnVariant)` collection.
- Backend `cache/object.rs`, `cache/serialize.rs`, `cache/mod.rs` — cache reconstruction sites.
- Typecheck `traits.rs`, `program.rs`, `infer.rs`, `checker.rs` — synthesis sites: `ast: Some(synthesised_defn)` becomes `ast: Some(synthesised_variant)` (drop the outer `Defn` wrapper — synthesise the meaningful payload directly).

**Discipline calibration (vs. prior audit).** The prior audit's "facade moves" framing was correct *in direction* — facade did need to leave `Option<Expr>` — but missed the subsequent question: *narrow to what?* On user-questioning, "to source's `Option<Defn>`" was rejected as ratifying vestigial structure; the answer that survives configuration-grounding is `Option<DefnVariant>`. Audit discipline lesson: when a "facade moves" finding ratifies source, verify the source shape is itself configuration-grounded (minimum mechanism + single source of truth) — source-as-target is not automatic even when facade is editorial-stale.

**Closes S-DRIFT-6.**

---

### Finding S-DRIFT-7 — `ModuleEntry::Def.kind` boxing — **RESOLVED (Submission 35) — facade moves**

**Triage bucket: D — RESOLVED Submission 35.** Facade catch-up to source's `Box<DefKind>` per Principle 6 (size discipline; pattern-match through Box is transparent).

**Closure direction.** **Facade moves.** No source-side change owed — source already at `Box<DefKind>`.

**Target shape (source-canonical at `crates/cranelisp-types/src/module.rs:478`; facade-canonical post-Submission-35).**

```rust
kind: Box<DefKind>,
```

**Grounding.**

- **Principle 6** (complexity has a budget — size discipline). `DefKind` has heavy variants:
  - `Overloaded { variants: Vec<OverloadVariant> }` — multi-sig dispatch carries the full variant set.
  - `UserFn { constrained_fn: Option<Box<ConstrainedFn>> }` — constrained polymorphism payload.
  - `Macro { clauses_meta, sexp, source }` — multi-clause dispatch metadata.

  Boxing trims `ModuleEntry::Def`'s stack size; the heavy variant's payload lives on the heap addressed by the `Box` pointer.

- **Pattern-match through `Box` is transparent.** Consumers write `match *kind { DefKind::UserFn { .. } => … }` exactly as if `kind` were an inline `DefKind`. No consumer-side migration owed.

- **No Decision specifically authors the boxing.** Editorial implementation choice. The facade was sloppy in not catching up.

**Manifestation pointers.**

- Source: `crates/cranelisp-types/src/module.rs:478` — `kind: Box<DefKind>` field declaration (unchanged).
- Facade: `design/arch/facades/types.md` §"Symbol table — the single store" `ModuleEntry::Def` shape summary — `kind: Box<DefKind>` with inline note citing Principle 6 + transparent-pattern-match clarification.
- Audit: this closure block; triage register row 98 updated; per-finding RESOLVED marker.

**Wave-3 cascade.** None owed — pattern-match through `Box` is transparent; consumers already write through it.

**Closes S-DRIFT-7.**

---

### Finding S-DRIFT-8 — RESOLVED (Submission 31, 2026-05-23)

**Triage bucket: D — RESOLVED Submission 31.** Source-side promotion landed: type alias replaced with `#[non_exhaustive]` newtype struct per facade `#[non_exhaustive]` policy + Principles 8/13 + BC invariant 11.

**Target shape (now source-canonical at `crates/cranelisp-types/src/check.rs:7–43`).**

```rust
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[non_exhaustive]
pub struct MethodResolutions {
    pub resolved_calls: HashMap<Span, ResolvedCall>,
}

impl MethodResolutions {
    pub fn new() -> Self {
        Self::default()
    }
}
```

**Grounding (four authorities cited inline on the source rustdoc).**

- **Facade §"`#[non_exhaustive]` policy"** (binding): "every public struct and enum in `cranelisp-types` MUST be `#[non_exhaustive]`." Type aliases are exempt from the attribute in Rust (it cannot be applied to an alias), but the policy *intent* — extensibility, allow adding fields without breaking consumers — was violated by the alias: consumers saw `HashMap` directly and committed the surface to its shape.
- **Principle 8 (no interim implementations).** The alias was a stand-in that committed the public surface to `HashMap` forever. Promotion to a newtype struct lifts the interim into the target shape — admits future `pub` field additions (e.g., per-call-site context; instance-context for trait resolution — illustrative, not committed) without touching the public-api baseline.
- **Principle 13 (`interfaces.md` is auditable + `cargo-public-api`-gateable).** The newtype struct is the auditable surface; a type alias to a foreign generic (`HashMap<…>`) bypasses the `cargo-public-api` baseline gate (every change to `HashMap`'s API ripples through the alias). The struct shape pins the surface to a stable, baseline-checkable boundary.
- **BC invariant 11 (data-record DTO).** `MethodResolutions` is named explicitly in the BC invariant 11 enumeration as a DTO whose field set IS the contract; `serde` round-trips structurally. The promotion preserves this classification — `resolved_calls` is the public field.

**Scope-correction vs. prior framing.** The prior audit ("Consumers using `HashMap` methods continue via `Deref<Target=HashMap>` or via the `resolved_calls` field") considered a `Deref` impl as a possible migration aid. The landed shape does NOT add `Deref` — per Principle 8, the interim convenience would itself be a stand-in committing the surface again. Consumers migrate mechanically to `.resolved_calls.X` (the field access path), which is the durable shape.

**Manifestation sites.**
- Source: `crates/cranelisp-types/src/check.rs:7–43` (struct definition + rustdoc + `impl new()`).
- Facade: `facades/types.md` line ~1499 (already at target shape pre-S31; no edit needed) + new PIF row at §"Struct fields" naming `resolved_calls` as the data-record DTO field.
- Audit: this closure block; triage register row updated; per-finding RESOLVED marker.

**Wave-3 cascade (deferred to /dev per `feedback_facade_walk_no_interior.md`).** ~10 consumer migration sites in `crates/cranelisp-typecheck/src/checker.rs` + `infer.rs` rewrite `state.method_resolutions.X` (HashMap method calls — `.insert`, `.contains_key`, `.get`, `.clear`) to `state.method_resolutions.resolved_calls.X`. Construction sites (`HashMap::new()`) become `MethodResolutions::new()`. Mechanical; no semantic shift.

**Discipline footer.** Walk-through fire per `memory/feedback_facade_walk_no_interior.md` — facade + source aligned within `cranelisp-types`; cross-crate consumer cascade NOT performed; workspace `cargo check` NOT run (expected broken — ~10 cascade sites in typecheck); `public-api.txt` baseline regen deferred to end-of-walk; no consumer crate edits.

---

### Finding S-DRIFT-9 — RESOLVED (Submission 32, 2026-05-23)

**Triage bucket: D — RESOLVED Submission 32.** Facade self-reconciliation under Decision 47 (line 513 already correctly named the 4-field shape; line 512 misattribution + line 1792 PIF row stale text were the editorial drift) + source-side `#[non_exhaustive]` policy catch-up (scope-extended per user direction to avoid revisiting this data structure).

**Framing — neither "facade moves" nor "source moves" purely.** Pre-S32 facade had three places naming `ResolvedCall::TraitMethod`'s shape:

- Line 513 (§"Resolved type system"): `ResolvedCall::TraitMethod { trait_name: FQTraitName, … }` — **correct** under Decision 47 since the Decision authored.
- Line 512 (same paragraph): `MethodResolutions.impl_type` — **misattribution** (the field lives on `ResolvedCall::TraitMethod`, NOT on `MethodResolutions` which is the per-`Span` lookup map).
- Line 1792 (§"Item-by-item disposition" §"Enum variants"): three-field shape with misplaced `trait_resolution` — **stale text predating Decision 47's sharpening**.

The mixed-correctness was facade-internal inconsistency, not source-facade drift. Source has carried the post-D47 4-field shape since D47 authored. Resolution: facade self-reconciles (lines 512 + 1792 catch up to line 513's already-correct text); source picks up the `#[non_exhaustive]` policy add bundled in.

**Target shape (now facade-canonical at line 1792).**

```rust
ResolvedCall::TraitMethod {
    trait_name: FQTraitName,
    method_name: Symbol,
    impl_type: FQTypeName,
    mangled_name: JitSymbol,
}
```

`trait_resolution` lives on `ResolvedCall::AutoCurry` only (already correct at facade line 1832; line 1792 cross-reference now explicit). Backend reads `mangled_name: JitSymbol` to emit the call; reads `trait_name` + `impl_type` for resolution-context introspection (REPL displays, error messages).

**Target shape (now source-canonical at `crates/cranelisp-types/src/check.rs:46–73`).**

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ResolvedCall {
    TraitMethod { trait_name: FQTraitName, method_name: Symbol, impl_type: FQTypeName, mangled_name: JitSymbol },
    SigDispatch { mangled_name: JitSymbol },
    AutoCurry { target_name: Symbol, applied_count: usize, total_count: usize, trait_resolution: Option<Box<ResolvedCall>> },
    BuiltinFn { name: Symbol },
}
```

**Grounding (authorities cited inline).**

- **Decision 47 (FQTypeName binding at resolved-stage boundaries).** `MethodResolutions` is a typecheck-output type → resolved stage → exception-1/-2 don't apply → FQ binding applies. `trait_name: FQTraitName` + `impl_type: FQTypeName` on `TraitMethod` is the post-D47 target. Source has carried this since D47 authored; facade lines 512 + 1792 were the un-cascaded text.
- **Facade §"`#[non_exhaustive]` policy"** (binding): "every public struct and enum in `cranelisp-types` MUST be `#[non_exhaustive]`." `ResolvedCall` was the un-cascaded source-side gap; Submission 32 lands the attribute.
- **Principle 13 (`interfaces.md` is auditable + `cargo-public-api`-gateable).** The `#[non_exhaustive]` attribute is the structural enforcement of evolution discipline — future variant additions (e.g., platform-effect dispatch shapes, dictionary-passing trait carriers, speculative-inlining markers) land without touching the consumer-side baselines.
- **Facade internal consistency.** Lines 512 + 513 + 1792 + 1832 must agree. Pre-S32, lines 513 + 1832 were correct; lines 512 + 1792 were stale. S32 brings 512 + 1792 in line.

**Scope-extension vs. prior framing.** The audit's original disposition named only the facade-side correction (PIF row rewrite + line-512 misattribution fix). Submission 32 scope-extends to bundle the source-side `#[non_exhaustive]` add per user direction: "S-DRIFT-9 + ResolvedCall `#[non_exhaustive]` — bundled here to avoid revisiting this data structure." The bundling is scope-extension, not a redirected disposition — the facade-side correction remains the structural payload; the source attribute add is the policy-catch-up bonus.

**Manifestation sites.**

- Source: `crates/cranelisp-types/src/check.rs` lines 44–66 (enum + 14-line rustdoc citing `#[non_exhaustive]` policy + Principle 13 + D47 reference; `#[non_exhaustive]` attribute on line 67; 4-field `TraitMethod` variant intact at lines 70–75).
- Facade: `design/arch/facades/types.md` line 512 (misattribution corrected to `ResolvedCall::TraitMethod.impl_type`); line 1792 (PIF row rewritten with 4-field `TraitMethod` + D47 citation + AutoCurry-only `trait_resolution` clarification). Line 1500 opaque summary unchanged (already at `TraitMethod { /* … */ }` placeholder shape — variant fields documented at the §"Item-by-item disposition" expansion).
- Audit: this closure block; triage register row updated; per-finding RESOLVED marker.

**Cross-reference.** Submission 31's closure flagged the line-512 misattribution as a follow-up; that follow-up lands here.

**Wave-3 cascade (deferred to /dev per `feedback_facade_walk_no_interior.md`).** ~5-10 pattern-match sites on `ResolvedCall` outside `cranelisp-types` (typecheck consumers in `cranelisp-typecheck/src/{checker,infer,traits}.rs`; backend consumers in `cranelisp-backend/src/{compiler,primitives_inline}.rs`) need `_ =>` arms added to handle the now-non-exhaustive enum. Mechanical; no semantic shift. Within-crate consumers verified zero — no `match` on `ResolvedCall` exists inside `crates/cranelisp-types/src/` (grep-confirmed; `#[non_exhaustive]` only affects cross-crate match exhaustivity per Rust semantics).

**Discipline footer.** Walk-through fire per `memory/feedback_facade_walk_no_interior.md` — facade + source aligned within `cranelisp-types`; cross-crate consumer cascade NOT performed; workspace `cargo check` NOT run (expected broken — ~5-10 cascade sites in typecheck + backend); `public-api.txt` baseline regen deferred to end-of-walk; no consumer crate edits. **Closes Group B** (all four findings resolved: S-DRIFT-2, S-DRIFT-3 — Submission 30; S-DRIFT-8 — Submission 31; S-DRIFT-9 — Submission 32).

---

### Finding S-DRIFT-10 — `View<'a, C, L>` shape — **RESOLVED (Submission 34)**

**Direction: source moves to struct with private fields.** User-arbitrated 2026-05-23. The audit's prior bucket-C "arbitration genuine" framing was superseded by user direction — the discipline pattern that emerged through Group A/B (facade-as-target + Principle 18 when both options exist) settled the arbitration.

**Target shape (landed in `crates/cranelisp-types/src/view.rs` + `facades/types.md` §"View"):**

```rust
pub struct View<'a, C: CodeStore = (), L: LinkerStore = ()> {
    staging: Option<&'a SymbolTable<C, L>>,
    live: &'a SymbolTable<C, L>,
}

impl<'a, C: CodeStore, L: LinkerStore> View<'a, C, L> {
    pub fn union(staging: &'a SymbolTable<C, L>, live: &'a SymbolTable<C, L>) -> Self {
        Self { staging: Some(staging), live }
    }
    pub fn single(live: &'a SymbolTable<C, L>) -> Self {
        Self { staging: None, live }
    }
    pub fn lookup(&self, name: &Symbol) -> Option<&ModuleEntry<C>> {
        self.staging
            .and_then(|s| s.get(name.as_ref()))
            .or_else(|| self.live.get(name.as_ref()))
    }
    pub fn iter(&self) -> Box<dyn Iterator<Item = (&'a Symbol, &'a ModuleEntry<C>)> + 'a> {
        match self.staging {
            Some(staging) => /* chain staging.all_symbols() with live.all_symbols()
                                filtered to skip names already in staging */
            None => Box::new(self.live.all_symbols()),
        }
    }
}
```

**Grounding** (manifestation in `crates/cranelisp-types/src/view.rs` module rustdoc + struct rustdoc + `facades/types.md` §"View" §"Properties" §"Opacity is structural" bullet):

- **Decision 44** (cluster-atomic typecheck via orchestrator-owned staging) — names the opacity intent ("typecheck reads `ctx.current_symbol_table()` whenever it would have read `&SymbolTable` directly; it cannot tell whether the view unions staging+live or hits live alone") + uses "newtype" terminology (singular structural shape) for `View`. The opacity claim is structurally enforced only by the struct form with private fields. The prior `pub enum View { Single, Union }` form admitted consumer-side `match view { View::Union { .. } => …, View::Single { .. } => … }`, which IS observable staging-vs-live distinction — defeating the Decision's rationale.

- **Principle 18** (enforce architectural invariants structurally where possible) — when both a structural option and a behavioural one exist, the structural option is the right choice. The struct-with-private-fields form prevents the cluster-mode shortcircuit by construction; consumers consume `View` only through `lookup` / `iter`, which is the read-side abstraction Decision 44 names. The audit's prior framing — "(a) Source moves vs (b) Facade moves — both grounded; /arch arbitration" — over-weighted the configuration's permissive "newtype" wording at the expense of Principle 18.

**Internal encoding choice.** `staging: Option<&'a SymbolTable<C, L>>` (`Some` = cluster mode, staging consulted before live; `None` = committed mode, live only) + `live: &'a SymbolTable<C, L>` (unconditional). The `Option` encoding is the structural realisation of the cluster-vs-committed mode that the prior enum tag carried: cluster vs. committed is encoded as a single private `Option`, not as a public variant tag. The lookup / iter dispatch is straightforward `Option`-based logic (`self.staging.and_then(...).or_else(...)` for lookup; `match self.staging { Some(...) => chain, None => live-only }` for iter).

**`#[non_exhaustive]` deliberately NOT applied** — private fields already prevent external construction, so the structural non-exhaustivity is implicit. The struct shape supersedes the prior enum's `#[non_exhaustive]` attribute.

**Within-crate consumer migration.** The four match-arm sites inside `view.rs` itself (constructors + `lookup` + `iter`) are rewritten in the same edit. Grep of `crates/cranelisp-types/src/` confirms zero other within-crate pattern-match consumers on `View::Single` / `View::Union`.

**Discipline calibration note.** The audit's bucket-C "arbitration genuine" framing was superseded by user direction. The configuration loaded at audit time correctly identified Principle 18 as the tipping consideration ("the principled default" — see §6 A5 brief); user-arbitration settled to that default. The discipline pattern that emerged through Group A/B fires (facade-as-target by default; Principle 18 grounds the structural option when both exist) directly applies here — the prior "two paths, both grounded" framing under-weighted Principle 18's "the structural option is the right choice when both exist" claim. See `memory/feedback_facade_walk_no_interior.md` (within-crate consumer migration in scope) + `memory/feedback_hold_to_facade_default.md` (source-moves default when source has no Decision-level grounding for its current shape — the prior enum had no Decision-level grounding beyond the permissive "newtype" wording).

**Manifestation pointers**:

- Source: `crates/cranelisp-types/src/view.rs` (full file) — struct definition + impl block + module rustdoc + struct rustdoc citing Decision 44 + Principle 18 + opacity rationale + internal `Option` encoding rationale.
- Facade: `design/arch/facades/types.md` §"View" — struct shape with private `staging: Option<&'a SymbolTable<C, L>>` + `live: &'a SymbolTable<C, L>` fields documented; §"Properties" §"Opacity is structural" bullet added with full Decision 44 + Principle 18 grounding + opacity-defeat-by-prior-enum-form narrative; §"`#[non_exhaustive]` deliberately NOT applied" paragraph rewritten (was "`#[non_exhaustive]`" alone); §"Item-by-item disposition" §"Enum variants" introductory paragraph updated to exclude `View` from the enum-variants list (S-DRIFT-10 Submission-34 note inline); PIF row at §"Enum variants" rewritten — was "`View::Single`, `View::Union`" with PIF-candidate narrative; now "`View` (struct; no public variants)" with RESOLVED Submission-34 closure narrative + cross-reference to §"View" for the canonical shape statement.
- Audit: this closure block; triage register row updated; top-of-doc disposition-class table updated (Arbitration count 1 → 0 with A5-RESOLVED narrative; Source moves count 26 → 27 with S-DRIFT-10 reclassification rationale); §"Item-by-item disposition" summary table row updated; A5 brief in §6 marked RESOLVED.

**Wave-3 cascade (deferred to /dev per `memory/feedback_facade_walk_no_interior.md`).** Typecheck `ClusterContext` consumer pattern-match sites on `View::Single` / `View::Union` migrate to `view.lookup(name)` / `view.iter()` method calls. Per the audit's prior consumer trace (§6 A5 brief), these are minimal in typecheck — the typecheck pass code consumes `View` through `ctx.current_symbol_table()` and forwards to `lookup` / `iter` already. The mechanical-rewrite sites are the ones that did pattern-match (if any). Mechanical; no semantic shift.

**Discipline footer.** Walk-through fire per `memory/feedback_facade_walk_no_interior.md` — facade + source aligned within `cranelisp-types`; cross-crate consumer cascade NOT performed; workspace `cargo check` NOT run (expected broken — typecheck `ClusterContext` pattern-match sites on `View::Single` / `View::Union` need migration); `public-api.txt` baseline regen deferred to end-of-walk; no consumer crate edits. **Closes Group C** — all 5 findings resolved: U12, U13, U14, U15 (Submission 33); S-DRIFT-10 (Submission 34).

---

### Finding S-DRIFT-11 — RESOLVED (Submission 23 — walk row 23)

**User-arbitrated 2026-05-22; both move (fused params shape).** The prior audit framed this as "facade moves" — adopt source's parallel-vec shape `params: Vec<Symbol>` + `param_annotations: Vec<Option<TypeExpr>>` (with the "Principle 11 uniformity" rationale, which on review was a misattribution — Principle 11 governs single-pipeline mode parameters, not annotation shape). User-revised framing: source has the right **semantic** shape (per-param independently optional, no return-type field) but the wrong **structural** shape — the parallel-vec layout carries an unenforced `params.len() == param_annotations.len()` lockstep invariant, which **Principle 18** (enforce architectural invariants structurally) directs us to fold into the type.

**Target shape (landed in `crates/cranelisp-types/src/ast.rs` and `facades/types.md`):**

```rust
#[non_exhaustive]
pub struct DefnVariant {
    pub params: Vec<(Symbol, Option<TypeExpr>)>,
    pub body: Expr,
    pub span: Span,
}
```

**Grounding** (manifestation in `facades/types.md` §"AST" `DefnVariant` block + adjacent doc-comment + `crates/cranelisp-types/src/ast.rs` `DefnVariant` rustdoc):

- **Spec §5.1.1 EBNF** — `annotated_param = colon_prefix symbol | symbol` — annotation is independently optional per-param. The tuple `(Symbol, Option<TypeExpr>)` IS this grammar at the type level.
- **Spec §5.1 (L41)** — "The return type is always inferred; there is no return type annotation syntax." `return_type` field is deliberately absent.
- **Principle 18** — the fused tuple shape replaces the parallel-vec lockstep invariant with structural enforcement: a `Vec<(Symbol, Option<TypeExpr>)>` cannot get out of sync with itself, where two parallel `Vec`s can.

**Consumer cascade.** `cranelisp-frontend::build_annotated_params` returns the prior tuple shape; `cranelisp-typecheck` call sites that read `variant.params` and `variant.param_annotations` separately need migration. Deferred to /dev wave-3 per `memory/feedback_facade_walk_no_interior.md`.

**Expr::Lambda mirror — RESOLVED (Submission 24 — walk row 24).** The Submission-23 flag is closed. User-arbitrated 2026-05-22; both move on `Expr::Lambda` with the same grounding: spec §2.3.5 + §2.5 (`fn_expr` parameter list uses the same `param_list` / `annotated_param` EBNF as `defn`; per-param annotation independently optional) + Principle 18 (fused tuple replaces the parallel-vec lockstep invariant with structural enforcement) + Principle 7 (Lambda's shape mirrors `DefnVariant`'s — single source of truth for the same semantic concept). Target shape:

```rust
Lambda {
    params: Vec<(Symbol, Option<TypeExpr>)>,
    body: Box<Expr>,
    span: Span,
    inferred_type: Option<Box<Type>>,
}
```

Manifestation: `crates/cranelisp-types/src/ast.rs` `Expr::Lambda` variant (rustdoc added citing spec §2.3.5 + §2.5 + P18 + P7); `facades/types.md` §"AST" Lambda struct line + adjacent inline doc-comment; `facades/types.md` PIF row at §"Struct fields" consolidated — the single `params` tuple `.1: Option<TypeExpr>` row now covers both `DefnVariant` and `Expr::Lambda`. Cross-crate consumer cascade (frontend AST builder construction sites; typecheck `infer.rs:38–44` destructure + `infer_lambda` helper signature) deferred to /dev wave-3 per `memory/feedback_facade_walk_no_interior.md`. Within-crate consumer (`free_vars_expr` in `ast.rs`) migrated in-place under the variant-shape-change scope (precedent: Submission 22 within-crate match-arm pruning).

Closes S-DRIFT-11.

---

### Finding S-DRIFT-12 — `FieldDef` shape + missing span — **RESOLVED (Submission 25)**

**Disposition: both move.** User-arbitrated 2026-05-22 (Option A). Target shape landed:

```rust
pub struct FieldDef { pub name: Symbol, pub type_expr: TypeExpr, pub span: Span }
```

Grounding:
- **`name: Symbol`** (not `Option<Symbol>`) — spec §2.2.6 + §5.2 grammar `field_def = annotation SYMBOL | SYMBOL` terminates in a required `SYMBOL` on both productions. The facade's prior `Option<Symbol>` admitted a case unreachable from any parser path.
- **`type_expr: TypeExpr`** (Option A — unconditional `TypeExpr`, not `Option<TypeExpr>`) — bare fields receive a synthesised `TypeExpr::TypeVar` at parse time; ADT type-resolution consumers always have a syntactic type to resolve. User chose Option A over Option B's `Option<TypeExpr>` consistency-with-`DefnVariant`/`Lambda` alternative on the grounds that `FieldDef` is consumed at a different layer (ADT type resolution) than per-param annotations (inference fan-in); the synthesis-at-parse policy preserves a uniform downstream contract. Editorial naming `type_expr` (over the prior facade `ty`) is canonical per Principle 7 — producer-side naming is the single source of truth.
- **`span: Span`** — Decision 39 grounding (per-defn source coordinate system; substance manifested in `facades/types.md` §"Symbol table" and `repl/spec.md` §15.4). Per-field span is the structural prerequisite for "field has wrong type" diagnostics that point at the field's source location, not the enclosing constructor.

**Scope correction vs. prior framing.** The prior disposition deferred the source-side `span` field-add to the H11 / S-DRIFT-4 D39-per-name-span arc on the assumption that source-side struct changes were out of scope for the walk. That framing was revised by the 2026-05-21 update to `memory/feedback_facade_walk_no_interior.md` — source-side struct/field additions ARE in scope for the walk; only function-body population and cross-crate consumer cascade defer. Per the updated rule, Submission 25 lands the `span: Span` field add on `FieldDef` in `cranelisp-types`. The wave-3 work that remains is parser-side population (set real spans from `field_sexp.span()` rather than `Span::SYNTHETIC`) and the ~25 construction sites across `cranelisp-frontend` + `cranelisp-typecheck` that need the new field added to their `FieldDef { ... }` initialisers. `Span::SYNTHETIC` is acceptable as the initial population value when the cascade lands; real-span population is the D39 arc proper.

**Manifestation.**
- `crates/cranelisp-types/src/ast.rs` `FieldDef` struct (lines ~363–386): added `pub span: Span` with `#[serde(default)]` for cache compatibility; rustdoc cites spec §2.2.6 + §5.2 + Decision 39 + the synthesised-`TypeVar`-for-bare convention.
- `crates/cranelisp-types/src/span.rs`: `Span` gains `Default` derive (structurally equivalent to `Span::SYNTHETIC`) so `#[serde(default)]` works on the new field; doc-comment notes the Submission 25 motivation.
- `design/arch/facades/types.md` §"AST" `FieldDef` struct line (~230): target shape; adjacent inline doc-comment cites spec + Principle 7 + Decision 39 + synthesised-`TypeVar` convention.
- `design/arch/facades/types.md` PIF rows (line ~1648–1649): `type_expr` row updated to note the unconditional-`TypeExpr` convention + Option-B rejection; new `span` row added with Decision 39 grounding + serde-default note.
- `design/arch/facades/types.md` migration-map for retired `ConstructorInfo` (lines ~1327–1328): `.fields[i].ty` → `.fields[i].type_expr` + new line for `.fields[i].span`.

**Cross-crate consumer cascade deferred to /dev wave-3** per `memory/feedback_facade_walk_no_interior.md`. ~25 construction sites need the new `span` field added. Workspace `cargo check` expected broken across consumer crates; no consumer crates touched; no `public-api.txt` regen this fire.

---

### Finding S-DRIFT-13 — `TraitImpl` shape — RESOLVED (Submission 27, 2026-05-22)

**Resolution.** Both move. The right answer pulled on a deeper thread than the prior framings recognised: the syntactic stage needs to capture **as-written qualification** structurally, not just at the `TraitImpl` use site but at every `TypeName` / `TraitName` reference site (`TypeExpr::Named`, `TypeExpr::Applied`, `TraitImpl.trait_name`, `TraitImpl.type_constraints`). This produced new syntactic-stage newtypes + a TypeExpr cascade + a 5-field `TraitImpl` target — conceptually one change, many touch points.

**New syntactic-stage newtypes** (in `crates/cranelisp-types/src/newtype.rs`):

```rust
pub struct TraitRef {
    pub module: Option<ModuleFullPath>,
    pub name: TraitName,
}

pub struct TypeRef {
    pub module: Option<ModuleFullPath>,
    pub name: TypeName,
}
```

Same structural shape as `FQTraitName` / `FQTypeName` but with `Option<ModuleFullPath>` because the syntactic stage captures **what the user wrote**: unqualified (`Int`, `Display`), aliased (`option/Option`, `fmt/Display`), or fully-qualified (`core.option/Option`, `core.fmt/Display`). Per spec §2.3.4 + §4.2.2 qualified references resolve via the module system; typecheck resolves the optional module through the import graph at the lift site, producing `FQTraitName` / `FQTypeName` at the resolved-stage boundary per Decision 47.

**`TypeExpr` cascade** (in `crates/cranelisp-types/src/ast.rs`):

```rust
pub enum TypeExpr {
    Named(TypeRef),                  // was Named(TypeName)
    Applied(TypeRef, Vec<TypeExpr>), // was Applied(TypeName, …)
    TypeVar(Symbol),
    SelfType,
    FnType(Vec<TypeExpr>, Box<TypeExpr>),
}

impl TypeExpr {
    pub fn head_ref(&self) -> Option<&TypeRef>;  // for Named/Applied; None for TypeVar/SelfType/FnType
}
```

The `Named` and `Applied` variant payloads cascade from bare `TypeName` to `TypeRef`. The `head_ref` accessor places data-ownership of the head reference on `TypeExpr` per data-ownership discipline #1.

**Target `TraitImpl` shape** (in `crates/cranelisp-types/src/ast.rs`):

```rust
pub struct TraitImpl {
    pub trait_name: TraitRef,
    pub target: TypeExpr,
    pub type_constraints: Vec<(Symbol, TraitRef)>,
    pub methods: Vec<Defn>,
    pub span: Span,
}
```

5 fields. Diff from prior source's 6-field shape:
- `trait_name: TraitName` → `TraitRef` (qualification captured structurally)
- `target_type: TypeName + type_args: Vec<Symbol>` → fused into `target: TypeExpr` (target's TypeExpr contains the TypeRefs which contain the args' qualification; type-var bindings are reachable structurally as `TypeExpr::TypeVar` inside `target`)
- `type_constraints: Vec<(Symbol, TraitName)>` → `Vec<(Symbol, TraitRef)>` (constraints can be qualified — `:(fmt/Display a)`)

**Scope correction vs. prior framing.** The prior triage-D framing ("facade catch-up to source's syntactic-stage shape") missed two things:

1. **Source's `trait_name: TraitName` was wrong.** `(impl fmt/Display ...)` is valid spec-grammar (qualified references per spec §4.2.2 + §2.3.4); the as-written qualification needs to be captured. Bare `TraitName` discards it. Holding the facade as `FQTraitName` was over-prescriptive (it forced resolution before AST construction); holding source as `TraitName` was under-prescriptive (it discarded the user's qualification). Neither pole was right — both moved to `TraitRef`, the missing third option.

2. **The `target_type + type_args` split had no Decision-level grounding.** Spec §5.4 EBNF treats `target_type` as one grammatical unit (`target_type = qualified_symbol | '(' qualified_symbol type_arg+ ')'`); the split of "head name" + "type vars" into two separate fields was a source-side implementation detail. Per `feedback_hold_to_facade_default.md` the default discipline when source has no Decision-level grounding is source-moves; per the configuration's spec-EBNF reading the target IS one grammatical unit, captured uniformly as `target: TypeExpr` (simple target → `TypeExpr::Named(TypeRef)`; polymorphic target → `TypeExpr::Applied(TypeRef, Vec<TypeExpr>)`).

The deeper consequence: syntactic-stage qualification is captured **structurally everywhere** via the new `TraitRef` / `TypeRef` types, not just at the `TraitImpl` use site. This sharpens Decision 47's producer/consumer split — the syntactic stage no longer carries "bare name slips through" but "syntactic stage carries the qualification structurally; typecheck does the lift."

**Grounding.**

- **Spec §2.3.4 / §2.5** — qualified-reference grammar (`module/name`); the syntactic stage carries the optional leading-module part structurally.
- **Spec §4.2.2** — qualified references resolve via the module system; the lift to canonical defining-module is typecheck's responsibility.
- **Spec §5.4 EBNF** — `impl_form = '(' 'impl' trait_ref constraints? target_type method_def* ')'`; `target_type = qualified_symbol | '(' qualified_symbol type_arg+ ')'` — one grammatical unit, captured uniformly as `TypeExpr`.
- **Spec §8** — module / import / qualification semantics: the import graph is what the lift consults.
- **Decision 47** — FQTypeName / FQTraitName binding at resolved-stage boundaries; the producer/consumer split is sharpened by S69 Submission 27.
- **Decision 45** — `ModuleEntry::TraitImpl` storage on trait's defining module (the resolved-stage counterpart; FQ names throughout post-resolution).
- **`feedback_hold_to_facade_default.md`** — source-moves default when source has no Decision-level grounding for its current shape.
- **`feedback_configuration_grounds_facade.md`** — facade is meaningful only as grounded by Decisions / Principles / spec; the new `TraitRef` / `TypeRef` types are the missing structural carriers.

**Manifestation pointers.**

- `crates/cranelisp-types/src/newtype.rs` — new `TraitRef` + `TypeRef` structs with rustdoc citing spec §2.3.4 + §4.2.2 + Decision 47.
- `crates/cranelisp-types/src/lib.rs` — `TraitRef` / `TypeRef` added to the newtype re-export list.
- `crates/cranelisp-types/src/ast.rs` — `TypeExpr::Named` / `Applied` cascade from `TypeName` to `TypeRef`; `head_ref` helper added; `TraitImpl` rewritten to 5-field target; rustdoc on both citing spec §5.4 EBNF + spec §4.2.2 + Decision 47 sharpening + cross-reference to `ModuleEntry::TraitImpl`.
- `design/arch/facades/types.md` — §"AST" `TypeExpr` enum expanded with explicit variants + `head_ref` + cross-reference to S69 Submission 27; `TraitImpl` struct line ~269 rewritten to 5-field target + adjacent doc-comment citing spec §5.4 EBNF + cross-reference to resolved-stage `ModuleEntry::TraitImpl`; new §"Syntactic-stage references (S69 Submission 27)" section after §"Fully-qualified references" documenting `TraitRef` / `TypeRef` with three-case as-written examples; §"Resolved type system" — D47 exception text rewritten to four-pair partition (`TypeRef` ↔ `FQTypeName`; `TraitRef` ↔ `FQTraitName`); producer/consumer paragraph rewritten; PIF row at line ~1678 (was `type_args, type_constraints`) replaced with consolidated `target, type_constraints, trait_name` row.
- This audit closure (you are reading it).

**Consumer cascade deferred to /dev wave-3.** Substantial — every `TypeExpr::Named(TypeName)` / `Applied(TypeName, …)` pattern-match consumer in frontend (parser construction sites — `ast_builder` `build_type_expr` etc.), typecheck (`resolve.rs` lift site, `traits.rs` `fqtn_for_bare_type_name`, `infer.rs` annotation walks, ADT registration), backend (any annotation-walking codegen path), and `src/` int (REPL `/info` / `/sig` annotation rendering) needs to update to the `TypeRef` payload (most consumers will use `.name` for back-compat or shift to the new `head_ref()` accessor). Construction sites for `TraitImpl` (~5–10 across `cranelisp-frontend/ast_builder.rs` impl-building) need the 5-field shape with `TraitRef` / `TypeExpr` construction. Workspace `cargo check` expected broken across consumer crates; per `memory/feedback_facade_walk_no_interior.md` `cargo check` was NOT run; consumer crates NOT touched; `public-api.txt` baseline regen deferred to end-of-walk.

---

### Finding S-DRIFT-14 — `TraitMethodSig` shape — RESOLVED (Submission 26, 2026-05-22)

**Resolution.** Both move. Target shape:

```rust
#[non_exhaustive]
pub struct TraitMethodSig {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub params: Vec<(Symbol, TypeExpr)>,
    pub ret_type: TypeExpr,
    pub span: Span,
    pub hkt_param_index: Option<usize>,
    pub default_body: Option<Expr>,
}
```

7 fields. Diff from prior source's 8-field shape: `params: Vec<TypeExpr>` → `Vec<(Symbol, TypeExpr)>` (fused); `default_param_names: Vec<Symbol>` retired (subsumed into `params.0`); `default_body: Option<Sexp>` → `Option<Expr>`. Diff from prior 4-field facade: rename `return_type` → `ret_type`; add `docstring`, `span`, `hkt_param_index`; switch `params` to fused tuple (the audit's original facade row had `params: Vec<TypeExpr>` which lost the names entirely).

**Grounding.**

- **Spec §5.3 EBNF** — `required_method = '(' name docstring? '[' param+ ']' type_expr ')'`; `default_method  = '(' name docstring? '[' param+ ']' body ')'`; `param = ':' type_expr symbol | symbol`. **Every method has named parameters** — the `param` production always terminates in a `symbol`. The audit's prior framing (and my pre-correction proposals) implicitly coupled `default_param_names` to default-method-only — that coupling was a semantic-model error. Names belong with the params, not with the default body. Fused into `params.0` per Principle 18.
- **Spec §5.3.1** — bare parameter names default to the implementing type. The parser synthesises `TypeExpr::SelfType` for bare params at parse time, so `Vec<(Symbol, TypeExpr)>` is unconditional (consumers always have a name + a syntactic type). This collapses the `Option<TypeExpr>` from the `DefnVariant` / `Lambda` mirror — for traits the synthesis convention always produces some `TypeExpr` (either user-written or synthesised `SelfType`).
- **Spec §5.3.2** — HKT traits parameterise on type constructors; `hkt_param_index: Option<usize>` identifies which parameter position uses the HKT constructor variable. HKT traits forbid default-method implementations (parser guard in `build_method_sig`).
- **Spec §5.4.5** — "Method bodies are type-checked against the instantiated trait signature." This grounds `default_body: Option<Expr>` (the target) over `Option<Sexp>` (prior source): AST building at trait-decl time catches structural errors in special forms (`let`, `if`, `match`, etc.) immediately, while name resolution + type-checking still defer to per-impl context (the trait declaration clones the `Expr` into each impl's typecheck context).
- **Principle 18** (enforce invariants structurally) — fused `(Symbol, TypeExpr)` tuple replaces parallel-vec lockstep invariant; `default_param_names` deletion eliminates the implicit invariant `default_param_names.is_empty() == default_body.is_none()` by construction.
- **Principle 7** (single source of truth) — `ret_type` is the canonical producer-side naming (over the prior facade `return_type`).
- **Decision 39** — per-defn source coordinate system; substance manifested in `facades/types.md` §"Symbol table" and `repl/spec.md` §15.4. `span: Span` per method for diagnostics.

**Scope-correction note vs. prior audit framing.**

1. The audit's original "facade moves" disposition was grounded on **Principle 11** ("uniform Sexp default-body"). Submission 23 corrected this misattribution — Principle 11 governs single-pipeline mode parameters, not Sexp-vs-AST default-body retention. With the misattribution removed, source's `Option<Sexp>` had **no Decision-level grounding**; per `feedback_hold_to_facade_default.md` the default discipline is source-moves. Facade is target; source moves to `Option<Expr>`.

2. The audit's semantic model was wrong. Coupling `default_param_names` to `default_body` treats required-method params as nameless type expressions — but spec §5.3 EBNF assigns names to every method's params (`param` production always terminates in a `symbol`). The parameter names belong with the parameters, not with the default body. Fused into `params.0` per Principle 18.

3. **Source-side bonus discovery** — `crates/cranelisp-frontend/src/ast_builder.rs:713` (the required-method branch of `build_method_sig`) parses bracket items via `build_type_expr` directly, discarding parameter names entirely. Per spec §5.3 (the `param` production), required-method params have names. The required-method branch should mirror the default-method branch's `build_annotated_params(&children[next])` call and produce `(Symbol, TypeExpr)` pairs (with synthesised-`SelfType` for bare names per spec §5.3.1). This is a parser defect that the wave-3 consumer cascade must address. **Filed as a separate FIXME after the walk completes** (not in this submission's scope — see SPRINT.md Submission 26 row for the follow-up flag).

**Manifestation pointers.**

- `crates/cranelisp-types/src/ast.rs` — `TraitMethodSig` struct rewritten to 7-field target shape + rustdoc citing groundings above.
- `design/arch/facades/types.md` — `TraitMethodSig` struct line ~236 updated; adjacent inline doc-comment rewritten; PIF row at §"Item-by-item disposition" (line ~1651) updated.
- This audit closure (you are reading it).

**Consumer cascade deferred to /dev wave-3.** Workspace build expected broken across `cranelisp-frontend` (`build_method_sig` — required-method branch needs name-capture per spec §5.3.1; default-method branch needs `default_body` to come from `build_expr` not `children[ret_pos + 1].clone()`) + `cranelisp-typecheck` (`traits.rs` ~6 read sites on `default_param_names` / `default_body`; 4 construction sites in tests; instantiated-signature typecheck path clones the `Expr` per impl per spec §5.4.5). ~10–15 sites total. `public-api.txt` baseline regen deferred to end-of-walk per `memory/feedback_facade_walk_no_interior.md`.

Closes S-DRIFT-14.

---

### Finding S-DRIFT-15 — RESOLVED (Submission 21, 2026-05-21)

Form-record narrow + facade alignment per spec §2.2.9 lands in `facades/types.md` §"Cross-module structural specs" (`PlatformSpec { name: ModuleName, span: Span }` — `manifest_path` + `alias` fields dropped; spec §2.2.9 grammar permits no alias; resolved data does not belong on a form-record).

Adjacent architectural finding: `ModuleEntry::PlatformDecl` retires; platform modules register at `symbol_tables["platform.<name>"]` per spec §8.9.3; the loaded DLL handle lives on the platform module's **own** SymbolTable via the new `D: DllStore` generic + `dll: Option<D>` field. See `facades/types.md` §"Symbol table — the single store" SymbolTable shape + the `PlatformDecl` retirement note on `ModuleEntry` + walk-log Submission 21.

Source cascade in /dev wave-3 concurrency-cluster brief: (a) `String → ModuleName` newtype narrow on `PlatformSpec.name` + update construction sites in `parse_platform` and `parse_platform_sexp` (`crates/cranelisp-frontend/src/module_extract.rs`); (b) add `DllStore` marker trait + third generic parameter `D: DllStore` to `SymbolTable` + `dll: Option<D>` field + serde discipline; (c) delete `ModuleEntry::PlatformDecl` variant; (d) update platform-load path so the Dll handle returned by DLL-load lands in `symbol_tables["platform.<name>"].dll = Some(dll)`.

Arbitration A7 (carried from prior audit; framed as "resolved-vs-pre-resolved shape") is **closed** by the form-record framing — the form-record's job is to record what the user wrote, NOT to carry resolved data. Resolved state is structural (the existence of `symbol_tables["platform.<name>"]` + its `dll` field + its `symbols`).

---

### Finding S-DRIFT-16 — `ModDecl` shape — **RESOLVED (Submission 40, 2026-05-24)**

**Triage bucket: D — mechanical.** Originally "No action"; revisited Sub 40 under user-arbitration.

**Facade expects.** Line 597 (pre-S40): `pub struct ModDecl { pub name: ModuleName, pub visibility: Visibility, pub span: Span }` — 3-field abbreviation that omitted `inline_body`.

**Source does (pre-S40).** `module.rs:1061-1066`: `pub struct ModDecl { pub name: ModuleName, pub is_private: bool, pub inline_body: Option<Vec<Sexp>>, pub span: Span }` — 4 fields with `is_private: bool` synonym.

**Design intent.** Two coupled drifts: (1) `is_private: bool` vs `visibility: Visibility` — ModDecl was the **only** struct in the entry/decl family using the bool synonym; every other entry/decl uses `visibility: Visibility` and `is_public()` consults that one field uniformly. Principle 7 (single source of truth — same property, one encoding) + Principle 18 (enforce invariants structurally — `Visibility` is the enum that exists for this purpose) ground source-side narrowing. (2) `inline_body` is a real persistent field load-bearing during the parse-write-load lifecycle (frontend populates → int's `worker::handle_mod` consumes via `write_inline_mod_to_disk` → int's source-rewriter MUST emit as `(mod name)` per spec §8.2.2 step 2). The audit's "shape-summary abbreviation" was tolerable when audits were lighter; Sub 30/36/39's trajectory toward fuller surface accuracy in shape summaries supersedes that tolerance.

**Disposition.** **RESOLVED by source narrowing + facade enumeration + FIXME file (S69 Sub 40).** Three coupled changes:

(1) `ModDecl.is_private: bool → visibility: Visibility` source narrowing per Principle 7 (single source of truth; ModDecl was the only struct in the decl/entry family using bool synonym; every other entry/decl uses Visibility) + Principle 18 (enforce invariants structurally — Visibility is the enum that exists for this purpose). Consumer cascade (`.is_private` → `.visibility == Visibility::Private`) deferred to wave-3.

(2) Facade shape summary updated honestly to 4 fields including `inline_body: Option<Vec<Sexp>>` — the audit's "no action" deferral to per-field disposition table is superseded by Sub 30/36/39's trajectory toward fuller surface accuracy in shape summaries. Lifecycle of `inline_body` documented adjacent to the shape: frontend populates → int's `worker::handle_mod` consumes via `write_inline_mod_to_disk` → int's source-rewriter MUST emit `(mod name)` only per spec §8.2.2 step 2.

(3) FIXME `design/arch/fixmes/0217-inline-module-spec-rewrite.md` filed against `/int` for spec §8.2.2 step 2 (parent-file rewrite) implementation gap. User-arbitrated reading: `inline_body` stays as a real persistent field; the rewriter strips it on serialization rather than the data shape changing. The spec gap closes when /int implements the rewrite, not by retiring the field.

**Wave-3 cascade anticipated.** `is_private` field reads / construction sites in `crates/cranelisp-frontend/src/module_extract.rs` (parse_mod_decl signature + construction + 5 test assertions); `src/worker.rs` (~8 sites — construction in tests + privacy-check predicate at line 1547 + visibility derivation at line 1323 + save serialisation at `src/save.rs:119,478`). Mechanical rename `.is_private` → `.visibility == Visibility::Private` and `is_private: bool_value` → `visibility: if bool_value { Visibility::Private } else { Visibility::Public }`.

---

### Finding S-DRIFT-17 — RESOLVED (Submission 36, 2026-05-23) — ModuleEntry settlement with scope extension

**Settlement direction.** The original disposition ("facade catch-up to D48-mandated 3-variant split `{ Inline, Extern, PlatformEffect }`") is **superseded by a scope-extended cluster correction**. Neither the facade-stale `{ Builtin, PlatformEffect }` 2-variant shape nor the source-stale `{ Inline, Extern, PlatformEffect }` 3-variant shape is the target. The settlement retires `PrimitiveKind` entirely and lands four convergent changes under one fire, surfaced by user-questioning during walk-through:

1. **`PrimitiveKind` enum retired.** `Inline`/`Extern` variants were vestigial — no production consumer read them (verified by grep at submission time; only test assertions read the discriminator). Backend dispatches all bundled primitives uniformly via GOT slot per Decision 48; inline-eligibility for arithmetic / vec / sexp ops is encoded per-call-site in `ResolvedCall::BuiltinFn { name }` (set by typecheck), not in a `PrimitiveKind::Inline` discriminator.

2. **`jit_name: Option<JitSymbol>` field retired from `DefKind::Primitive`.** The symbol-table key IS the JIT linker name uniformly per `src/CLAUDE.md` §"JIT Symbol Names". For bundled primitives the key is bare kebab-case (`str-concat`, `vec-push`, etc.) and that bare name IS what the JIT registers under. For trait methods / multi-sig variants the key is already mangled (`Display.show$Option$Int`, `add$Int+Int`). No separate field is needed. Rust runtime functions rename per the same convention (drop `cranelisp_` prefix; `JITBuilder::symbol()` registers under the spec name) — that rename is wave-3 cascade work.

3. **`PlatformEffect` promoted to `DefKind` sibling variant.** Was the `PrimitiveKind::PlatformEffect { scheduling_class }` sub-variant; now `DefKind::PlatformEffect { scheduling_class }`. The `scheduling_class` is the cross-crate-load-bearing payload (read by `src/worker.rs` for JIT-symbol-table registration; carried in IO trampoline records per Decision 26). PlatformEffect's body location (DLL) is structurally distinct from bundled-primitive provenance — sibling-variant placement under `DefKind` reflects that. Decision 26's variant-internal invariant ("a user fn cannot carry a scheduling_class") is preserved at the `DefKind` level.

4. **`SpecialForm` promoted to `ModuleEntry` sibling variant** (per user direction "we want to settle ModuleEntry"). Special forms read only 4 of `Def`'s ~11 fields (`scheme`, `param_names`, `docstring`, `description`); a dedicated `ModuleEntry::SpecialForm` variant fits the introspection use case cleanly and parallels Submission 30's `IntrinsicType` shape (compiler-provided construct, no user-level definition, no JIT registration, no `got_slot`, no `code`, no `ast`). The new variant lives in the root module `""` per FIXME 0193.

**Target shape (now in `facades/types.md` §"Symbol table — the single store").**

```rust
pub enum ModuleEntry<C: CodeStore = ()> {
    Def {
        scheme: Scheme,
        visibility: Visibility,
        docstring: Option<String>,
        param_names: Vec<Symbol>,
        kind: Box<DefKind>,
        callees: Vec<FQSymbol>,
        got_slot: Option<usize>,
        trait_origin: Option<FQTraitName>,
        seq: u64,
        ast: Option<DefnVariant>,
        code: Option<C>,
    },
    SpecialForm {
        scheme: Scheme,
        param_names: Vec<Symbol>,
        docstring: Option<String>,
        description: String,
        visibility: Visibility,
    },
    IntrinsicType { ty: Type, visibility: Visibility },
    TypeDef { /* … */ },
    TraitDecl { /* … */ },
    Import { /* … */ },
    TraitImpl { /* … */ },
    Ambiguous { /* … */ },
}

pub enum DefKind {
    Primitive,                                                              // bundled — no payload
    PlatformEffect { scheduling_class: SchedulingClass },                    // DLL-routed
    UserFn { constrained_fn: Option<Box<ConstrainedFn>> },
    Overloaded { variants: Vec<OverloadVariant>, sexp: Option<Sexp>, source: Option<String> },
    Constructor { type_name: FQTypeName, tag: usize, field_count: usize, internal: bool },
    Macro { clauses_meta: Vec<MacroClauseInfo>, sexp: Option<Sexp>, source: Option<String> },
}

// PrimitiveKind enum DELETED.
```

**Grounding.**
- **Decision 48** (primitives uniform module + bundled provenance) — primitives dispatch via GOT uniformly; `Inline`/`Extern` was a stale pre-D48 sub-discrimination.
- **Decision 26** (variant-internal scheduling_class) — preserved at the `DefKind` level after PlatformEffect's promotion.
- **Principle 7** (single source of truth) — symbol-table key IS the JIT linker name; no `jit_name` duplicates that data.
- **Principle 18** (enforce architectural invariants structurally where possible) — a variant fits its data: `Def`'s 11 fields don't fit a 4-field special-form record; the dedicated `ModuleEntry::SpecialForm` variant is structurally correct. PlatformEffect-vs-bundled-Primitive is a sibling provenance distinction at the `DefKind` level, not a sub-classification inside one variant.
- **`src/CLAUDE.md` §"JIT Symbol Names"** (convention) — every symbol addressable as `module/symbol` (or appropriate mangled form); the key IS the JIT linker name.
- **Submission 30 parallel** (`IntrinsicType` shape) — the same shape-justification pattern (compiler-provided construct, distinct enough to be a sibling variant) applies to `SpecialForm` and underwrites the promotion.

**Scope-extension vs original framing.** The audit's original disposition named only "facade catch-up to source's 3-variant split". Submission 36 scope-extends through user-questioning: each of the four convergent changes (PrimitiveKind retirement / jit_name retirement / SpecialForm promotion / PlatformEffect promotion) was surfaced by asking "what is this field/variant actually for?" against current production consumers. The audit's mechanical-direction framing missed the structural opportunity to settle the larger ModuleEntry shape under one fire — the "ModuleEntry settlement" framing per user direction was the trigger.

**Manifestation pointers (source-side aligned this fire).**
- `crates/cranelisp-types/src/module.rs`:
  - `ModuleEntry::SpecialForm` variant added (5 fields) — line 596+ region.
  - `DefKind::Primitive { primitive_kind, jit_name }` → `DefKind::Primitive` (no payload).
  - `DefKind::PlatformEffect { scheduling_class }` added as sibling variant.
  - `DefKind::SpecialForm` variant deleted.
  - `pub enum PrimitiveKind` enum deleted entirely; replaced with a block comment explaining the retirement rationale at the previous declaration site.
  - `impl<C: CodeStore> ModuleEntry<C>` blocks updated: `is_public` and `into_concrete` add `SpecialForm` arms (mechanical field copy).
  - In-crate tests (lines ~1750–1855) rewritten — `def_kind_platform_effect_carries_scheduling_class` (was `primitive_kind_platform_effect_carries_scheduling_class`) destructures the new `DefKind::PlatformEffect { scheduling_class }`; `platform_effect_scheduling_class_round_trips` updated to new shape; both tests drop `jit_name` references and add a serde assertion that `jit_name` does NOT appear in the JSON.
  - `use crate::JitSymbol;` line retired with comment.
- `crates/cranelisp-types/src/lib.rs` — `PrimitiveKind` re-export removed; retirement comment added.
- `crates/cranelisp-types/src/scheduling.rs` — module-level rustdoc updated to cite `DefKind::PlatformEffect` (was `PrimitiveKind::PlatformEffect`).
- `design/arch/facades/types.md` — `ModuleEntry` shape summary updated (new `SpecialForm` variant + got_slot doc-comment updated for the new `Primitive` / `PlatformEffect` shapes + JIT symbol naming policy paragraph added); `DefKind` shape rewritten (no `Primitive` payload; new `PlatformEffect` variant; no `SpecialForm`); `PrimitiveKind` block deleted from facade with retirement comment; PIF table rows updated for `ModuleEntry::SpecialForm`, `description` (relocated), `jit_name` (RETIRED); `ModuleEntry::arity()` doc updated for the new variant set; §"Scheduling" paragraph updated to reference `DefKind::PlatformEffect`.
- This audit closure (replaces the prior finding body).

**Disposition class.** Reclassified D → "RESOLVED — scope-extended cluster correction" (a new framing the audit register accommodates alongside the prior "RESOLVED by deletion / self-reconciliation"). The audit's original "facade moves" disposition stood for the narrow finding; the settlement extension overruns that framing with structural cluster-correction.

**Within-crate consumer migration in scope and landed.** 2 test fixtures updated; 4 in-crate `impl ModuleEntry` match-arm extensions (`is_public`, `into_concrete`, both gain `SpecialForm`); one `use crate::JitSymbol;` retirement; one `defined_symbols` filter — verified that the filter still terminates correctly without modification because `SpecialForm` is no longer a `Def` variant and was never matched by the `ast.is_some()` predicate. Cross-crate consumer cascade (~100+ sites) is wave-3 work.

**Wave-3 cascade (deferred to /dev).** Substantial:
- **typecheck `builtins.rs`** — registration sites drop `jit_name` and `primitive_kind` arguments to `register_primitive` (or equivalent); SpecialForm registrations convert from `DefKind::SpecialForm { description }` payload to `ModuleEntry::SpecialForm { … }` variant construction. Many sites.
- **typecheck `infer.rs::resolve_primitive_jit_name`** (lines 447–500) — simplify dramatically: just check if entry is `DefKind::Primitive`, return the symbol-table key (which IS the JIT linker name).
- **`src/worker.rs` PlatformEffect pattern-matches** (lines 2962–3000, 3565) — update from `DefKind::Primitive { primitive_kind: PrimitiveKind::PlatformEffect, .. }` to `DefKind::PlatformEffect { .. }`.
- **`cranelisp-primitives` self-registration sites** — same `DefKind::Primitive` no-payload shape.
- **Rust runtime functions** — `cranelisp_trace_<X>` → `trace_<X>` rename pass per `src/CLAUDE.md` JIT Symbol Names convention; `JITBuilder::symbol()` calls register under the spec/symbol-table-key name.
- **Test fixtures pattern-matching on `PrimitiveKind` / `DefKind::SpecialForm`** — mechanical conversion to new shapes.

**Closes Group E partially — S-DRIFT-17 closed with scope extension.** U18 (SchedulingClass default) + U22 (HeapCategory::classify) are NOT in this fire — separate closure. (U22 subsequently RESOLVED by relocation per Submission 38 — see §"Finding U22" body.)

**Discipline observations.** Walk-through fire per `memory/feedback_facade_walk_no_interior.md` — facade + source aligned within `cranelisp-types`; within-crate consumer migration (2 test fixtures + 4 match-arm extensions + 1 import retirement + 3 doc-comment sweeps) IS in scope and landed; cross-crate consumer cascade NOT performed (~100+ sites deferred to /dev wave-3); workspace `cargo check` NOT run (expected broken at the wave-3 sites); `public-api.txt` baseline regen deferred to end-of-walk per S67 baseline-diff discipline; no consumer crate edits.

**Cross-references.** Decision 26 (variant-internal scheduling_class — preserved); Decision 48 (primitives uniform module — bundled provenance; the structural payload PIF that motivated the original audit finding); `src/CLAUDE.md` §"JIT Symbol Names" (the convention that retires `jit_name`); Submission 30 (`IntrinsicType` shape — the parallel-justification pattern for `SpecialForm` promotion); Principle 7 (single source of truth — symbol-table key IS the linker name); Principle 18 (enforce invariants structurally — a variant fits its data); `memory/feedback_facade_walk_no_interior.md` (within-crate migration in scope; cross-crate cascade deferred); `memory/feedback_proposal_discipline.md` (data ownership / single responsibility / minimum mechanism — surfaced PrimitiveKind's vestigial nature and jit_name's derivability).

Closes S-DRIFT-17 with scope extension.

---

### Finding S-DRIFT-18 — RESOLVED (Submission 28, 2026-05-22)

**Facade catch-up to source: associated-const idiom + Default-derive documentation + always-public `new()` / `merge()` documented.**

**Target shape now in `facades/types.md` §"Public surface" §"Source-level constructs":**

```rust
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub const SYNTHETIC: Span = Span { start: 0, end: 0 };
    pub fn new(start: u32, end: u32) -> Self;
    pub fn merge(self, other: Span) -> Span;
}
```

**Grounding.**
- `SYNTHETIC` as associated const: Rust idiom; no Decision-level question — source canonical.
- `Default` derive: documents Submission 25's source addition (`#[serde(default)]` cache compatibility for `FieldDef::span`); same value as `SYNTHETIC` but distinct semantic role (synthetic-form marker vs serde-default zero).
- `new()` / `merge()`: always-public APIs that the prior facade text never documented; modest editorial improvement bundled into this catch-up.

**Scope-extension vs. original framing.** The audit's original disposition named only the `SYNTHETIC` associated-const flip. This closure documents two adjacent shapes (`Default` derive + `new`/`merge`) that the source has but the facade did not name. The bucket stays "Facade moves" (no source change, no reclassification) — the extension is editorial completeness, not a redirected disposition.

**Manifestation pointers.**
- `crates/cranelisp-types/src/span.rs` — source canonical (no change).
- `design/arch/facades/types.md` §"Public surface" §"Source-level constructs" — `Span` block updated to associated-const + `Default` + `new`/`merge`; inline note added on `default()` vs `SYNTHETIC` semantic-role distinction.
- This audit closure.

**No source change. No consumer cascade. No `cargo check`. No `public-api.txt` regen.**

Closes S-DRIFT-18.

---

### Finding S-DRIFT-19 — RESOLVED (in /dev concurrency-cluster brief).

Source-side migration scheduled in SPRINT.md row 53 (Category A — SymbolTable concurrency cluster, promoted to in-sprint S69 per user direction 2026-05-20). Flip `symbols: HashMap → DashMap`; flip writes to `&self`; lift `next_got_slot: usize → AtomicUsize`; change `get` return to `Ref<'_, Symbol, ModuleEntry<C>>`; demote `pub` structural fields to `pub(crate)` (C-HOLE-5); add encapsulating write methods per H3/H5/H6/H7. Grounded by Decisions 31/32/38/41/44/48 + canonical `concurrency-symbol-table-entry.mmd` sequence diagram + Principle 18. The 91 register-call sites flow through `current_symbol_table_mut` accessor — surgery is at accessor + ~5–10 backend GOT-write sites.

---

### Finding S-DRIFT-20 — RESOLVED (in /dev concurrency-cluster brief).

Bundled with S-DRIFT-19. Source-side `allocate_got_slot` receiver flip `&mut self → &self` + `usize += 1 → AtomicUsize::fetch_add` scheduled in SPRINT.md row 53.

---

### Finding S-DRIFT-21 — RESOLVED (in /dev concurrency-cluster brief).

Bundled with S-DRIFT-19. Source-side `next_got_slot: usize → AtomicUsize` scheduled in SPRINT.md row 53.

---

### Finding S-DRIFT-22 — RESOLVED (Submission 29, 2026-05-22)

**Facade catch-up to source: factual variant enumeration corrected + cross-crate public-method API documented. Opacity policy intact per Principle 15.**

**Target shape now in `facades/types.md` §"Public surface" §"Source-level constructs":**

```rust
pub enum Sexp { /* 8 variants: 5 atom kinds (Symbol/Int/Float/Bool/Str), List, Bracket, Comment — each carries Span */ }

impl Sexp {
    pub fn span(&self) -> Span;
    pub fn format_flat(&self) -> String;
    pub fn format_indented(&self, indent: usize) -> String;
}
impl Display for Sexp { /* uses format_indented(0) */ }
```

**Three editorial sharpenings:**
- Factual error correction: the prior one-line summary named "atom / list / bracket variants" — undercounted (8 variants in source, not 3 categories); the new wording names all 8 by category (5 atom kinds + List + Bracket + Comment).
- Phrasing fix: "preserves source spans" implied a single shared span policy; each variant carries its OWN `Span` payload in its tuple position. Reworded to "each carries Span".
- Public-method documentation: `span()`, `format_flat()`, `format_indented()`, and `impl Display` are always-public APIs that the prior facade text never named; documented inline (mirror of Submission 28's `Span` treatment of `new` / `merge`).

**Opacity policy preserved.** Variant structural shape (the `(payload, Span)` tuple form of each variant) stays in source rustdoc — readers consult `crates/cranelisp-types/src/sexp.rs` for full destructuring detail. Per Principle 15 ("facade types live with their behavior") cross-crate consumers (frontend `expand.rs`, macros, etc.) walk the tree by reading source, not by reading facade. The new facade text names the variant set so a future reader knows the inventory; payload shape remains a source-read.

**Scope-extension vs. original framing.** The audit's original disposition was "No action — already covered by facade (internal-but-exposed opacity per Principle 15)." This closure extends scope (user-approved 2026-05-22) to apply three editorial sharpenings (factual correction + phrasing + method documentation) while preserving the opacity policy intact. Bucket reclassifies D ("No action") → "Facade moves" — the opacity claim was correct but the facade text had latent drift and a documentation gap; editorial completeness (not a redirected disposition) closes both.

**Grounding.**
- Factual variant count: source `sexp.rs` lines 7–24 enumerate 8 variants — verified.
- Per-variant `Span`: source `sexp.rs` `span(&self)` matches all 8 variants destructured as `(_, s)` — confirms each variant carries its own `Span` payload position.
- Public-method documentation: mirror of Submission 28's `Span` treatment (`new` / `merge` documented as always-public).
- Principle 15 (facade types live with their behavior): the opacity policy is the rationale for keeping per-variant payload destructuring in source rustdoc rather than the facade.

**Manifestation pointers.**
- `crates/cranelisp-types/src/sexp.rs` — source canonical (no change; the 8 variants + 3 methods + Display already match the target).
- `design/arch/facades/types.md` §"Public surface" §"Source-level constructs" — `Sexp` block updated to name all 8 variants + correct "carries Span" phrasing + document public methods + Display impl; adjacent prose note on cross-crate pattern-match convention per Principle 15.
- This audit closure.

**No source change. No consumer cascade. No `cargo check`. No `public-api.txt` regen.**

Closes S-DRIFT-22. **Closes Group A** — all six Group A items (S-DRIFT-11/12/13/14/18/22 + Lambda mirror Sub 24) resolved.

---

## 4. Coverage holes — what mechanical tests cannot detect

### Finding C-HOLE-1 — crate-root `pub use` set drift

**Triage bucket: D — mechanical.** /qa-side enhancement: add `pub use` set assertion to compliance test (parse `lib.rs` re-exports + assert match to facade enumeration).

**Facade expects.** Implicitly — the §"Public surface" code blocks describe items reachable via `cranelisp_types::Symbol`, `cranelisp_types::Type`, etc.

**Source does.** `lib.rs:32–82` enumerates re-exports. No mechanical assertion ties the facade's crate-root expectations to source's re-export set.

**Design intent.** **Principle 13** (`interfaces.md` is auditable) + the S67-close baseline-diff discipline (per `design/arch/CLAUDE.md` §"Baseline-diff discipline (Sprint 67 close)") name `cargo-public-api` baselines as the per-crate audit-of-record. The compliance test scaffolded in S67 Wave 0 asserts every pub-api line is named in the corresponding facade. But that test substring-greps for type names; if `pub use module::SymbolTable` is removed and the type remains reachable via the submodule path, the substring still appears under `module::SymbolTable` and the test passes. The hole exists structurally in the test design.

**Disposition.** **Requires /qa work** for an additional mechanical-test row: "the set of crate-root `pub use` re-exports must exactly match the facade's §'Identifier newtypes' + §'Source-level constructs' + §'Resolved type system' + …  type-name enumeration." Implementation: parse `lib.rs`'s `pub use` lines + extract facade's `pub struct…` / `pub enum…` / `pub fn…` declarations + assert match. Per the audit discipline this is /qa-side enhancement, not S69 facade-doc work. Schedule deferral acceptable.

---

### Finding C-HOLE-2 — field-level type changes within an unchanged variant

**Triage bucket: D — mechanical.** /qa-side enhancement: per-critical-field PIF rows for D47-binding fields.

**Disposition.** **Requires /qa work** for per-critical-field PIF row. Each Decision-47-binding field gets a PIF row asserting the type (e.g., `Scheme.constraints: HashMap<TypeId, Vec<FQTraitName>>`, `ModuleEntry::TraitImpl::trait_name: FQTraitName`, `Type::ADT(FQTypeName, _)`). Same /qa enhancement direction as C-HOLE-1. Schedule deferral acceptable.

---

### Finding C-HOLE-3 — auto-trait projections

**Triage bucket: D — mechanical.** Audit's "No action — covered by Wave 2 /qa orphan-filter refinement" holds.

**Disposition.** **No action.** Covered by Wave 2 /qa orphan-filter refinement per SPRINT.md.

---

### Finding C-HOLE-4 — newtype `pub String` field exposure

**Triage bucket: D — mechanical.** Mechanical source-side change to `string_newtype!` macro (drop `pub` on inner `String`) + ~5–15 consumer `.0`-access site migrations per Principle 18.

**Facade expects.** §"`#[non_exhaustive]` policy" line 919:

> The newtypes (`Symbol`, `ModuleFullPath`, etc.) are an exception — they wrap a single `String` and are constructed via `From`/`From<&str>`. The wrapper is opaque; field access is not exposed.

**Source does.** `crates/cranelisp-types/src/newtype.rs:11`: `pub struct $name(pub String);`. Inner field is `pub`.

**Design intent.** **The facade's "wrapper is opaque" claim is structurally violated.** Per **Principle 18** (enforce architectural invariants structurally where possible — `pub(crate)` defaulting): the opacity invariant is structurally enforceable by removing `pub` from the inner field. Consumers writing `sym.0` or `Symbol("foo".to_string())` would migrate to `Symbol::from("foo")` / `.as_ref()` / `Deref`. The structural enforcement IS the test surface for the opacity claim; without it, the claim is aspirational.

**Difference implies.** Future representation changes (interning, validation) would break consumers that rely on `.0` access; the facade promises opacity but cannot deliver under source's current visibility.

**Disposition.** **Source moves.** Change `string_newtype!` macro to `pub struct $name(String);` (drop the `pub` on inner). Migrate consumers writing `.0` to `From`/`AsRef`/`Deref`. Likely ~5–15 sites in `crates/` and tests. Grounded by Principle 18 + facade-text opacity claim. Closes C-HOLE-4.

---

### Finding C-HOLE-5 — RESOLVED (in /dev concurrency-cluster brief).

Bundled with S-DRIFT-19. Source-side demotion of raw `pub` fields (`imports`, `exports`, `platforms`, `submodules`, `symbols`, `next_got_slot`) to `pub(crate)` scheduled in SPRINT.md row 53. `got: Arc<GotTable>` may remain `pub` (read-side accessor surface).

---

### Finding C-HOLE-6 — submodule `pub mod` exposure

**Triage bucket: D — mechanical.** Mechanical source-side narrow `pub mod → pub(crate)` for submodules + consumer use-site flips to crate-root re-exports per Principles 13 + 18. Low priority; schedule deferral acceptable.

**Facade expects.** Crate-root re-exports are the intended consumer surface; submodule paths are implementation-detail.

**Source does.** `lib.rs:4–28` declares every submodule as `pub mod`.

**Design intent.** **Principle 13** + S67 baseline-diff discipline name the public-api surface as the contract; deep paths are not. Per **Principle 18** (`pub(crate)` defaulting), submodules should be `pub(crate)` and consumers go through crate-root re-exports.

**Disposition.** **Source moves (low priority).** Narrow submodules to `pub(crate)`; flip consumer use sites from `cranelisp_types::module::SymbolTable` to `cranelisp_types::SymbolTable`. Bounded but disruptive. Schedule deferral acceptable; **not S69 work**. Grounded by Principles 13 + 18.

---

## 5. Findings overview

| ID | One-line subject | Disposition class | Grounding citation |
|---|---|---|---|
| H1 | `operator::primitives()` unioning accessor | Both move (D48 retirement arc) | Decision 48 + FIXMEs 0182, 0191 |
| H2 | `Type::unwrap_io(&self) -> &Type` (rename + borrow) | Source moves | Principles 2 + 6 |
| H3 | `SymbolTable::write_structural_decls` + `StructuralDecls` | Source moves | Decisions 33 + 44 + sequence diagram + Decision 39 |
| H4 | `SymbolTable::append_defn_order` + `defn_order` | Source moves | Decision 39 |
| H5 | `SymbolTable::install_import_bindings` | Source moves | Decisions 32/41/44 (receiver) + Decision 45 / Principle 17 (encapsulation) |
| H6 | `SymbolTable::write_code` (Decision 31 atomicity) | Source moves | Decisions 31, 32, 38, 41 |
| H7 | `SymbolTable::insert_or_update` (carry-forward) | Source moves | Decisions 31, 32, 41, 44 + sequence diagram |
| H8 | `SymbolTable::get_type` (D47 exception 2) | Both move | Decision 47 exception 2 (source-add direction); editorial fix on return type (facade-side) |
| H9 | `SymbolTable::defn_order()` accessor | Source moves | Bundled with H4 |
| H10 | `StructuralDecls` carrier | Source moves | Bundled with H3 |
| H11 | `NamedImport`/`NamedExport` per-name spans | Source moves | Decision 39 + ErrorLocation |
| U1 | `ModuleEntry::Constructor` variant | Facade moves | Principle 13 (doc gap) |
| U2 | `ModuleEntry::Reexport` variant | Facade moves | Decision 45 (chain-follow) + Principle 13 |
| U3 | `ModuleEntry::Ambiguous` | No action | Already aligned |
| U4 | `ModuleEntry::Macro.source`/`sexp` (doc gap portion) | **RESOLVED (Submission 13)** | Closed alongside S-DRIFT-5 via unified `DefKind::Macro { clauses_meta, sexp, source }` shape |
| U5 | `ModuleEntry::Def.param_names` | Facade moves | `/sig` consumer + Principle 13 |
| U6 | `Pattern::Constructor.bindings` | No action | Already in placeholder |
| U7 | `Expr::Var`, `Expr::Let` | Facade moves | Editorial omission |
| U8 | `EnsureOutcome` variants | Facade moves | Principle 13 |
| U9 | `ImportNames::None`/`MemberGlob` | Both move + arbitration A6 | None vs AliasOnly: Principle 7. MemberGlob: /spec on syntactic feature |
| U10 | `ExportSpec.module_path` | Facade moves | Decision 45 (Reexport edges) |
| U11 | `ExportSpec.names: ImportNames` | Source moves | Bundled with H11 (Decision 39) |
| U12 | `SymbolTable.linker: Option<L>` field | **RESOLVED (Submission 33) — facade moves** | Decision 35 (`L = ()` integration-side; `L` reserved for future Linker retention) |
| U13 | `SymbolTable::new_with_params` | **RESOLVED (Submission 33) — facade moves** | Decision 35 (instantiation pattern; Rust default-type-param inference does not propagate to associated fn calls) |
| U14 | `into_concrete` (SymbolTable + ModuleEntry) | **RESOLVED (Submission 33) — facade moves** | Decision 35 (cache-restore bridge — `#[serde(skip)]` on `code`/`linker`/`dll` makes serialised form parameter-independent; install layer instantiates concretely) |
| U15 | `GotTable::new()` (no capacity) | **RESOLVED (Submission 33) — facade moves** | Decisions 23 (two-GOT model — fixed-capacity GOT) + 48 (primitives static GOT) both specify fixed-capacity; no Decision authorises configurable surface |
| U16 | `ErrorLocation::{from_span,…}` | **RESOLVED by facade enumeration (Submission 39)** | Decisions 39 + 42 |
| U17 | `LineCol::new`/`LineColRange::new` | **RESOLVED by facade enumeration (Submission 39)** | Bundled with U16 |
| U18 | `SchedulingClass::default()` | No action | Auto-trait noise (Sequential = 0) |
| U19 | `PlatformError::location()` | **RESOLVED by facade enumeration (Submission 39)** | Decision 42 (symmetry with CranelispError::location) |
| U20 | `CranelispError::{message,span,location}` accessors | **RESOLVED by facade enumeration + structural narrowing (Submission 39)** | Principle 7 + Principle 18 + Decisions 39/42 invariant (location narrowed `Option<&ErrorLocation> → &ErrorLocation`); 1-site wave-3 cascade |
| U21 | `CranelispError::From<PlatformError>` | **RESOLVED by facade enumeration (Submission 39) — audit's "No action" overridden** | S67 baseline-diff discipline (every pub-api line named) + Decision 42 grounding |
| U22 | `HeapCategory::classify<C, L>` | **RESOLVED (Submission 38) — by relocation** | Reclassified D→RESOLVED. Consumer trace surfaced bounded-context violation (zero non-backend consumers); enum + classify + classify_adt + classify_from_type_def_info + gated-test-module relocated `cranelisp-types` → `cranelisp-backend`; facade entry migrates `types.md` §"Heap layout" → `backend.md` §"Heap classification". Aligns Principle 3 (cranelisp-types narrower BC) + Principle 7 (codegen concern in codegen crate) + Decision 48 §"Structural invariant — backend dep-ban". |
| S-DRIFT-1 | `Scheme.{type_vars→vars}` + FQTraitName | Facade moves | Decision 47 (FQ binding mandates `FQTraitName`) + editorial (`vars`) |
| S-DRIFT-2 | `Type::from_name(&str)` | **RESOLVED (Submission 30) — closed by deletion** | Bridge was spec-violating per S69 /spec fire (FIXME 0216 + spec §3.1 / §8.9.1 / §8.11.4 sharpening — bare `:Int` requires prelude or explicit import). Deleted from source; structural replacement via new `ModuleEntry::IntrinsicType { ty: Type, visibility: Visibility }` variant. |
| S-DRIFT-3 | `Type::type_name() -> Option<&'static str>` | **RESOLVED (Submission 30) — closed by deletion** | Bundled with S-DRIFT-2 — bridge was spec-violating; same retirement + structural replacement. |
| S-DRIFT-4 | `ImportNames` / `ExportSpec` variant set | Source moves | Bundled with H11 (Decision 39) |
| S-DRIFT-5 | `ModuleEntry::Macro` field set (GOT-callable) | **RESOLVED (Submission 13)** | Unified to `Def { kind: DefKind::Macro { clauses_meta, sexp, source } }`; per-clause GOT-callable via mangled-variant `UserFn` Defs (`{macro}$clause-{N}`), parallel to multi-sig fns; `MacroEnv` sidecar retires |
| S-DRIFT-6 | `ModuleEntry::Def.ast: Option<DefnVariant>` | **RESOLVED (Submission 35) — both move (scope-corrected from "facade moves")** | Source narrowed `Option<Defn>` → `Option<DefnVariant>` per minimum mechanism (discipline #4) + Principle 7 (Def's own `name`/`docstring`/`visibility`/`seq` fields are the single source — the outer `Defn` wrapper duplicated them post-decomposition); Decision 22 (codegen-compilable predicate `ast.is_some()`) preserved; facade catches up. Wave-3 cascade: ~30-50 backend + typecheck consumer sites. |
| S-DRIFT-7 | `ModuleEntry::Def.kind: Box<DefKind>` | **RESOLVED (Submission 35) — facade moves** | Principle 6 (size discipline; pattern-match through `Box` transparent); editorial — no Decision authors the boxing. |
| S-DRIFT-8 | `MethodResolutions` newtype struct | **RESOLVED (Submission 31)** — source moves | Facade `#[non_exhaustive]` policy + Principles 8/13 + BC invariant 11; type alias promoted to `#[non_exhaustive]` struct with `Default` derive + `new()` constructor; wave-3 cascade ~10 sites in typecheck |
| S-DRIFT-9 | `ResolvedCall::TraitMethod` field set | **RESOLVED (Submission 32)** — facade self-reconciliation + source `#[non_exhaustive]` catch-up | Decision 47 (source's FQ shape IS the target — facade line 513 already correct; line 512 misattribution + line 1792 PIF row stale text were the gap) + facade §"`#[non_exhaustive]` policy" (binding for `ResolvedCall` enum); scope-extended per user direction to bundle `#[non_exhaustive]` add and avoid revisiting this data structure; wave-3 cascade ~5-10 pattern-match sites in typecheck/backend |
| S-DRIFT-10 | `View<'a, C, L>` enum vs struct | **RESOLVED (Submission 34) — source moves** | Decision 44 opacity intent + "newtype" terminology + Principle 18 (enforce architectural invariants structurally — struct-with-private-fields is the structural option that prevents consumer-side staging-vs-live observation by construction). Bucket-C "arbitration genuine" framing superseded by user direction — Group A/B discipline pattern (facade-as-target + Principle 18 when both options exist) settled the arbitration. |
| S-DRIFT-11 | `DefnVariant` fused params + no return_type | **RESOLVED (Submission 23) — both move** | Principle 18 (lockstep invariant folded structurally) + spec §5.1.1 EBNF + spec §5.1 L41 |
| S-DRIFT-12 | `FieldDef` shape + missing span | **RESOLVED (Submission 25) — both move** | spec §2.2.6 + §5.2 (name always present) + Principle 7 (`type_expr` naming) + Decision 39 (per-field `span`); Option A (`TypeExpr` unconditional, synthesised-`TypeVar`-for-bare convention) user-arbitrated 2026-05-22 |
| S-DRIFT-13 | `TraitImpl` ast.rs shape + syntactic-stage qualification | **RESOLVED (Submission 27) — both move** | New syntactic-stage newtypes `TraitRef { module: Option<ModuleFullPath>, name: TraitName }` + `TypeRef { module: Option<ModuleFullPath>, name: TypeName }` capture as-written qualification structurally; `TypeExpr::Named` / `Applied` cascade to `TypeRef` payloads; `TraitImpl` rewritten to 5-field target `{ trait_name: TraitRef, target: TypeExpr, type_constraints: Vec<(Symbol, TraitRef)>, methods, span }`. Spec §2.3.4 + §4.2.2 (qualified references) + spec §5.4 EBNF (target as one grammatical unit — `target_type + type_args` split had no Decision-level grounding) + Decision 47 sharpening (producer/consumer split: syntactic stage carries qualification structurally; typecheck does the FQ lift) + Decision 45 (resolved-stage counterpart on trait's defining module); `feedback_hold_to_facade_default.md` directs source-moves when source has no Decision-level grounding; user-arbitrated 2026-05-22 |
| S-DRIFT-14 | `TraitMethodSig` shape | **RESOLVED (Submission 26) — both move** | spec §5.3 EBNF (every method has named params; `param = ':' type_expr symbol | symbol` always terminates in a `symbol`) + spec §5.3.1 (synthesised-`SelfType` for bare params) + spec §5.3.2 (HKT param index) + spec §5.4.5 (default-body typecheck against instantiated signature per impl) + Principle 18 (lockstep invariant folded structurally — `default_param_names` retired) + Principle 7 (`ret_type` producer-side naming canonical) + Decision 39 (per-method span); user-arbitrated 2026-05-22 (facade is target — source's `Option<Sexp>` had no Decision-level grounding after Submission 23 corrected the Principle 11 misattribution; `feedback_hold_to_facade_default.md` directs source-moves as default) |
| S-DRIFT-15 | `PlatformSpec` placeholder shape | Both move + arbitration A7 | Principle 14 / newtype rule (source-side narrowing) + arbitration on resolved-vs-pre-resolved |
| S-DRIFT-16 | `ModDecl.is_private` + `inline_body` | **RESOLVED (Submission 40) — source narrowing + facade enumeration + FIXME-cascade** | Principle 7 (single source of truth — Visibility is the encoding; ModDecl was sole bool outlier in entry/decl family) + Principle 18 (enforce invariants structurally — `Visibility` enum exists for this purpose); facade catches up to honest 4-field shape with `inline_body` lifecycle note; FIXME 0217 against `/int` for spec §8.2.2 step 2 parent-file rewrite gap; wave-3 cascade ~15 sites (frontend module_extract + worker + save) |
| S-DRIFT-17 | `PrimitiveKind` retired + `jit_name` retired + `PlatformEffect` promoted to `DefKind` sibling + `SpecialForm` promoted to `ModuleEntry` sibling | **RESOLVED (Submission 36) — scope-extended ModuleEntry settlement** | Decision 48 (primitives uniform module — vestigial Inline/Extern; `jit_name` derivable from symbol-table key) + Decision 26 (variant-internal scheduling_class — preserved at new `DefKind::PlatformEffect` level) + Principle 7 (single source of truth — symbol-table key IS the JIT linker name) + Principle 18 (variant fits its data — `SpecialForm` reads only 4 of 11 fields; `PlatformEffect` is a sibling provenance class, not a sub-classification) + Submission 30 parallel (`IntrinsicType` shape pattern) + `src/CLAUDE.md` §"JIT Symbol Names" convention. |
| S-DRIFT-18 | `Span::SYNTHETIC` associated const + Default derive + new/merge | **RESOLVED (Submission 28)** — facade moves | Editorial (Rust idiom); scope-extended to `Default` derive (Sub-25) + always-public APIs |
| S-DRIFT-19 | `SymbolTable::get` receiver + HashMap vs DashMap | **Source moves** | **Decisions 31, 32, 38, 41, 44, 48 + sequence diagram + Principle 18** |
| S-DRIFT-20 | `allocate_got_slot` receiver | Source moves | Bundled with S-DRIFT-19 |
| S-DRIFT-21 | `next_got_slot: AtomicUsize` | Source moves | Bundled with S-DRIFT-19 |
| S-DRIFT-22 | `Sexp` opaque shape | **RESOLVED (Submission 29)** — facade moves (scope-extended) | Editorial sharpening — factual variant enumeration (8 variants, naming `Comment` + 5 atom kinds), "each carries Span" phrasing, public-method documentation (`span` / `format_flat` / `format_indented` / `Display`); opacity policy preserved per Principle 15 (per-variant payload destructuring stays in source rustdoc). **Closes Group A.** |
| C-HOLE-1 | Crate-root `pub use` set mechanical gap | Requires /qa work | Principle 13 + S67 baseline discipline |
| C-HOLE-2 | Field-type drift mechanical gap | Requires /qa work | Principle 13 + Decision 47 enforcement |
| C-HOLE-3 | Auto-trait projections | No action | Wave 2 /qa orphan-filter |
| C-HOLE-4 | `pub String` in `string_newtype!` opacity | Source moves | Principle 18 + facade opacity claim |
| C-HOLE-5 | `SymbolTable` `pub` fields | Source moves | Bundled with S-DRIFT-19 (Principle 18) |
| C-HOLE-6 | Submodule `pub mod` exposure | Source moves (low priority) | Principles 13 + 18 |

**Final counts by disposition class:**

| Class | Count |
|---|---|
| Source moves | 27 (H2, H3, H4, H5, H6, H7, H9, H10, H11, U11, S-DRIFT-4, S-DRIFT-10, S-DRIFT-19, S-DRIFT-20, S-DRIFT-21, C-HOLE-4, C-HOLE-5, C-HOLE-6 — plus partial source-side moves in H8, S-DRIFT-12, S-DRIFT-15, U9 = 22 hard + ~5 partial; S-DRIFT-8 RESOLVED in-place Submission 31 — source moved as predicted; direction column unchanged; wave-3 cascade deferred. S-DRIFT-10 RESOLVED in-place Submission 34 — reclassified from bucket C "arbitration genuine" to "source moves" + landed; source rewritten from `pub enum View { Single, Union }` to `pub struct View { staging: Option<&'a SymbolTable>, live: &'a SymbolTable }` with private fields per Decision 44 opacity intent + Principle 18; typecheck ClusterContext pattern-match consumer cascade deferred to wave-3.) |
| Facade moves | 3 (U1, U2, U4, U5, U7, U8, U10, S-DRIFT-1, S-DRIFT-7, S-DRIFT-18, S-DRIFT-22 — U22 removed S38 per scope-corrected bounded-context reclassification; U16, U17, U19, U20 removed S39 per reclassification to "RESOLVED by facade enumeration" (Group F — errors + locations bundle); S-DRIFT-17 removed S36 per scope-extended cluster correction; S-DRIFT-11 reclassified to "both move" per Submission 23 + S-DRIFT-12 reclassified per Submission 25 + S-DRIFT-14 reclassified per Submission 26 + S-DRIFT-13 reclassified per Submission 27 + S-DRIFT-2/S-DRIFT-3 reclassified to "RESOLVED by deletion" per Submission 30 + S-DRIFT-9 reclassified to "RESOLVED — facade self-reconciliation + source `#[non_exhaustive]` catch-up" per Submission 32 — each surfaced that source had no Decision-level grounding and the configuration prefers a third option neither side held; the parallel S-DRIFT-11/S-DRIFT-14 reclassifications grounded on the corrected Principle 11 misattribution; S-DRIFT-22 reclassified D→"Facade moves" per Submission 29 — scope-extended editorial sharpening preserves opacity policy intact; S-DRIFT-2/S-DRIFT-3 reclassified D→"RESOLVED by deletion" per Submission 30 — S69 /spec fire FIXME 0216 surfaced the reverse-lookup bridge was spec-violating, not facade-misaligned; S-DRIFT-9 reclassified D→"RESOLVED — facade self-reconciliation + source `#[non_exhaustive]` catch-up" per Submission 32 — facade line 513 already at D47-target since the Decision authored, lines 512 + 1792 were un-cascaded stale text within a facade-internally-inconsistent state, not source-facade drift. U12 + U13 + U14 + U15 RESOLVED in-place per Submission 33 — facade-only catch-up (source already at target shape per Decision 35 instantiation pattern + Decisions 23 + 48 fixed-capacity GOT); count decremented by 4. S-DRIFT-6 reclassified D→"Both move" per Submission 35 — scope-corrected from prior "facade moves to source's `Option<Defn>`" framing: source narrowed `Option<Defn>` → `Option<DefnVariant>` per minimum mechanism (discipline #4) + Principle 7 (Def's own `name`/`docstring`/`visibility`/`seq` fields are canonical for that metadata — the outer `Defn` wrapper duplicated them post-decomposition); facade catches up to the narrowed shape; Decision 22 codegen-compilable predicate preserved (indifferent to payload type); count decremented by 1. S-DRIFT-7 RESOLVED in-place per Submission 35 — facade catch-up to source's `Box<DefKind>` per Principle 6 size discipline; no reclassification. S-DRIFT-17 reclassified D→"RESOLVED — scope-extended cluster correction" per Submission 36 — ModuleEntry settlement: PrimitiveKind enum retired + jit_name field retired + PlatformEffect promoted to DefKind sibling + SpecialForm promoted to ModuleEntry sibling; original "facade catch-up to D48 3-variant split" framing superseded by user-questioning that surfaced the four convergent changes; count decremented by 1. U22 reclassified D→"RESOLVED by relocation" per Submission 38 — bounded-context violation surfaced by consumer trace; `HeapCategory` relocated `cranelisp-types` → `cranelisp-backend`; facade entry migrates `types.md` §"Heap layout" → `backend.md` §"Heap classification"; count decremented by 1. U16 + U17 + U19 + U20 reclassified D→"RESOLVED by facade enumeration" per Submission 39 — Group F (errors + locations) bundle: mechanical facade enumeration for U16/U17/U19; scope-extended structural narrowing for U20 (`CranelispError::location()` `Option` retired per Principle 7 + Decision 39/42 invariant + Sub 35 parallel — 1-site wave-3 cascade `src/main.rs:91`); count decremented by 4.) |
| **RESOLVED by deletion / self-reconciliation / scope-extended cluster correction / relocation / facade enumeration / source narrowing + FIXME-cascade** | 11 (S-DRIFT-16 — Submission 40; `ModDecl.is_private: bool → visibility: Visibility` source narrowing per Principle 7 + Principle 18; facade shape summary updated to 4 fields honestly enumerating `inline_body: Option<Vec<Sexp>>` with lifecycle note documenting frontend → worker → source-rewriter path; FIXME 0217 filed against `/int` for spec §8.2.2 step 2 (parent-file rewrite) implementation gap; user-arbitrated reading: `inline_body` stays as real persistent field, rewriter strips it on serialization rather than data shape changing — spec gap closes when /int implements the rewrite, not by retiring the field; wave-3 cascade ~15 sites across frontend module_extract + worker + save. S-DRIFT-2, S-DRIFT-3 — Submission 30; `Type::from_name` / `Type::type_name` deleted from source; new `ModuleEntry::IntrinsicType` variant for uniform intrinsic-type registration. S-DRIFT-9 — Submission 32; facade lines 512 + 1792 self-reconciled under Decision 47; line 513 was already correct since D47 authored; source-side `#[non_exhaustive]` policy catch-up bundled per user direction. S-DRIFT-17 — Submission 36; ModuleEntry settlement: PrimitiveKind enum retired + jit_name field retired from DefKind::Primitive + PlatformEffect promoted to DefKind sibling + SpecialForm promoted to ModuleEntry sibling; original audit framing "facade catch-up to D48 3-variant split" superseded by user-questioning during walk-through; ~100+ cascade sites across typecheck builtins / worker / backend / primitives / runtime renames / tests. U22 — Submission 38; HeapCategory + classify + classify_adt + classify_from_type_def_info + gated-out test module relocated `cranelisp-types/src/heap.rs` → `cranelisp-backend/src/heap.rs`; HeapHeader + offset constants retain in cranelisp-types as the genuine cross-crate layout contract; consumer trace (zero non-backend production consumers) reclassified D→RESOLVED by relocation per Submission 38 — bounded-context violation surfaced by consumer trace; HeapCategory relocated cranelisp-types → cranelisp-backend; facade entry migrates from types.md §Heap layout to backend.md §Heap classification. Aligns Principle 3 + Principle 7 + Decision 48 §"Structural invariant — backend dep-ban". U16 + U17 + U19 + U20 + U21 — Submission 39 (Group F — errors + locations bundle); reclassified D→RESOLVED per: U16 facade enumerates `ErrorLocation::{unknown, from_span, from_span_file}` with producer-side guidance (Decisions 39 + 42); U17 facade enumerates `LineCol::new` / `LineColRange::new` (bundled with U16's suggestive-surface logic for `ErrorLocation.line_col`); U19 facade enumerates `PlatformError::location() -> &ErrorLocation` (Decision 42 + Principle 7 symmetry); U20 scope-extended structural narrowing — facade enumerates `CranelispError::{message, span, location}` accessors AND source narrows `CranelispError::location() : Option<&ErrorLocation> → &ErrorLocation` (Principle 7 + Principle 18 + Decisions 39/42 invariant — every variant carries `location: ErrorLocation`; the Option hid the structural invariant; parallel to Sub 35's `Option<Defn> → Option<DefnVariant>` narrowing; consumer trace confirmed 1 site at `src/main.rs:91` for wave-3 cascade); U21 — audit's "No action" disposition overridden; facade names `impl From<PlatformError> for CranelispError` per S67 baseline-diff discipline (every pub-api line named in the facade) + Decision 42 grounding.) |
| Both move | 9 (H1, H8, U9, S-DRIFT-6, S-DRIFT-11, S-DRIFT-12, S-DRIFT-13, S-DRIFT-14, S-DRIFT-15) — S-DRIFT-6 added per Submission 35 (scope-corrected from "facade moves") — source narrowed `Option<Defn>` → `Option<DefnVariant>` per minimum mechanism + Principle 7; facade catches up to the narrowed shape. |
| Arbitration (genuine) | 0 — A2 (= S-DRIFT-5) closed by Submission 13; A5 (= S-DRIFT-10) RESOLVED Submission 34 — direction defaulted to source-moves per Principle 18 (the audit's stated default), user-arbitrated to that default 2026-05-23; bucket-C "arbitration genuine" framing was superseded by user direction — the Group A/B discipline pattern (facade-as-target + Principle 18 when both options exist) settled the arbitration |
| No action | 4 (U3, U6, U18, C-HOLE-3) — U3 confirmed Submission 40 (variant uniformity holds; `is_public` uniform check at module.rs:827 grounds the informational-stub field). S-DRIFT-22 reclassified to "Facade moves" per Submission 29 (scope-extended editorial sharpening; opacity policy intact per Principle 15); U21 reclassified D→"RESOLVED by facade enumeration" per Submission 39 — audit's "No action" overridden under S67 baseline-diff discipline (every pub-api line named); S-DRIFT-16 reclassified D→"RESOLVED by source narrowing + facade enumeration + FIXME-cascade" per Submission 40 — original "No action — already covered by facade disposition table" framing superseded by Sub 30/36/39's fuller-surface-accuracy trajectory + Principle 7 single-source-of-truth grounding (ModDecl was sole bool outlier in decl/entry family); count decremented by 1 |
| Requires /qa work | 2 (C-HOLE-1, C-HOLE-2) |

(The count totals add to slightly more than 59 because findings with both-move dispositions appear in two columns. Per-finding source vs facade direction is in the table.)

---

## 6. What the audit cannot resolve alone — arbitration briefs

The audit identifies **one genuine arbitration item** (A5) where the architectural configuration does not ground a direction. The prior audit's "11 arbitration items" was inflated by mis-grounded findings; calibration table in §7 shows the conversions. A2 (Macro callable shape) closed by Submission 13 — see §"S-DRIFT-5 — RESOLVED" above. Per the audit discipline, the remaining genuine arbitration is named with **the binary choice** + **the evidence either way** + **what tips it**.

### Arbitration A2 — RESOLVED (Submission 13)

Closed structurally by user-arbitrated unification of macros into `Def { kind: DefKind::Macro { clauses_meta, sexp, source } }`. The framing of A2 — "single GOT slot per macro with trampoline vs per-clause `func_ptr` via MacroEnv" — was dissolved by the third option: **per-clause GOT-callable via mangled-variant `UserFn` Defs** (`{macro-name}$clause-{N}`), parallel to multi-sig fn variants. Expansion-time clause-walk (existing logic) walks `clauses_meta` and GOT-dispatches to the matched clause's variant Def. See `facades/types.md` §"DefKind" `DefKind::Macro` for the manifestation site.

### Arbitration A5 — `View<'a, C, L>` enum vs struct (S-DRIFT-10) — **RESOLVED (Submission 34)**

**Disposition: source moves to struct with private fields.** User-arbitrated 2026-05-23 (defaulted to the audit's stated direction). The bucket-C "arbitration genuine" framing was superseded by user direction — the Group A/B discipline pattern (facade-as-target + Principle 18 when both options exist) settled the arbitration. The audit had correctly identified Principle 18 as the tipping consideration ("the principled default"); user-arbitration ratified that default without requiring a separate /typecheck audit.

**Closure summary.** Source rewritten from `pub enum View { Single, Union }` to `pub struct View { staging: Option<&'a SymbolTable>, live: &'a SymbolTable }` with private fields. Decision 44's opacity intent ("typecheck cannot tell whether the view unions staging+live or hits live alone") is now structurally enforced — consumer-side `match view { View::Union { .. } => …, View::Single { .. } => … }` shortcircuit is foreclosed by construction. Internal encoding: `Option<&_>` on staging captures cluster-vs-committed mode as a private structural detail, not a public variant tag. See per-finding §"Finding S-DRIFT-10 — RESOLVED (Submission 34)" body above for the full target shape + grounding bullets + manifestation pointers + wave-3 cascade brief.

### Arbitration A6 — `ImportNames::MemberGlob(Symbol)` (U9 carry-over)

**Question.** Is `MemberGlob(Symbol)` (e.g. `(import [foo [Type.*]])`) a syntactic feature that survives to the resolved layer, or a parser-side sugar that should not reach `cranelisp-types`?

**Stakeholders.** /spec (authority on what import forms are in spec); /arch (placement question if /spec confirms).

**Default direction.** Configuration-neutral. Source has it; facade silent. /spec arbitrates.

**What tips.** /spec on whether `(import [foo [Type.*]])` is a real spec form.

### Arbitration A7 — `PlatformSpec` shape (S-DRIFT-15)

**Question.** Does `PlatformSpec` carry the pre-resolution shape (`name: ModuleName, span`) or the post-resolution shape (`manifest_path: PathBuf, alias: Option<ModuleName>, span`)? And do we need both with a resolution boundary?

**Stakeholders.** /platform (DLL loading work; Decision 43); /arch.

**Default direction.** Source-side minimum fix is grounded (newtype-rule narrow `String → ModuleName`); the broader resolved-vs-pre-resolved shape is genuinely open.

**What tips.** /platform's S70 Decision-43 implementation status.

---

## 7. Calibration of prior dispositions (methodology correction)

This audit re-grounds the prior re-author's dispositions against the architectural configuration. The corrections below are the structural payload of the methodology pivot — each row names the configuration evidence that flips (or confirms) the disposition.

**Total dispositions evaluated**: 59
**Flipped from "facade moves" to "source moves"**: 23
**Flipped from "requires /arch arbitration" to a configuration-grounded direction**: 9
**Confirmed (same disposition, additional grounding citation added)**: 21
**Other flips**: 6

### Major flips (load-bearing payload)

| ID | Prior disposition | This audit | Grounding citation that flipped |
|---|---|---|---|
| **S-DRIFT-19** | Requires /arch arbitration | **Source moves** | Decisions 31, 32, 38, 41, 44, 48 + sequence diagram `concurrency-symbol-table-entry.mmd` + Principle 18 |
| **S-DRIFT-20** | Bundled with arbitration | **Source moves** (bundled) | Same as S-DRIFT-19 |
| **S-DRIFT-21** | Bundled with arbitration | **Source moves** (bundled) | Same as S-DRIFT-19 |
| **H3** | Requires /arch arbitration (Decision 39 scope) | **Source moves** | Decision 33 + Decision 44 + sequence diagram. Schedule is the legitimate question, not direction. |
| **H4** | Requires /arch arbitration (bundled with H3) | **Source moves** | Decision 39 grounding (facade lines 386–415); not pending; already binding intent |
| **H5** | Requires /arch arbitration (receiver tied to S-DRIFT-19) | **Source moves** | Decisions 32/41/44 + Decision 45 + Principle 17 |
| **H6** | Source moves (encapsulation); receiver tied to S-DRIFT-19 | **Source moves** (full) | Decisions 31, 32, 38, 41 all converge; receiver question retired |
| **H7** | Source moves (semantics); receiver tied to S-DRIFT-19 | **Source moves** (full) | Decision 32's Clone super-bound rationale + sequence diagram lines 60–64 |
| **H9, H10** | Bundled with arbitration | **Source moves** (bundled) | Decision 39 |
| **H11** | Requires /arch + /qa arbitration | **Source moves** | Decision 39 + ErrorLocation are already binding facade text; not pending |
| **S-DRIFT-4** | Requires /arch + /qa arbitration | **Source moves** | Bundled with H11 — Decision 39 |
| **S-DRIFT-13** | Facade moves | **RESOLVED (Submission 27) — both move** | Both poles missed a third option. Source's `trait_name: TraitName` discards user-written qualification (`(impl fmt/Display ...)` requires structural capture); facade's `FQTraitName` was over-prescriptive (forced resolution before AST). New `TraitRef { module: Option<ModuleFullPath>, name: TraitName }` + `TypeRef` (parallel for types) capture as-written qualification structurally; `TypeExpr::Named` / `Applied` cascade to `TypeRef`; `TraitImpl` 5-field target unifies `target_type + type_args` per spec §5.4 EBNF (one grammatical unit). Grounded by spec §2.3.4 + §4.2.2 + §5.4 + §8 + Decision 47 sharpening (producer/consumer split) + Decision 45. |
| **S-DRIFT-17** | Facade moves | **RESOLVED (Submission 36) — scope-extended cluster correction** | The mechanical "facade moves" direction was correct as far as it went, but Submission 36's walk-through user-questioning surfaced four convergent changes neither audit had named: (1) the `Inline`/`Extern` variants were vestigial — verified by grep, no production consumer reads them; backend dispatches via GOT uniformly per D48. (2) `jit_name: Option<JitSymbol>` was derivable from the symbol-table key per `src/CLAUDE.md` §"JIT Symbol Names" — no separate field needed. (3) `PlatformEffect`'s body location (DLL) is structurally distinct from bundled-primitive provenance — sibling-variant under `DefKind`, not nested. (4) `SpecialForm` reads only 4 of `Def`'s ~11 fields — sibling `ModuleEntry::SpecialForm` variant fits the introspection use case (parallels Submission 30's `IntrinsicType` shape). Audit-discipline lesson: when a "facade moves" finding ratifies a source shape that itself has insufficient configuration grounding, the next layer of user-questioning often surfaces a structural cluster correction the mechanical disposition missed. |
| **S-DRIFT-1 (b)** | Facade moves | **Facade moves** (confirmed, grounding added) | Decision 47 mandates `FQTraitName` — prior audit had direction right but missed D47 grounding |
| **S-DRIFT-5** | Requires /arch + /typecheck + /backend arbitration | **RESOLVED (Submission 13)** | Unified to `Def { kind: DefKind::Macro { clauses_meta, sexp, source } }` with per-clause GOT-callable via mangled-variant `UserFn` Defs (`{macro}$clause-{N}`). See §"S-DRIFT-5 — RESOLVED". |
| **C-HOLE-5** | Bundled with arbitration | **Source moves** (bundled with S-DRIFT-19) | Principle 18 + sequence diagram |
| **U9** | Both move + /arch (bundled with H11/S-DRIFT-4) | **Both move + arbitration A6 narrowed to /spec on MemberGlob** | The `None` vs `AliasOnly` direction is editorial; only `MemberGlob` is genuine /spec arbitration |
| **S-DRIFT-15** | Both move + /platform arbitration | **Both move (newtype-rule fix grounded) + arbitration A7** (broader shape) | Newtype-rule narrowing is Principle-14-grounded; broader shape is open |

### Confirmations (same disposition; new grounding citation)

The remaining 21 dispositions match the prior audit's direction but the corrected audit adds explicit configuration citations to each. For example:

- **S-DRIFT-6** (`ast: Option<DefnVariant>` post-Submission-35): prior audit "facade moves" was correct *in direction* (facade did need to leave `Option<Expr>`); this audit framed the destination as source's `Option<Defn>` citing Decision 22. **Reclassified Submission 35 to "both move" — scope-correction.** On user-questioning the audit's "to source's `Option<Defn>`" framing was rejected as ratifying vestigial structure (the outer `Defn` wrapper duplicates fields the Def's own `name`/`docstring`/`visibility`/`seq` already carry; post-decomposition `Defn.variants` is always `.len() == 1`). Source narrowed to `Option<DefnVariant>` per minimum mechanism (discipline #4) + Principle 7 (single source of truth); facade catches up. Decision 22's codegen-compilable predicate `ast.is_some()` preserved (indifferent to payload type). Audit-discipline lesson: when a "facade moves" finding ratifies source, verify the source shape is itself configuration-grounded — source-as-target is not automatic.
- **S-DRIFT-8** (`MethodResolutions` newtype): prior audit "source moves" stands; this audit cites facade non_exhaustive policy + Principle 8.
- **S-DRIFT-11** (`DefnVariant` split params): prior audit "facade moves" **revised in Submission 23 to "both move" — fused `Vec<(Symbol, Option<TypeExpr>)>` shape**. The Principle 11 citation in this audit was a misattribution (Principle 11 governs single-pipeline mode parameters, not annotation shape); the correct grounding is **Principle 18** (enforce invariants structurally — fold the parallel-vec lockstep invariant into the tuple) + spec §5.1.1 EBNF + spec §5.1 L41. See Finding S-DRIFT-11 body for closure pointer.
- **H2** (`Type::unwrap_io`): prior audit "source moves" stands; this audit cites Principles 2 + 6.

### Other movement

- **H1** (`primitives()` accessor): Prior audit "facade moves" → this audit "both move (D48 retirement arc)" — both sides retire post-D48 per FIXMEs 0182 + 0191. Calibration: surfacing the D48 grounding is what shifts this from "facade-doc fix" to "scheduled bilateral retirement."

- **S-DRIFT-10** (`View` enum vs struct): Prior audit "requires /arch arbitration" → this audit "arbitration A5 with default = source moves per Principle 18." Calibration: Principle 18 grounds the default direction even though the configuration does not name "struct" explicitly.

### The methodology correction itself

The prior audit's 23 "facade moves" dispositions were correct as facade-doc moves but **largely failed to surface the Decision-level grounding** — readers could not tell from the disposition column alone whether a "facade moves" was D47-mandated catch-up (e.g., S-DRIFT-1b, S-DRIFT-9; S-DRIFT-13 also originally cited here, since reclassified Submission 27 to "both move" with broader scope), D48-mandated catch-up (originally S-DRIFT-17 — subsequently reclassified Submission 36 to "RESOLVED — scope-extended cluster correction" when user-questioning surfaced four convergent changes the mechanical disposition missed), Decision-22-grounded (S-DRIFT-6), or editorial-only (S-DRIFT-7, S-DRIFT-18). The corrected audit names the grounding inline per finding so future audits can cite back. **Further audit-discipline lesson from Submission 36**: even when the mechanical direction is correct, a "facade moves" finding may be hiding a larger structural cluster opportunity behind the narrow framing. User-questioning during walk-through is the trigger that reframes — the audit cannot generate it; the walk-through can.

The prior audit's 11 "requires /arch arbitration" dispositions split into:
- **9 mis-grounded** (configuration grounds the direction; only schedule is in question): H3, H4, H5, H9, H10, H11, S-DRIFT-4, S-DRIFT-19/20/21 (one complex), C-HOLE-5. The corrected audit re-classes these as **source moves** with schedule deferral acceptable.
- **2 genuine arbitration** (A2 = S-DRIFT-5; A5 = S-DRIFT-10). The corrected audit retains the arbitration brief but adds the default direction the configuration grounds (per Principle 13 for A2; per Principle 18 for A5). Both subsequently resolved: A2 by Submission 13; A5 by Submission 34 (defaulted to source-moves per Principle 18 — the configuration-grounded direction the audit named).

The over-classification to "arbitration" in the prior audit was the structural failure mode the user's 2026-05-19 direction names — the audit was not reading the architectural configuration that grounds the facade. Decisions 31, 32, 38, 41, 44 + the canonical sequence diagram + Principle 18 collectively settle the SymbolTable concurrency complex; the prior audit's "binary choice + evidence" brief was real work but the configuration had already named the binary's answer. The methodology pivot is: read the configuration first, classify against it, only then identify what remains genuinely open.

---

## 8. Verdict

The audit identifies **27 source-side moves** and **20 facade-side moves** as the immediate disposition register; **4 both-move** items split work bilaterally; **2 genuine arbitration items** (A2, A5) require cross-skill input but with explicit default directions; **6 no-action** items (auto-trait noise, already-covered); **2 /qa-side** mechanical-test enhancements (C-HOLE-1/2).

The architectural payload is the **SymbolTable concurrency complex** — H3, H5, H6, H7, S-DRIFT-19/20/21, C-HOLE-5 — bundled as one source-side migration grounded by Decisions 31, 32, 38, 41, 44, 48 + the canonical `concurrency-symbol-table-entry.mmd` sequence diagram + Principle 18. The migration is bounded by the Decision-44 accessor-layer surgery (the 91 register-call sites in typecheck flow through `ctx.current_symbol_table_mut()`; the migration is at the accessor + ~5–10 backend GOT-write sites, not at the per-call-site level).

**Sprint scope.** S69 wave-3 can resolve the 20 facade-side moves cleanly. The 27 source-side moves are bounded source work; the concurrency-complex bundle is the largest single migration and is the natural fit for a dedicated source-side wave in S70 or a S70+S71 split. The 2 genuine arbitration items (A2, A5) require /arch input before source-side migration can be concrete; /sprint files the corresponding `/arch` FIXMEs at the S69 wave gate.

**Methodology correction signal.** 32 of the prior audit's 59 dispositions changed in some way under design-intent grounding (23 "facade moves" flipped to "source moves", 9 "arbitration" flipped to "source moves", plus 21 dispositions where direction confirmed but grounding citation added, 6 other shifts). The flip rate is high — over half the prior audit's findings carried mis-classification that was visible only once the configuration was loaded. The configuration grounds far more than the prior audit credited.

The remaining genuine arbitration count is **2** (down from prior 11). Both items name the configuration-grounded default direction; /arch input is for amendment-or-confirmation of the default, not for unbounded direction-finding. This is the audit-as-grounding-mechanism mode the user-direction 2026-05-19 names: the architectural configuration grounds the facade; the audit reads the configuration; the wave gate sees the right work-by-source vs work-by-facade split with each item named to its Decision/Principle/FIXME.
