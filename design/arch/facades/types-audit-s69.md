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

- **Decision 48 `PrimitiveKind { Inline | Extern | PlatformEffect }`** (S-DRIFT-17). The facade text post-S68 close was supposed to be updated; verification: facade still names `{ Builtin, PlatformEffect }` (lines 547–551). **Source's `{ Inline, Extern, PlatformEffect }` IS the Decision 48 target state** (Decision 48 names "Inline" as the Cranelift-IR-emitted-inline-at-callsite category and "Extern" as the GOT-dispatched-via-primitives-crate category; the §"Shape" code blocks in Decision 48 spell it out). Disposition: **facade moves** — but the move is *D48-mandated catch-up*, not facade-author preference. The prior audit had this right (disposition class) but mis-framed the rationale.

- **Per-name spans on imports/exports** (H11, S-DRIFT-4, S-DRIFT-12, U9, U10, U11). Facade names `NamedImport { name, span }` / `NamedExport { name, span }` + per-field span on `FieldDef`. Source has `Vec<Symbol>` + no per-field span. **The grounding is Decision 39** (per-defn source coordinate system; ErrorLocation per Decision 42). The facade's per-name spans are the structural prerequisite for the diagnostic-quality bar Decision 39 names. The prior audit framed this as "requires /arch arbitration on whether Decision 39 lands in S70" — but **Decision 39 isn't pending; it's already grounded in `ErrorLocation` (facade lines 759–804) and the per-defn-source plumbing**. The facade is target-stating per Decision 39. Disposition: **source moves**. Schedule is a separate question and is acceptable to defer; the disposition is not.

- **`get_type` return type** (H8). Facade: `Option<&TypeDef>`. Source has no `get_type` method. There IS a `TypeDefInfo` struct in source `check.rs`. The facade's name "`TypeDef`" without further qualification is a facade-text artefact — there is no Decision authoring a separate `TypeDef` newtype distinct from `TypeDefInfo`. **Disposition split**: source adds the method (per Decision 47 exception 2 — receiver-pinned); facade aligns the return type to source's `TypeDefInfo` (mechanical facade fix; no Decision authorising a separate `TypeDef`).

- **`SymbolTable.next_got_slot`** (S-DRIFT-21). Facade: `AtomicUsize`; source: `usize`. **Decision 32's Clone super-bound rationale + the concurrency sequence diagram + Decision 44's "per-entry under inner-DashMap locks" all premise concurrent slot allocation.** The atomic IS the target. Disposition: **source moves**, bundled with S-DRIFT-19.

- **`HeapCategory::classify` signature** (U22). Facade silent. Source declares `classify<C, L>(ty, Option<&DashMap<…, SymbolTable<C, L>>>)`. **Configuration check**: no Decision either authorises or retracts this surface. The function exists; backend consumes it. The facade silence is a documentation gap. Disposition: **facade moves** — but this is purely documentary catch-up, not a structural question.

Disposition class counts (59 findings):

| Class | Count | Meaning |
|---|---|---|
| **Source moves** (facade is target-stating per Decision / Principle / FIXME) | **27** | Source migration is owed. Wave 3+ source work. |
| Facade moves (facade text is stale, was sloppy, or source has evolved with retroactive Decision agreement) | 16 | Mechanical facade updates. Wave 2 facade-doc work. (Reduced by 4 across S23/S25/S26/S27 reclassifications — each surfaced that source's shape had no Decision-level grounding and the configuration prefers a third option neither side held.) |
| Both move | 8 | Each side adjusts; neither is wholly correct. (S-DRIFT-11 S23, S-DRIFT-12 S25, S-DRIFT-14 S26, S-DRIFT-13 S27 reclassifications + 4 prior.) |
| Arbitration — genuine cross-skill question the configuration does not ground | 1 | A5 (View enum-vs-struct opacity). A2 closed by Submission 13 — see "Macro callable shape" bullet above. |
| No action (auto-trait noise, already-covered) | 6 | Per audit discipline still gets a one-sentence rationale. |

**Prior re-author disposition flips**: 23 of the prior audit's "facade moves" recommendations are flipped to **source moves** under design-intent grounding. The calibration table in §7 enumerates them.

The configuration is unambiguous on the SymbolTable concurrency complex, on FQTypeName binding, on Decision 48's PrimitiveKind, and on Decision 39's per-name spans. The audit names them as source-moves, and the wave-gate question for /sprint is only **scheduling** (S69 wave-3, S70, or later), not **direction**. The configuration is genuinely ambiguous in only two places (A2, A5).

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
| U3 | D | Audit's own disposition is "No action — already aligned"; nothing to do. |
| U10 | A | Walk row 348 — `U10 + alias-symmetry` resolved; `ExportSpec` gains `alias` + structurally identical to `ImportSpec`. |
| U11 | A | Bundled with H11 (walk row 347). |
| U12 | D | Facade-side documentation catch-up — add `linker: Option<L>` field to shape summary per Decision 35. |
| U13 | D | Facade-side documentation catch-up — enumerate `new_with_params` constructor per Decision 35. |
| U14 | D | Facade-side documentation catch-up — enumerate `into_concrete` conversions per Decision 35 (cache-restore). |
| U15 | D | Facade-side fix — drop `(capacity: usize)` from `GotTable::new()` to match fixed-capacity source. |
| U16 | D | Facade-side enumeration — name three `ErrorLocation` constructors per Decisions 39 + 42. |
| U17 | D | Facade-side enumeration — name `LineCol::new` / `LineColRange::new` (bundled with U16). |
| U18 | D | Audit's disposition is "No action — auto-derive Default::default() = Sequential". |
| U19 | D | Facade-side enumeration — add `PlatformError::location()` accessor per Decision 42 symmetry. |
| U20 | D | Facade-side enumeration — name `CranelispError::{message, span}` accessors. |
| U21 | D | Audit's disposition is "No action — derived From impl is auto-trait noise". |
| U22 | D | Facade-side enumeration — add `HeapCategory::classify` signature with two-mode contract documentation. |
| S-DRIFT-1 | A | Walk rows 339+340 — (a) source-side `vars → type_vars` rename + (b) facade-side `Vec<TraitName> → Vec<FQTraitName>` both approved and applied. |
| S-DRIFT-2 | D | Facade catch-up to source's `&str` signature (Decision 47 exception 1 pragmatic implementation). |
| S-DRIFT-3 | D | Facade catch-up to source's `Option<&'static str>` return (Decision 47 exception 1 alloc-free reverse-lookup). |
| S-DRIFT-4 | A | Bundled with H11 (walk row 347). |
| S-DRIFT-6 | D | Facade catch-up to source's `Option<Defn>` per Decision 22 (codegen-compilable predicate). |
| S-DRIFT-7 | D | Facade catch-up to source's `Box<DefKind>` per Principle 6 (size discipline). |
| S-DRIFT-8 | D | Source-side promotion `type MethodResolutions = …` → `#[non_exhaustive] pub struct MethodResolutions { … }` per facade non_exhaustive policy. |
| S-DRIFT-9 | D | Facade-side correction — name 4-field `TraitMethod` shape (source's post-D47 shape); move misplaced `trait_resolution` to `AutoCurry` row. |
| S-DRIFT-10 | C | Genuine arbitration A5 — Decision 44 names "opacity" intent but does not arbitrate enum-vs-struct. Tips on /typecheck audit of pattern-match consumer usage. |
| S-DRIFT-11 | RESOLVED (Submission 23) | Both move — fused `params: Vec<(Symbol, Option<TypeExpr>)>` shape per Principle 18 (lockstep invariant folded into the type) + spec §5.1.1 EBNF (per-param independently-optional annotation) + spec §5.1 L41 (no return-type annotation syntax). User-arbitrated 2026-05-22; revises the prior audit's "facade moves" framing. |
| S-DRIFT-12 | A | RESOLVED Submission 25 — facade editorial (`name: Symbol`, `type_expr`) + source-side `span: Span` field add per Decision 39; Option A (`TypeExpr` unconditional, synthesised-`TypeVar`-for-bare convention) user-arbitrated 2026-05-22. Consumer cascade /dev wave-3. |
| S-DRIFT-13 | RESOLVED (Submission 27) | **Both move** — 5-field `pub struct TraitImpl { trait_name: TraitRef, target: TypeExpr, type_constraints: Vec<(Symbol, TraitRef)>, methods, span }` + new syntactic-stage newtypes `TraitRef { module: Option<ModuleFullPath>, name: TraitName }` and `TypeRef { module: Option<ModuleFullPath>, name: TypeName }` (in `cranelisp-types::newtype`) capture as-written qualification structurally. `TypeExpr::Named(TypeName)` / `Applied(TypeName, …)` cascade to `TypeRef` payloads. Two scope-corrections vs. prior framing: (1) source's `trait_name: TraitName` was wrong — `(impl fmt/Display ...)` requires qualification structurally; (2) the `target_type + type_args` split had no Decision-level grounding — spec §5.4 EBNF treats target as one grammatical unit. See finding closure below. |
| S-DRIFT-14 | RESOLVED (Submission 26) | Both move — target `pub struct TraitMethodSig { name, docstring, params: Vec<(Symbol, TypeExpr)>, ret_type, span, hkt_param_index, default_body: Option<Expr> }` (7 fields). Facade is target — source's `Option<Sexp>` had no Decision-level grounding after the Principle 11 misattribution was removed (Submission 23); per `feedback_hold_to_facade_default.md` default is source-moves. Per Principle 18 + spec §5.3 EBNF, `default_param_names` retired — names belong with params, not default body — fused into `params.0`. See finding closure below. |
| S-DRIFT-15 | RESOLVED (Submission 21) | Form-record narrow + platform-module architecture per spec §2.2.9 + §10.9 + §8.9.3 — `PlatformSpec` aligned to form-record shape; `ModuleEntry::PlatformDecl` retired; DLL handle on platform module's own `SymbolTable.dll` via `D: DllStore` generic. A7 closed by form-record framing. See finding body below for closure pointer. |
| S-DRIFT-16 | D | Audit's disposition is "No action — already covered by facade disposition table". |
| S-DRIFT-17 | D | Facade catch-up to D48-mandated 3-variant split `{ Inline, Extern, PlatformEffect }`. |
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

**Source does.** Matches. `module.rs:560`.

**Design intent.** Already aligned. No drift.

**Disposition.** **No action.** Documentation parity exists.

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

### Finding U12 — `SymbolTable.linker: Option<L>` field

**Triage bucket: D — mechanical.** Facade-side documentation catch-up: add `linker: Option<L>` field to §"Symbol table" shape summary per Decision 35.

**Facade expects.** §"Symbol table" shape summary names `pub got`, `pub next_got_slot`, `pub imports/exports/platforms/submodules`, `pub defn_order`, `pub path`, `pub schema_version`. No `linker`.

**Source does.** Pub-api 1085: `pub linker: Option<L>`.

**Design intent.** Per **Decision 35** (`Code` enum location): "Per Decision 35, the current integration-layer choice is `L = ()` because per-symbol `Code::Linker.linker: Arc<Linker>` retention covers every case where a Linker must outlive its construction; `L` is reserved for future scenarios where a Linker must outlive its construction without any `Code::Linker` referencing it." The field's existence is forward-compatibility per Decision 35.

**Difference implies.** Without the field documented, a reader cannot tell why `L` exists. Decision 35 grounds the field; facade enumeration lags.

**Disposition.** **Facade moves.** Add `linker: Option<L>` to §"Symbol table" shape summary with brief note: "Per-module Linker retention root; `L = ()` integration-side, reserved per Decision 35." Closes U12.

---

### Finding U13 — `SymbolTable::new_with_params` constructor

**Triage bucket: D — mechanical.** Facade-side documentation catch-up: enumerate `new_with_params` in the generic-impl block per Decision 35 instantiation pattern.

**Facade expects.** Only `SymbolTable::new(path) -> SymbolTable<(), ()>` documented (line 399).

**Source does.** Pub-api 1102: `new_with_params(path: ModuleFullPath) -> Self` — generic over `<C, L>`.

**Design intent.** Per `module.rs:223–228` source rustdoc: "Rust's default type parameter inference does not propagate to associated function calls. The concrete-`()` inherent impl resolves the ergonomic gap without sacrificing the parameterisation." Integration-layer call sites (`SymbolTable::<Code, ()>::new_with_params(path)`) per **Decision 35** instantiation pattern. The constructor pair (one `<(), ()>`-pinned, one generic) is necessary by Rust language semantics; no Decision-level question.

**Difference implies.** Integration consumers (`src/session_v4.rs`) call the generic form. Facade silence misleads readers.

**Disposition.** **Facade moves.** Add `pub fn new_with_params(path: ModuleFullPath) -> Self` to the §"Symbol table" `impl<C: CodeStore, L: LinkerStore>` block, with the source-rustdoc rationale inline. Closes U13.

---

### Finding U14 — `SymbolTable::into_concrete` + `ModuleEntry::into_concrete`

**Triage bucket: D — mechanical.** Facade-side documentation catch-up: name both `into_concrete` conversions per Decision 35 (cache-restore bridge from `<()>` to `<C, L>`).

**Facade expects.** Not named.

**Source does.** Pub-api 1093, 890. Conversion from `<(), ()>` to `<C, L>` (or `ModuleEntry<()>` to `ModuleEntry<C>`).

**Design intent.** **Decision 35** + cache-restore path: "the cache deserialises a `<()>`-flavoured table (because `code` is `#[serde(skip)]` and `linker` is `#[serde(skip)]`, the serialised form is parameter-independent); the integration layer needs to install it as a `<Code, ()>`-flavoured table for its session." The `into_concrete` conversion is the bridge. Decision 35 grounds the structural need.

**Difference implies.** The conversion is load-bearing for cache-restore. Facade silence means a reader cannot tell how cache-restore bridges the type-parameter gap.

**Disposition.** **Facade moves.** Add `into_concrete` to the §"Symbol table" + `ModuleEntry` shape summaries with note about cache-restore role per Decision 35. Closes U14.

---

### Finding U15 — `GotTable::default()` and `GotTable::new()` (no capacity arg)

**Triage bucket: D — mechanical.** Facade-side fix: drop the `(capacity: usize)` parameter from `GotTable::new()` signature; document fixed-capacity `GOT_TABLE_SIZE` constant per Decision 23.

**Facade expects.** §"GOT" line 676 `pub fn new(capacity: usize) -> Self`.

**Source does.** `crates/cranelisp-types/src/got.rs:38`: `pub fn new() -> Self` (no args). `GOT_TABLE_SIZE` constant (`pipeline.rs:39`) defines the fixed capacity (1024).

**Design intent.** Fixed-capacity GOTs are a structural choice — avoids dynamic-sizing semantics + the AtomicPtr-vector growth question. **Decision 23's two-GOT model** (per `facades/types.md` lines 668–683) names the GOT as a fixed-capacity `Vec<AtomicPtr<()>>`. Decision 48's primitives static GOT is fixed-capacity. No Decision authors a configurable-capacity surface; the facade's `(capacity: usize)` is sloppy facade authoring with no Decision grounding.

**Difference implies.** Consumers cannot supply a custom capacity even if they wanted to. The fixed-capacity property is by design.

**Disposition.** **Facade moves.** Fix `GotTable::new()` signature in §"GOT" — no capacity parameter; document the fixed `GOT_TABLE_SIZE` constant. Closes U15.

---

### Finding U16 — `ErrorLocation::{from_span, from_span_file, unknown}`

**Triage bucket: D — mechanical.** Facade-side enumeration: name the three constructors in §"Errors and warnings" with one-line guidance per Decisions 39 + 42.

**Facade expects.** Not enumerated.

**Source does.** Three `pub` constructors per pub-api.

**Design intent.** **Decision 39** (per-defn source coordinates) + **Decision 42** (`PlatformError` adopts `ErrorLocation`) ground the `ErrorLocation` carrier shape. The three constructors discriminate the producer-side context: parser has file in hand → `from_span_file`; typecheck has only span → `from_span`; runtime error from synthetic source → `unknown`. The constructors are load-bearing for the consumer-side dispatch in the int formatter (per facade lines 757–823). Facade enumeration gap is documentation only.

**Difference implies.** Consumer call sites need to know which constructor to use for which case. Facade silence leaves the choice opaque.

**Disposition.** **Facade moves.** Enumerate the three constructors in §"Errors and warnings" with one-line guidance per case, grounded by Decision 39 + 42.

---

### Finding U17 — `LineCol::new(line, col)` + `LineColRange::new(start, end)`

**Triage bucket: D — mechanical.** Bundled with U16; same facade-side enumeration.

**Disposition.** **Facade moves.** Enumerate in §"Errors and warnings". Same Decision-39 grounding as U16.

---

### Finding U18 — `SchedulingClass::default()`

**Triage bucket: D — mechanical.** Audit's "No action — auto-derive Default::default() = Sequential" disposition holds.

**Facade expects.** §"Scheduling" describes the enum; no `default()` method.

**Source does.** Derived `Default` impl.

**Design intent.** Per facade `SchedulingClass.from_u32(v) -> Self` (line 749), the `Sequential = 0` variant is the canonical default for cross-DLL ABI-version drift. `Default::default() = Sequential` is the same value. **No Decision arbitrates the auto-derive.** Per audit discipline this still gets a one-sentence rationale.

**Disposition.** **No action.** Auto-derive `Default::default()` returns `Sequential` (variant 0) — semantically equivalent to facade's `from_u32(0)` and consistent with the §"Scheduling" "default Sequential" framing. No consumer-contract question.

---

### Finding U19 — `PlatformError::location()` accessor

**Triage bucket: D — mechanical.** Facade-side enumeration: add `pub fn location(&self) -> Option<&ErrorLocation>` to `PlatformError` per Decision 42 + symmetry with `CranelispError::location()`.

**Facade expects.** Per Decision 42, `PlatformError` carries `ErrorLocation` per variant; the `int` formatter consumes via `CranelispError::Platform(PlatformError)`. No `location()` accessor named.

**Source does.** `pub fn location()` accessor per pub-api.

**Design intent.** **Decision 42** (`PlatformError` adopts `ErrorLocation`) names the `ErrorLocation` carry-discipline; the symmetric `location()` accessor matches `CranelispError::location()` (named at facade line 822) per Principle 7 (uniform consumer surface). The accessor is grounded by Decision 42 + the facade's existing `CranelispError::location()` shape.

**Disposition.** **Facade moves.** Add `pub fn location(&self) -> Option<&ErrorLocation>` to `PlatformError` in §"Errors and warnings". Grounded by Decision 42.

---

### Finding U20 — `CranelispError::{message, span}` accessors

**Triage bucket: D — mechanical.** Facade-side enumeration of formatter-convenience accessors.

**Facade expects.** §"Errors and warnings" names `location()` only.

**Source does.** `pub fn message`, `pub fn span` additional accessors per pub-api.

**Design intent.** Formatter convenience accessors per the int-side consumer pattern (per `facades/int.md`); accessing fields without per-variant pattern-matching. Editorial enumeration gap; no Decision-level question.

**Disposition.** **Facade moves.** Enumerate the accessors in §"Errors and warnings".

---

### Finding U21 — `CranelispError::From<PlatformError>` impl

**Triage bucket: D — mechanical.** Audit's "No action — auto-trait noise per Decision 42 variant" disposition holds.

**Design intent.** Decision 42's `CranelispError::Platform(PlatformError)` variant implies the `From` impl by Rust idiom (`?` operator from `Result<…, PlatformError>` to `Result<…, CranelispError>`). Auto-trait surface; no Decision-level question.

**Disposition.** **No action.** Derived `From` impl is auto-trait noise per Decision 42's variant shape.

---

### Finding U22 — `HeapCategory::classify<C, L>(ty, Option<&DashMap<…>>)`

**Triage bucket: D — mechanical.** Facade-side enumeration: add the full `classify` signature to §"Heap layout" with two-mode contract; the `&DashMap<…>` outer-container shape is consistent with the post-concurrency-cluster target.

**Facade expects.** §"Heap layout" describes `HeapCategory { NeverHeap | AlwaysHeap | Mixed }`. No `classify` function.

**Source does.** `heap.rs:55–78`: classification function consulting symbol tables for ADT ctor layout.

**Design intent.** No Decision specifically authors `classify`'s signature, but its two-mode behaviour (with/without tables → conservative `Mixed` vs exact) is grounded by **Principle 6** (complexity has a budget — conservative default) + the backend consumer pattern (RC discipline). Source is the producer-of-record; facade silence is a documentation gap. Note `Option<&DashMap<…>>` confirms the **DashMap target shape** of the symbol tables — corroborating evidence for the SymbolTable concurrency complex (the classify signature is consistent with the facade's DashMap target state, not source's HashMap as-built).

**Disposition.** **Facade moves.** Add the full signature to §"Heap layout": `pub fn classify<C, L>(ty: &Type, symbol_tables: Option<&dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>>) -> HeapCategory`. Document the two-mode contract. Note: the `&DashMap<…>` parameter shape will hold post-source-migration of the SymbolTable concurrency complex (S-DRIFT-19 et al.) — until then, the signature is *aspirational on the outer container shape too*, but is correct as the post-migration target.

---

## 3. Shape drift (facade and source both present; details diverge)

### Finding S-DRIFT-1 — RESOLVED (Submission 11 — walk rows 339+340).

(a) Source-side `vars → type_vars` rename approved at `crates/cranelisp-types/src/types.rs:135` (~109 sites across 8 files cascaded to /dev). (b) Facade `Vec<TraitName> → Vec<FQTraitName>` editorial fix applied at `facades/types.md:354` per Decision 47 FQ-binding mandate.

---

### Finding S-DRIFT-2 — `Type::from_name` signature

**Triage bucket: D — mechanical.** Facade catch-up to source's `&str` per Decision 47 exception 1 (reverse-lookup) + Principle 6 (alloc-free hot path).

**Facade expects.** §"Resolved type system" line 343: `pub fn from_name(name: &TypeName) -> Option<Type>`.

**Source does.** `types.rs:33`: `pub fn from_name(name: &str) -> Option<Type>`.

**Design intent.** **Decision 47 exception 1** — "Reverse-lookup helpers on `Type`. `from_name(&TypeName) -> Option<Type>` for primitive recognition and `type_name(&Type) -> Option<TypeName>` for primitive emission. These operate on the small set of built-in non-ADT types where the unqualified name IS unique workspace-wide." Decision 47 names `&TypeName` as the signature — but the facade's §"FQTypeName migration plan" §"backend" table at line 282 + S65 W2 review § 4.1 names primitive-registration call sites that synthesise `TypeName::from("Int")` from string literals (`builtins.rs:552,604,664,729,929,1082,…`). Source's wider `&str` admits both flavours.

The configuration here is **internally inconsistent**: Decision 47's exception 1 names `&TypeName` (narrow), but the migration plan + S65 W2 review accept literal-string callers (wider). Source's `&str` is the practical signature that lets the literal callers work without per-site `TypeName::from(...)` wrapping (alloc-per-call on a startup-hot path; Principle 6 — complexity has a budget — disfavours).

**Difference implies.** If facade enforces `&TypeName`, every primitive-init site adds a `TypeName::from("Int")` wrap. If source's `&str` stands, the exception-1 signature is "accepts `&str` because `&TypeName: Deref<Target=str>` auto-deref covers the typed call sites and bare-literal call sites match the same signature."

**Disposition.** **Facade moves.** Adjust facade `Type::from_name` to `pub fn from_name(name: &str) -> Option<Type>` and add inline note: "Decision 47 exception 1 (reverse-lookup): accepts `&str` to admit both `&TypeName` (via `Deref`) and bare literal call sites (primitive registration). The wider signature is structurally consistent with exception 1's narrow scope — built-in non-ADT types where unqualified names are unique." This is **facade catch-up to source's pragmatic Decision-47-exception-1 implementation**, not facade-author preference. The catch-up should ideally be accompanied by a one-line clarification in Decision 47 itself (filed separately as `/arch` follow-up if /design surfaces the inconsistency).

---

### Finding S-DRIFT-3 — `Type::type_name` return type

**Triage bucket: D — mechanical.** Facade catch-up to source's `Option<&'static str>` (bundled with S-DRIFT-2 — Decision 47 exception 1 + alloc-free reverse-lookup).

**Facade expects.** Line 344: `pub fn type_name(&self) -> Option<TypeName>`.

**Source does.** `types.rs:44`: `pub fn type_name(&self) -> Option<&'static str>`.

**Design intent.** Symmetric to S-DRIFT-2. **Decision 47 exception 1** names this as the inverse reverse-lookup helper. The `&'static str` return matches the static primitive name strings (`"Int"`, `"Bool"`, etc.); wrapping in `TypeName` forces a `String` allocation per call (TypeName is `pub struct TypeName(pub String)` per the `string_newtype!` macro — so `Option<TypeName>` is an owned alloc per call). Backend's primitive-codegen consults this for every primitive call site — startup + hot-path allocation.

**Difference implies.** Same as S-DRIFT-2 — wider source signature is the practical Decision-47-exception-1 shape.

**Disposition.** **Facade moves.** Adjust to `type_name(&self) -> Option<&'static str>`. Same rationale as S-DRIFT-2 — exception-1 reverse-lookup with alloc-free static string return.

---

### Finding S-DRIFT-4 — RESOLVED (Submission 11 — walk row 347).

Bundled with H11 closure. `ImportNames` locked to 5 spec-grounded variants {Specific, Glob, MemberGlob, AliasOnly, Null} (per spec §8.3.1–§8.3.6); `ExportSpec.names` decoupled from import enum and made structurally symmetric. Source-side migration in concurrency-cluster /dev brief.

---

### Finding S-DRIFT-5 — RESOLVED (Submission 13)

Closed by Submission 13 (`ModuleEntry::Macro` sibling-variant retirement + macro unification under `DefKind::Macro`). The arbitration A2 question — "can multi-clause macro dispatch live behind a single GOT slot per macro?" — was answered structurally: not through one slot at the parent entry, but through **N GOT slots one-per-clause-body** under mangled names `{macro-name}$clause-{N}`, parallel to multi-sig fn variants (`add$Int+Int`). The parent `Def { kind: Macro { clauses_meta, sexp, source } }` is metadata-only (`got_slot` unused, `code: None`); each clause body is its own `Def { kind: UserFn, got_slot, code: Some(_), … }`. `MacroEnv` retires; clause-body lookup is the same GOT-dispatch path as any other callable.

See `facades/types.md` §"DefKind" `DefKind::Macro` for the full shape, dispatch story, and three rejected alternatives (sibling-variant kept, entry-level trampoline, sexp/source at Def level). Source-side retirement of the `ModuleEntry::Macro` sibling variant tracked in the concurrency-cluster /dev brief (sprints/SPRINT.md).

---

### Finding S-DRIFT-6 — `ModuleEntry::Def.ast` type

**Triage bucket: D — mechanical.** Facade catch-up to source's `Option<Defn>` per Decision 22 (codegen-compilable predicate consumes wider `Defn` shape).

**Facade expects.** Line 455: `ast: Option<Expr>`.

**Source does.** Pub-api 851 + `module.rs:469`: `ast: Option<Defn>`.

**Design intent.** **Decision 21** (legacy: `tc-sourced-call-graph.md`) + **Decision 22** (legacy: `defined-symbols-shared-predicate.md`) ground the `ast` field's role: codegen-compilable iff `ast: Some(_)` AND kind is not `Overloaded`/constrained-fn template. Decision 22's predicate (`defined_symbols`) consumes `ast.is_some()`.

The narrower `Expr` vs wider `Defn` question: backend's compile path consumes the multi-variant signatures (mangled-variant emission), param names + annotations (calling convention), and the original span (error reporting at the defn level). Stripping to `Expr` would force backend to retrieve those elsewhere. **Decision 22's "code-compilable predicate"** assumes the wider `Defn` shape is what's stored.

**Difference implies.** Source's `Option<Defn>` is what Decision 22's predicate operates on and what backend's compile path consumes. Facade's `Option<Expr>` is editorial-narrower and would not match the consumer pattern Decision 22 names.

**Disposition.** **Facade moves.** Adjust to `ast: Option<Defn>`. Rationale: Decision 22's predicate + backend's consumer pattern require the wider `Defn` shape; facade-text narrowing is editorial. Source is the correct as-consumed shape. Closes S-DRIFT-6.

---

### Finding S-DRIFT-7 — `ModuleEntry::Def.kind` boxing

**Triage bucket: D — mechanical.** Facade catch-up to source's `Box<DefKind>` per Principle 6 (size discipline; pattern-match through Box is transparent).

**Facade expects.** Line 453: `kind: DefKind`.

**Source does.** Pub-api 856 + `module.rs:429`: `kind: Box<DefKind>`.

**Design intent.** `DefKind` has heavy variants — `Overloaded { variants: Vec<OverloadVariant> }` (multi-sig dispatch) and `UserFn { constrained_fn: Option<Box<ConstrainedFn>> }` (constrained polymorphism). Boxing trims the `ModuleEntry::Def` size (per **Principle 6** — complexity has a budget; pattern-match through `Box` is transparent). **No Decision specifically authors the boxing**; it is an implementation choice that the facade did not catch up to. Editorial.

**Disposition.** **Facade moves.** Adjust to `kind: Box<DefKind>` with one-line note: "Boxed for size discipline per Principle 6; pattern-match through the box is transparent." Closes S-DRIFT-7.

---

### Finding S-DRIFT-8 — `MethodResolutions` shape

**Triage bucket: D — mechanical.** Source-side promotion `type MethodResolutions = HashMap<…>` → `#[non_exhaustive] pub struct MethodResolutions { pub resolved_calls: HashMap<…> }` per facade non_exhaustive policy + Principles 8/13.

**Facade expects.** §"Typecheck output" line 646:

```rust
#[non_exhaustive] pub struct MethodResolutions { pub resolved_calls: HashMap<Span, ResolvedCall> }
```

**Source does.** `check.rs:7`: `pub type MethodResolutions = HashMap<Span, ResolvedCall>`.

**Design intent.** **Facade §"`#[non_exhaustive]` policy"** (line 919) is binding: "every public struct and enum MUST be `#[non_exhaustive]`." Type aliases are exempt from `#[non_exhaustive]` in Rust (you can't apply the attribute to an alias), but the policy intent — extensibility, allow adding fields without breaking consumers — is violated by the alias: consumers see `HashMap` directly and use HashMap methods. **Principle 8** (no interim implementations) + **Principle 13** (`interfaces.md` is auditable + `cargo-public-api`-gateable) ground the newtype struct shape as the target.

**Difference implies.** The alias commits to HashMap forever; the newtype struct admits future fields (per-call-site context, instance-context for trait resolution). The non_exhaustive policy is binding facade-text intent.

**Disposition.** **Source moves.** Promote to `#[non_exhaustive] pub struct MethodResolutions { pub resolved_calls: HashMap<Span, ResolvedCall> }`. Consumers using `HashMap` methods continue via `Deref<Target=HashMap>` or via the `resolved_calls` field. Migration: ~5–10 consumer dot-access sites in typecheck + backend. Grounded by facade non_exhaustive policy + Principles 8/13. Closes S-DRIFT-8.

---

### Finding S-DRIFT-9 — `ResolvedCall::TraitMethod` field set

**Triage bucket: D — mechanical.** Facade-side correction: name source's 4-field shape (`trait_name: FQTraitName, method_name, impl_type: FQTypeName, mangled_name: JitSymbol`) per Decision 47 FQ-binding; move misplaced `trait_resolution` to `AutoCurry` row.

**Facade expects.** §"Item-by-item disposition" §"Enum variants" describes `ResolvedCall::TraitMethod::{method_name, mangled_name, trait_resolution}` (three fields, third being `trait_resolution: Option<Box<ResolvedCall>>`).

**Source does.** `check.rs:13–18`:

```rust
TraitMethod {
    trait_name: FQTraitName,
    method_name: Symbol,
    impl_type: FQTypeName,
    mangled_name: JitSymbol,
}
```

Four fields. **No `trait_resolution`** (that field lives on `AutoCurry`, per facade line 987).

**Design intent.** **Decision 47** (FQTypeName binding) target-states `trait_name: FQTraitName` + `impl_type: FQTypeName` on resolved-stage boundary types. `MethodResolutions` is a typecheck-output type → resolved stage → exception-1/-2 don't apply → FQ binding applies. Source's four-field shape IS the post-D47 target. The facade's three-field shape misnames `TraitMethod` by ascribing `trait_resolution` (which actually belongs to `AutoCurry`) and omits the trait + impl_type identifiers that Decision 47 mandates.

**Difference implies.** Backend reads `mangled_name: JitSymbol` to emit the call directly; reads `impl_type` + `trait_name` for resolution-context introspection. The facade's `trait_resolution` chain is misplaced.

**Disposition.** **Facade moves.** Correct the §"Item-by-item disposition" §"Enum variants" row to name `TraitMethod::{trait_name: FQTraitName, method_name: Symbol, impl_type: FQTypeName, mangled_name: JitSymbol}` per source (which is the Decision-47 target). Move `trait_resolution` to the `AutoCurry` row (where it already belongs per facade line 987). Source is correct; facade documentation error. Closes S-DRIFT-9.

---

### Finding S-DRIFT-10 — `View<'a, C, L>` shape

**Triage bucket: C — arbitration genuine.** Decision 44 names opacity intent + "newtype" (singular) but does not arbitrate enum-vs-struct; needs /typecheck audit of consumer-side pattern-match usage (and/or /arch Decision-44 amendment) to settle direction.

**Facade expects.** §"View" lines 188–219:

```rust
pub struct View<'a, C: CodeStore = (), L: LinkerStore = ()> {
    staging: &'a SymbolTable<C, L>,
    live: &'a SymbolTable<C, L>,
}
impl ... {
    pub fn union(staging, live) -> Self;
    pub fn single(live) -> Self;
    pub fn lookup(...);
    pub fn iter(...);
}
```

Newtype struct with `union`/`single` constructors. §"Properties" claim: consumers don't know which side a lookup hit (staging vs live).

**Source does.** `view.rs:33–43`:

```rust
#[non_exhaustive]
pub enum View<'a, C, L> {
    Single { live: &'a SymbolTable<C, L> },
    Union { staging: &'a SymbolTable<C, L>, live: &'a SymbolTable<C, L> },
}
```

**Public enum with visible variants.**

**Design intent.** **Decision 44** (cluster-atomic typecheck via orchestrator-owned staging) names the View shape and the staging-vs-live opacity claim:

> A `View<'a, C, L>` is the read-side abstraction: a thin newtype on `cranelisp-types` that holds two `&SymbolTable` references (staging + live) and routes lookups (staging-first, then live). `View` is constructed inside `ClusterContext::current_symbol_table()` for cluster mode; in committed (`Live`) mode the same method returns a single-source view. Typecheck reads `ctx.current_symbol_table()` whenever it would have read `&SymbolTable` directly; it cannot tell whether the view unions staging+live or hits live alone.

The Decision 44 text uses "newtype" — singular structural shape — not "enum." The opacity claim ("cannot tell whether the view unions staging+live or hits live alone") is structurally enforced only by the struct form with private internal state. Source's public enum admits consumer-side `match view { Union { .. } => …, Single { .. } => … }` which IS observable distinction. The enum vs struct shape is **mid-implementation drift**, not a Decision-arbitrated alternative.

However: Decision 44 specifies the *intent* (opacity) but not the *concrete shape*. The §"Item-by-item disposition" §"PIF candidate" line 959 already self-flags this finding as the enum-vs-struct PIF candidate. So the configuration acknowledges the inconsistency.

**Difference implies.** The opacity claim is structurally undermined by the enum form. Consumer-side staging-vs-live shortcircuits become possible, which defeats Decision 44's "typecheck cannot distinguish staging from live because the accessor abstracts the difference" rationale (per Decision 44 §"Statement"). The structural enforcement that Decision 44 names is currently absent.

**Disposition.** **Arbitration A5 (genuine — configuration names opacity intent but does not arbitrate enum vs struct).** Two paths:

- **(a) Source moves** — re-author `View` as a `struct` with a private enum-shaped inner state (or `(staging: Option<&_>, live: &_)`). Expose `union` / `single` constructors, `lookup` / `iter` methods. Hide the staging-vs-live distinction. **Tips toward (a):** Decision 44's opacity claim is the binding intent; the struct form is the structural enforcement Principle 18 names; the consumer-side pattern-match shortcircuit is a hazard Decision 44 explicitly speaks against.

- **(b) Facade moves** — re-author the facade to describe `View` as the enum, with the §"Properties" opacity claim retracted via a Decision-44 amendment. Document that consumers MAY pattern-match the variant when they need to know the mode (REPL introspection that wants to skip cluster-staging).

**What tips.** /arch on whether Decision-44 amendment is preferred over source rework. Per **Principle 18** (enforce invariants structurally where possible — the structural option is the right choice when both exist), (a) is the principled default. But the configuration genuinely does not name "struct" explicitly — only "newtype" — and (b) is consistent with a more permissive reading of Decision 44.

Schedule deferral acceptable; A5 brief in §6.

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

### Finding S-DRIFT-16 — `ModDecl` shape

**Triage bucket: D — mechanical.** Audit's "No action — already covered by facade disposition" holds.

**Facade expects.** Line 597: `pub struct ModDecl { pub name: ModuleName, pub visibility: Visibility, pub span: Span }`.

**Source does.** `module.rs:748–753`: `pub struct ModDecl { pub name: ModuleName, pub is_private: bool, pub inline_body: Option<Vec<Sexp>>, pub span: Span }`.

**Design intent.** Already self-flagged by facade §"Item-by-item disposition" §"Struct fields" — `is_private` synonym + `inline_body` for inline `(mod name forms…)` declarations. The shape-summary uses `visibility: Visibility` as the abbreviated form. No Decision-level question.

**Disposition.** **No action.** Already covered by existing facade disposition. (The §"Item-by-item disposition" already names both fields.)

---

### Finding S-DRIFT-17 — `PrimitiveKind` variants

**Triage bucket: D — mechanical.** Facade catch-up to D48-mandated 3-variant split `{ Inline, Extern, PlatformEffect }`.

**Facade expects.** Lines 548–551:

```rust
pub enum PrimitiveKind {
    Builtin,
    PlatformEffect { scheduling_class: SchedulingClass },
}
```

Two variants.

**Source does.** `module.rs:638–660`:

```rust
pub enum PrimitiveKind {
    Inline,
    Extern,
    PlatformEffect { scheduling_class: SchedulingClass },
}
```

Three variants.

**Design intent.** **Decision 48** (`cranelisp-primitives` owns a statically-constructed `SymbolTable` + `Arc<GotTable>`) names the variant split explicitly:

> Inline (codegen emits Cranelift IR inline at the call site for `+`, `-`, etc.), Extern (call dispatches via the GOT slot to the primitive's body in `cranelisp-primitives`), PlatformEffect (DLL-routed effect).

The variant rename `Builtin` → `Inline` + the addition of `Extern` is the post-D48 target state. **Decision 48 is landed in source** (`Inline`/`Extern` variants exist); the facade has not caught up. The facade post-S68 close was supposed to update; verification: line 548 still names `Builtin`.

**Difference implies.** Facade's `{ Builtin, PlatformEffect }` is pre-D48 stale text. Source's `{ Inline, Extern, PlatformEffect }` IS the post-D48 target.

**Disposition.** **Facade moves (Decision-48-mandated catch-up).** Adjust §"Symbol table" `PrimitiveKind` to `pub enum PrimitiveKind { Inline, Extern, PlatformEffect { scheduling_class: SchedulingClass } }`. Document inline: "Inline = backend emits Cranelift IR inline at the call site; Extern = call dispatches via the GOT slot to the primitive's body in `cranelisp-primitives` per Decision 48; PlatformEffect = DLL-routed effect per Decision 26." Closes S-DRIFT-17.

(Calibration flip from prior audit: prior audit had "facade moves" but did not surface that this is **Decision-48-mandated**. Future maintainers should see the D48 grounding inline.)

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
| U12 | `SymbolTable.linker: Option<L>` field | Facade moves | Decision 35 |
| U13 | `SymbolTable::new_with_params` | Facade moves | Decision 35 (instantiation pattern) |
| U14 | `into_concrete` (SymbolTable + ModuleEntry) | Facade moves | Decision 35 (cache-restore) |
| U15 | `GotTable::new()` (no capacity) | Facade moves | Decision 23 (fixed-capacity GOT) + Principle 6 |
| U16 | `ErrorLocation::{from_span,…}` | Facade moves | Decisions 39 + 42 |
| U17 | `LineCol::new`/`LineColRange::new` | Facade moves | Bundled with U16 |
| U18 | `SchedulingClass::default()` | No action | Auto-trait noise (Sequential = 0) |
| U19 | `PlatformError::location()` | Facade moves | Decision 42 (symmetry with CranelispError::location) |
| U20 | `CranelispError::{message,span}` accessors | Facade moves | Principle 13 |
| U21 | `CranelispError::From<PlatformError>` | No action | Auto-trait noise (Decision 42 implies) |
| U22 | `HeapCategory::classify<C, L>` | Facade moves | Principle 6 (two-mode conservative) + Principle 13 |
| S-DRIFT-1 | `Scheme.{type_vars→vars}` + FQTraitName | Facade moves | Decision 47 (FQ binding mandates `FQTraitName`) + editorial (`vars`) |
| S-DRIFT-2 | `Type::from_name(&str)` | Facade moves | Decision 47 exception 1 + Principle 6 |
| S-DRIFT-3 | `Type::type_name() -> Option<&'static str>` | Facade moves | Decision 47 exception 1 + Principle 6 |
| S-DRIFT-4 | `ImportNames` / `ExportSpec` variant set | Source moves | Bundled with H11 (Decision 39) |
| S-DRIFT-5 | `ModuleEntry::Macro` field set (GOT-callable) | **RESOLVED (Submission 13)** | Unified to `Def { kind: DefKind::Macro { clauses_meta, sexp, source } }`; per-clause GOT-callable via mangled-variant `UserFn` Defs (`{macro}$clause-{N}`), parallel to multi-sig fns; `MacroEnv` sidecar retires |
| S-DRIFT-6 | `ModuleEntry::Def.ast: Option<Defn>` | Facade moves | Decision 22 (codegen-compilable predicate) |
| S-DRIFT-7 | `ModuleEntry::Def.kind: Box<DefKind>` | Facade moves | Principle 6 (size discipline); editorial |
| S-DRIFT-8 | `MethodResolutions` newtype struct | Source moves | Facade non_exhaustive policy + Principles 8/13 |
| S-DRIFT-9 | `ResolvedCall::TraitMethod` field set | Facade moves | Decision 47 (source's FQ shape IS the target) |
| S-DRIFT-10 | `View<'a, C, L>` enum vs struct | Arbitration A5 (genuine) | Decision 44 names opacity intent; doesn't arbitrate enum vs struct |
| S-DRIFT-11 | `DefnVariant` fused params + no return_type | **RESOLVED (Submission 23) — both move** | Principle 18 (lockstep invariant folded structurally) + spec §5.1.1 EBNF + spec §5.1 L41 |
| S-DRIFT-12 | `FieldDef` shape + missing span | **RESOLVED (Submission 25) — both move** | spec §2.2.6 + §5.2 (name always present) + Principle 7 (`type_expr` naming) + Decision 39 (per-field `span`); Option A (`TypeExpr` unconditional, synthesised-`TypeVar`-for-bare convention) user-arbitrated 2026-05-22 |
| S-DRIFT-13 | `TraitImpl` ast.rs shape + syntactic-stage qualification | **RESOLVED (Submission 27) — both move** | New syntactic-stage newtypes `TraitRef { module: Option<ModuleFullPath>, name: TraitName }` + `TypeRef { module: Option<ModuleFullPath>, name: TypeName }` capture as-written qualification structurally; `TypeExpr::Named` / `Applied` cascade to `TypeRef` payloads; `TraitImpl` rewritten to 5-field target `{ trait_name: TraitRef, target: TypeExpr, type_constraints: Vec<(Symbol, TraitRef)>, methods, span }`. Spec §2.3.4 + §4.2.2 (qualified references) + spec §5.4 EBNF (target as one grammatical unit — `target_type + type_args` split had no Decision-level grounding) + Decision 47 sharpening (producer/consumer split: syntactic stage carries qualification structurally; typecheck does the FQ lift) + Decision 45 (resolved-stage counterpart on trait's defining module); `feedback_hold_to_facade_default.md` directs source-moves when source has no Decision-level grounding; user-arbitrated 2026-05-22 |
| S-DRIFT-14 | `TraitMethodSig` shape | **RESOLVED (Submission 26) — both move** | spec §5.3 EBNF (every method has named params; `param = ':' type_expr symbol | symbol` always terminates in a `symbol`) + spec §5.3.1 (synthesised-`SelfType` for bare params) + spec §5.3.2 (HKT param index) + spec §5.4.5 (default-body typecheck against instantiated signature per impl) + Principle 18 (lockstep invariant folded structurally — `default_param_names` retired) + Principle 7 (`ret_type` producer-side naming canonical) + Decision 39 (per-method span); user-arbitrated 2026-05-22 (facade is target — source's `Option<Sexp>` had no Decision-level grounding after Submission 23 corrected the Principle 11 misattribution; `feedback_hold_to_facade_default.md` directs source-moves as default) |
| S-DRIFT-15 | `PlatformSpec` placeholder shape | Both move + arbitration A7 | Principle 14 / newtype rule (source-side narrowing) + arbitration on resolved-vs-pre-resolved |
| S-DRIFT-16 | `ModDecl.is_private` + `inline_body` | No action | Already covered |
| S-DRIFT-17 | `PrimitiveKind { Inline, Extern, PlatformEffect }` | Facade moves | Decision 48 (variant split mandated) |
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
| Source moves | 27 (H2, H3, H4, H5, H6, H7, H9, H10, H11, U11, S-DRIFT-4, S-DRIFT-8, S-DRIFT-19, S-DRIFT-20, S-DRIFT-21, C-HOLE-4, C-HOLE-5, C-HOLE-6 — plus partial source-side moves in H8, S-DRIFT-12, S-DRIFT-15, U9 = 22 hard + ~5 partial) |
| Facade moves | 18 (U1, U2, U4, U5, U7, U8, U10, U12, U13, U14, U15, U16, U17, U19, U20, U22, S-DRIFT-1, S-DRIFT-2, S-DRIFT-3, S-DRIFT-6, S-DRIFT-7, S-DRIFT-9, S-DRIFT-17, S-DRIFT-18, S-DRIFT-22; S-DRIFT-11 reclassified to "both move" per Submission 23 + S-DRIFT-12 reclassified per Submission 25 + S-DRIFT-14 reclassified per Submission 26 + S-DRIFT-13 reclassified per Submission 27 — each surfaced that source had no Decision-level grounding and the configuration prefers a third option neither side held; the parallel S-DRIFT-11/S-DRIFT-14 reclassifications grounded on the corrected Principle 11 misattribution; S-DRIFT-22 reclassified D→"Facade moves" per Submission 29 — scope-extended editorial sharpening preserves opacity policy intact) |
| Both move | 8 (H1, H8, U9, S-DRIFT-11, S-DRIFT-12, S-DRIFT-13, S-DRIFT-14, S-DRIFT-15) |
| Arbitration (genuine) | 2 (A2 = S-DRIFT-5; A5 = S-DRIFT-10) — both with default direction stated |
| No action | 5 (U3, U6, U18, U21, S-DRIFT-16, C-HOLE-3) — S-DRIFT-22 reclassified to "Facade moves" per Submission 29 (scope-extended editorial sharpening; opacity policy intact per Principle 15) |
| Requires /qa work | 2 (C-HOLE-1, C-HOLE-2) |

(The count totals add to slightly more than 59 because findings with both-move dispositions appear in two columns. Per-finding source vs facade direction is in the table.)

---

## 6. What the audit cannot resolve alone — arbitration briefs

The audit identifies **one genuine arbitration item** (A5) where the architectural configuration does not ground a direction. The prior audit's "11 arbitration items" was inflated by mis-grounded findings; calibration table in §7 shows the conversions. A2 (Macro callable shape) closed by Submission 13 — see §"S-DRIFT-5 — RESOLVED" above. Per the audit discipline, the remaining genuine arbitration is named with **the binary choice** + **the evidence either way** + **what tips it**.

### Arbitration A2 — RESOLVED (Submission 13)

Closed structurally by user-arbitrated unification of macros into `Def { kind: DefKind::Macro { clauses_meta, sexp, source } }`. The framing of A2 — "single GOT slot per macro with trampoline vs per-clause `func_ptr` via MacroEnv" — was dissolved by the third option: **per-clause GOT-callable via mangled-variant `UserFn` Defs** (`{macro-name}$clause-{N}`), parallel to multi-sig fn variants. Expansion-time clause-walk (existing logic) walks `clauses_meta` and GOT-dispatches to the matched clause's variant Def. See `facades/types.md` §"DefKind" `DefKind::Macro` for the manifestation site.

### Arbitration A5 — `View<'a, C, L>` enum vs struct (S-DRIFT-10)

**Question.** Is `View` a public enum (consumers MAY pattern-match the variant) or a struct with private internal mode (consumers consume only through methods)?

**Stakeholders.** /arch (Decision 44 amendment authority); /typecheck (primary consumer).

**Configuration check.** Decision 44 names the opacity intent ("typecheck cannot distinguish staging from live because the accessor abstracts the difference") + uses "newtype" (singular) in the View shape description. Source has authored as `pub enum`. Principle 18 (enforce invariants structurally — the struct form is the structural enforcement of the opacity intent). Facade's own §"Item-by-item disposition" already self-flags View as the enum-vs-struct PIF candidate.

**Default direction (Principle-18-grounded).** **Source moves** to struct form.

**Evidence toward (a) struct.** Decision 44 opacity intent + Principle 18 + facade §"Properties" claim. Consumer-side pattern-match shortcircuits would defeat Decision 44's staging-vs-live opacity.

**Evidence toward (b) enum stays.** Source has settled here; the enum form is simpler and admits cluster-aware observability hooks (e.g., counting staging vs live hits). Decision 44's "newtype" wording could be read permissively (Rust often uses "newtype" loosely to mean "thin wrapper").

**What tips.** /typecheck audit on consumer-side pattern-match usage. If typecheck (the primary consumer) consistently calls `view.lookup` / `view.iter` without pattern-matching, struct form costs little and locks in opacity per Principle 18. If typecheck pattern-matches `View::Single` / `View::Union`, struct-form refactor cost is real and /arch's call.

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
| **S-DRIFT-17** | Facade moves | **Facade moves** (confirmed, grounding added) | Decision 48 mandates the variant split — prior audit had direction right but missed D48 grounding |
| **S-DRIFT-1 (b)** | Facade moves | **Facade moves** (confirmed, grounding added) | Decision 47 mandates `FQTraitName` — prior audit had direction right but missed D47 grounding |
| **S-DRIFT-5** | Requires /arch + /typecheck + /backend arbitration | **RESOLVED (Submission 13)** | Unified to `Def { kind: DefKind::Macro { clauses_meta, sexp, source } }` with per-clause GOT-callable via mangled-variant `UserFn` Defs (`{macro}$clause-{N}`). See §"S-DRIFT-5 — RESOLVED". |
| **C-HOLE-5** | Bundled with arbitration | **Source moves** (bundled with S-DRIFT-19) | Principle 18 + sequence diagram |
| **U9** | Both move + /arch (bundled with H11/S-DRIFT-4) | **Both move + arbitration A6 narrowed to /spec on MemberGlob** | The `None` vs `AliasOnly` direction is editorial; only `MemberGlob` is genuine /spec arbitration |
| **S-DRIFT-15** | Both move + /platform arbitration | **Both move (newtype-rule fix grounded) + arbitration A7** (broader shape) | Newtype-rule narrowing is Principle-14-grounded; broader shape is open |

### Confirmations (same disposition; new grounding citation)

The remaining 21 dispositions match the prior audit's direction but the corrected audit adds explicit configuration citations to each. For example:

- **S-DRIFT-6** (`ast: Option<Defn>`): prior audit "facade moves" stands; this audit cites Decision 22 (codegen-compilable predicate) as the grounding.
- **S-DRIFT-8** (`MethodResolutions` newtype): prior audit "source moves" stands; this audit cites facade non_exhaustive policy + Principle 8.
- **S-DRIFT-11** (`DefnVariant` split params): prior audit "facade moves" **revised in Submission 23 to "both move" — fused `Vec<(Symbol, Option<TypeExpr>)>` shape**. The Principle 11 citation in this audit was a misattribution (Principle 11 governs single-pipeline mode parameters, not annotation shape); the correct grounding is **Principle 18** (enforce invariants structurally — fold the parallel-vec lockstep invariant into the tuple) + spec §5.1.1 EBNF + spec §5.1 L41. See Finding S-DRIFT-11 body for closure pointer.
- **H2** (`Type::unwrap_io`): prior audit "source moves" stands; this audit cites Principles 2 + 6.

### Other movement

- **H1** (`primitives()` accessor): Prior audit "facade moves" → this audit "both move (D48 retirement arc)" — both sides retire post-D48 per FIXMEs 0182 + 0191. Calibration: surfacing the D48 grounding is what shifts this from "facade-doc fix" to "scheduled bilateral retirement."

- **S-DRIFT-10** (`View` enum vs struct): Prior audit "requires /arch arbitration" → this audit "arbitration A5 with default = source moves per Principle 18." Calibration: Principle 18 grounds the default direction even though the configuration does not name "struct" explicitly.

### The methodology correction itself

The prior audit's 23 "facade moves" dispositions were correct as facade-doc moves but **largely failed to surface the Decision-level grounding** — readers could not tell from the disposition column alone whether a "facade moves" was D47-mandated catch-up (e.g., S-DRIFT-1b, S-DRIFT-9; S-DRIFT-13 also originally cited here, since reclassified Submission 27 to "both move" with broader scope), D48-mandated catch-up (S-DRIFT-17), Decision-22-grounded (S-DRIFT-6), or editorial-only (S-DRIFT-7, S-DRIFT-18). The corrected audit names the grounding inline per finding so future audits can cite back.

The prior audit's 11 "requires /arch arbitration" dispositions split into:
- **9 mis-grounded** (configuration grounds the direction; only schedule is in question): H3, H4, H5, H9, H10, H11, S-DRIFT-4, S-DRIFT-19/20/21 (one complex), C-HOLE-5. The corrected audit re-classes these as **source moves** with schedule deferral acceptable.
- **2 genuine arbitration** (A2 = S-DRIFT-5; A5 = S-DRIFT-10). The corrected audit retains the arbitration brief but adds the default direction the configuration grounds (per Principle 13 for A2; per Principle 18 for A5).

The over-classification to "arbitration" in the prior audit was the structural failure mode the user's 2026-05-19 direction names — the audit was not reading the architectural configuration that grounds the facade. Decisions 31, 32, 38, 41, 44 + the canonical sequence diagram + Principle 18 collectively settle the SymbolTable concurrency complex; the prior audit's "binary choice + evidence" brief was real work but the configuration had already named the binary's answer. The methodology pivot is: read the configuration first, classify against it, only then identify what remains genuinely open.

---

## 8. Verdict

The audit identifies **27 source-side moves** and **20 facade-side moves** as the immediate disposition register; **4 both-move** items split work bilaterally; **2 genuine arbitration items** (A2, A5) require cross-skill input but with explicit default directions; **6 no-action** items (auto-trait noise, already-covered); **2 /qa-side** mechanical-test enhancements (C-HOLE-1/2).

The architectural payload is the **SymbolTable concurrency complex** — H3, H5, H6, H7, S-DRIFT-19/20/21, C-HOLE-5 — bundled as one source-side migration grounded by Decisions 31, 32, 38, 41, 44, 48 + the canonical `concurrency-symbol-table-entry.mmd` sequence diagram + Principle 18. The migration is bounded by the Decision-44 accessor-layer surgery (the 91 register-call sites in typecheck flow through `ctx.current_symbol_table_mut()`; the migration is at the accessor + ~5–10 backend GOT-write sites, not at the per-call-site level).

**Sprint scope.** S69 wave-3 can resolve the 20 facade-side moves cleanly. The 27 source-side moves are bounded source work; the concurrency-complex bundle is the largest single migration and is the natural fit for a dedicated source-side wave in S70 or a S70+S71 split. The 2 genuine arbitration items (A2, A5) require /arch input before source-side migration can be concrete; /sprint files the corresponding `/arch` FIXMEs at the S69 wave gate.

**Methodology correction signal.** 32 of the prior audit's 59 dispositions changed in some way under design-intent grounding (23 "facade moves" flipped to "source moves", 9 "arbitration" flipped to "source moves", plus 21 dispositions where direction confirmed but grounding citation added, 6 other shifts). The flip rate is high — over half the prior audit's findings carried mis-classification that was visible only once the configuration was loaded. The configuration grounds far more than the prior audit credited.

The remaining genuine arbitration count is **2** (down from prior 11). Both items name the configuration-grounded default direction; /arch input is for amendment-or-confirmation of the default, not for unbounded direction-finding. This is the audit-as-grounding-mechanism mode the user-direction 2026-05-19 names: the architectural configuration grounds the facade; the audit reads the configuration; the wave gate sees the right work-by-source vs work-by-facade split with each item named to its Decision/Principle/FIXME.
