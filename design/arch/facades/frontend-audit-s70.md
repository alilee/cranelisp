# cranelisp-frontend facade audit — Sprint 70 Phase B

**Status**: authored; audit findings dispositioned in B3-B (commits `ced64ab`–`f9ae663`); facade subsequently retired in B3-C (this memo survives as the historical audit-walk record).
**Filed**: 2026-05-26
**Filed by**: /arch (B1 — audit memo authoring; not actioning)
**Inputs frozen at**: `a4fc9e0` (S70 Phase A close + A5 doc-refresh follow-up).

> **Post-B3-C note (2026-05-26).** The facade document audited here (`design/arch/facades/frontend.md`) was retired in S70 Phase B group B3-C; its narrative folded into `crates/cranelisp-frontend/src/lib.rs` //! preamble + per-item rustdoc + `design/arch/bounded-contexts.md` §1. This audit memo references the pre-retirement facade by section/line; those references are historical records of the document state at audit time.

---

## Scope

This audit walks the per-line `crates/cranelisp-frontend/public-api.txt` against the per-line `design/arch/facades/frontend.md` (post-Phase-A amended state) and disposes findings against the configuration grounds (Decisions, Principles, BC §1 + §7, FIXMEs, `design/frontend/*.md`).

### Inputs

1. **Facade**: `design/arch/facades/frontend.md` (251 LOC; substantially amended vs S69 baseline — see S69→S70 facade diff summary below).
2. **Source surface**: `crates/cranelisp-frontend/public-api.txt` (120 LOC; byte-identical to pre-A4 baseline per S70 Phase A constraint — Phase A was internal-only).
3. **Configuration grounds**:
   - `design/arch/CLAUDE.md` Decisions register (filtered for frontend-touching: 32, 33, 39, 43, 44, 45, 47)
   - `design/arch/principles/` — 2, 13, 15, 17, 18 (cited below)
   - `design/arch/bounded-contexts.md` §1 (frontend BC) + §7 (types crate — `ModuleAliases`, `SymbolTables`, per-entry visibility, multi-legged authoring)
   - `design/arch/fixmes/0098-dev-frontend-typecheck-int-resolutiongap-checkerror-expansionerror-migration.md`
   - `design/arch/fixmes/0175-arch-frontend-expand-invocation-gap.md`
   - `design/frontend/frontend.md`, `design/frontend/sprint-70-cascade-plan.md`
   - `design/arch/facades/cranelisp-frontend-audit-s69.md` (S69 precedent; eight findings)

### Out of scope

- **Items S69 dispositioned cleanly + closed**. None — all S69 source-side dispositions (H1, H2, S1, S2) remain **un-actioned**; their status has not changed. They are carried forward as still-open in §"S69 carries" below, not re-audited from scratch.
- **Items the S69 audit folded to /qa scoping (C1/C2/C3)**. Coverage-hole class is a project-wide /qa concern, not frontend-specific; not re-derived here.
- **Per-crate design doc audits**. The cascade-plan, ast-builder, and expand design docs are /design territory.
- **`crates/cranelisp-types/` surface**. Settled by S70 Phase 3 steps 1+2+3 cascade.

### S69→S70 facade diff summary (essential to ground findings)

Between commits `9516dfc` (S69 close baseline) and `a4fc9e0` (S70 Phase A close), the frontend facade was substantively amended in five places:

| # | Section | Change |
|---|---|---|
| (i) | `expand` signature | Gained third parameter `module_aliases: &ModuleAliases` |
| (ii) | `SymbolTables<C, L>` typedef block | `Arc<SymbolTable<...>>` wrapper removed; canonical home declared as `cranelisp-types` (was: `cranelisp_frontend::expand`) |
| (iii) | `SymbolTables` typedef block | Added second typedef `ModuleAliases = DashMap<ModuleFullPath, ModuleAliasEntry>` |
| (iv) | Macro lookup paragraph | `ModuleEntry::Macro` retired → `Def { kind: DefKind::Macro { clauses_meta, … } }`; clause-body GOT-dispatch path narrated |
| (v) | New `## Deftype expander` trailing section | Constructor-as-`DefKind::Constructor` synthesis path; `ParsedEntry::Constructor` → `ModuleEntry::Def`-with-`DefKind::Constructor` rather than `ModuleEntry::Constructor` |

Plus an inline **Drift note** acknowledging the `Arc` was editorial drift from S69 (the canonical typedef per BC §7 has no `Arc`).

(iv) and (v) are facade narrative changes that track the S70 Phase 3 cascade (`ModuleEntry::Macro` retired in step 1; `DefKind::Constructor` introduced in step 3). They do not introduce facade-side drift vs source if source already follows the Phase 3 cascade — which Phase A delivered for the type-side (Submissions 13, 22, etc.). Frontend source-side consumption is what this audit walks.

(i), (ii), (iii) are the substantively new target-stated commitments not in S69 — they ARE the new drift to disposition.

### Method

Per `memory/feedback_audit_per_item_analysis.md` + `memory/feedback_configuration_grounds_facade.md` + `memory/feedback_hold_to_facade_default.md`: **five-block per finding** (facade-expects / source-does / design-intent grounded in named Decision/Principle/BC/FIXME / difference / disposition). Default per `feedback_hold_to_facade_default.md` is **source moves** when the facade is target-stating; *facade moves* requires explicit Decision-amendment rationale + user signoff at B2. The facade's own §5 self-declaration ("This spec is target-stating") binds.

---

## S69 carries — still-open dispositions from the precedent audit

The S69 audit (`design/arch/facades/cranelisp-frontend-audit-s69.md`) dispositioned four source-moves (H1, H2, S1, S2). Verifying source state at `a4fc9e0`:

| S69 ID | S69 disposition | Source state at `a4fc9e0` | Carry status |
|---|---|---|---|
| H1 | Source moves: `pub use expand::{expand, EXPANSION_DEPTH_LIMIT, SymbolTables};` | `lib.rs` does not contain the line | **STILL OPEN** |
| H2 | Source moves: extend `pub use quasiquote::{...}` to include `expand_quote_template` | `lib.rs:44` still: `pub use quasiquote::{expand_quasiquotes, next_synthetic_span};` (two-name set) | **STILL OPEN** |
| S1 | Source moves: `extract_module_declarations(containing_module: &ModuleFullPath, forms: …)` | `module_extract.rs:28–30`: `path: ModuleFullPath, sexps: Vec<Sexp>` (by-value, generic names) | **STILL OPEN** |
| S2 | Source moves: rename `_span` → `span`, wire user-source span into outer `Sexp::List` | `defmacro.rs:337`: `_span: Span` (underscore retained; never used in body) | **STILL OPEN** |

These four are not re-audited from scratch (S69 grounded them fully); they are folded into the S70 disposition table below as **inherited source-moves**. Phase A scope did not include them (Phase A was the Phase-3 cascade absorption — newtype opacity, ModuleEntry/Def shape changes — orthogonal to these four). Either Phase B3 actions them (small mechanical edits; ~one commit) or they carry forward to S71. The disposition rationale stands as authored in the S69 memo — no re-grounding needed.

S69 also dispositioned **C1/C2/C3** as `/qa S70` and **U0** as `no-action`. C1/C2/C3 are outside the source/facade lens of this audit (project-wide test infrastructure); U0 was a positive-confirmation pass that the identifier-set matched — re-verified as still matching below in §"Verified-at-target items".

---

## Findings — new drift introduced by S70 facade amendment

The S70 facade introduced three substantively new target-stated commitments (i, ii, iii above). Source has not been updated to match. Each is a separate finding:

### Finding F1 — `expand` signature has 2 parameters in source, 3 parameters in facade

- **Lens / Category**: Free function signature (boundary entry, narrowness-load-bearing).
- **Site**:
  - Facade: `design/arch/facades/frontend.md:27–35` (post-A4 signature).
  - Source: `crates/cranelisp-frontend/src/expand.rs:142–149`; public-api line 41.
- **facade-expects**:
  ```rust
  pub fn expand<C, L>(
      sexp: Sexp,
      symbol_tables: &SymbolTables<C, L>,
      module_aliases: &ModuleAliases,
  ) -> Result<Sexp, ExpansionError>
  where C: CodeStore, L: LinkerStore;
  ```
  Facade §59 grounds the necessity inline: "§8.6.6 qualified-name resolution for a macro head (`m.n.str/some-macro`) may need to traverse an import or export alias on the way to the macro's defining module — the lookup is not just a module-table get. The two tables are threaded as two parameters per the narrow-interfaces principle (Principle 2) and to keep the existing in-flight migration from inline `&DashMap<…>` shapes to a single materialised typedef (S69 audit F-1) tractable."
- **source-does**:
  ```rust
  pub fn expand<C, L>(
      sexp: Sexp,
      symbol_tables: &SymbolTables<C, L>,
  ) -> Result<Sexp, ExpansionError>
  where C: CodeStore, L: LinkerStore
  ```
  Pub-api line 41: `pub fn cranelisp_frontend::expand::expand<C, L>(sexp: ..., symbol_tables: &SymbolTables<C, L>) -> ...` — no third parameter. The body (lines 150–212) only consults `symbol_tables`; alias resolution is not yet implemented (the `lookup_macro_fq` helper scans every module in `symbol_tables`, not the alias table).
- **design-intent**:
  - **BC §7 §"Module aliases live at session level"** (`design/arch/bounded-contexts.md:260`): "`SymbolTable` holds a single per-key store … The module-path-namespace aliases introduced by spec §8.3.4 (import alias) and §8.4.4 (export mount) live in a parallel session-level table `ModuleAliases = DashMap<ModuleFullPath, ModuleAliasEntry>` … keying by full path lets §8.6.6 qualified-name resolution do a single-table longest-prefix-match against the queried `module_path`." This is the binding architectural commitment — `ModuleAliases` is named here as a workspace-stable session-level table, not as an internal frontend concern.
  - **Spec §8.3.4 + §8.4.4 + §8.6.6** (spec citation in BC §7) ground the alias-import + export-mount + qualified-name-resolution semantics. Expand needs alias traversal for FQ-name macro head lookup.
  - **Principle 2 — Narrow interfaces**: two parameters (not a single bundled "session context") because each is a different keying domain and consumers (typecheck-only at `SymbolTables<(), ()>`, integration-layer at `SymbolTables<Code, ()>`) need to construct or borrow them independently.
  - **Facade §5 self-declaration**: target-stating.
- **difference**: Source's two-parameter signature does not support spec §8.6.6 alias traversal at the macro-head lookup. Today the gap is masked because `expand` returns `Err(Gap)` on every macro head encountered (FIXME 0175 deferral — the real invocation lives in `src/expander.rs`); the alias-traversal step is never reached in the frontend's deferred-skeleton. Once FIXME 0175 resolves (likely `cranelisp-marshal` crate per the facade's S66 W3a-β status paragraph) and the live invocation path migrates into `cranelisp-frontend`, alias resolution becomes load-bearing and the two-param signature is structurally insufficient.
- **proposed disposition**: **Source moves** (with FIXME-deferral option for the ParsedEntry-style migration scoping).

  Two paths:
  - **(F1.a) Add the third parameter now** (Phase B3 mechanical edit). Source-side: add `module_aliases: &ModuleAliases` parameter; thread through `expand_recursive`; for now (FIXME 0175 still open) the parameter is unused inside the function body, marked `_module_aliases` until the live invocation path lands. Callers (the deferred-skeleton tests in `expand.rs` + any in-tree caller) pass an empty `DashMap::new()` or a session-supplied reference. `ModuleAliases` + `ModuleAliasEntry` are authored in `cranelisp-types` at the same time per ground (a) (BC §7's canonical placement). Cost: ~10 LOC source + ~5 LOC types crate.
  - **(F1.b) Defer to a FIXME** (file `target: /dev` or `target: /frontend`). Rationale: F1 is structurally entangled with FIXME 0175's marshal-deps gap. If `cranelisp-marshal` becomes a new crate, alias resolution may live there rather than in `cranelisp-frontend`'s signature. A premature signature change might be re-done. Cost: zero now; defer until 0175 resolves.

  Recommendation: **F1.a** is the principled call. The facade target-states the parameter as a uniform-Gap-era commitment (the function returns Gap today; the parameter is wiring for later). Per `feedback_hold_to_facade_default.md`: "default to source-moves; cost is not a strong reason; facade-as-binding is binary not gradient." The parameter is unused-but-present; the disciplinary cost is small; the architectural debt is paid immediately. **F1.b** is offered only if the user prefers FIXME-deferral pending FIXME 0175 resolution — at which point the carrier-coupling between F1 and 0175 becomes the explicit rationale to revisit.

- **rationale**: BC §7 grounds `ModuleAliases` as canonical; spec §8.6.6 grounds the alias-traversal need; Principle 2 grounds the parameter shape; facade §5 binds target-stating. Configuration is not silent — three named grounds converge on the F1.a shape.

### Finding F2 — `SymbolTables<C, L>` defined in `cranelisp-frontend::expand`, not `cranelisp-types`

- **Lens / Category**: Type alias location (boundary type placement; Principle-15 grounded).
- **Site**:
  - Facade: `frontend.md:53–57` (the typedef block, annotated "Canonical declarations in `cranelisp-types`; re-exported / imported here").
  - Source: `crates/cranelisp-frontend/src/expand.rs:69–75` — the `SymbolTables<C, L>` typedef is **defined here**, not imported.
- **facade-expects**:
  ```rust
  // Canonical declarations in `cranelisp-types`; re-exported / imported here:
  pub type SymbolTables<C, L> = DashMap<ModuleFullPath, SymbolTable<C, L>>;
  pub type ModuleAliases = DashMap<ModuleFullPath, ModuleAliasEntry>;
  ```
  The comment "Canonical declarations in `cranelisp-types`" is explicit — the typedef's canonical home is types-crate.

  Facade §"Module layout" table row for `cranelisp_frontend::expand` (post-amendment): "Contains: `expand`, `ExpansionError`, `EXPANSION_DEPTH_LIMIT`. … `SymbolTables<C, L>` and `ModuleAliases` aliases are consumed from `cranelisp_types` (S69 cascade — types-crate is the canonical home)."

  Facade §"Consumed surface" (post-amendment): `cranelisp-types` consumed list explicitly includes `SymbolTables`, `ModuleAliases`, `ModuleAliasEntry`.

- **source-does**: `expand.rs:69–75`:
  ```rust
  /// Per-frontend type alias for the workspace-wide symbol-tables map.
  pub type SymbolTables<C, L> = DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>;
  ```
  Defined in the frontend crate. Pub-api line 42: `pub type cranelisp_frontend::expand::SymbolTables<C, L> = dashmap::DashMap<…, alloc::sync::Arc<…>>` — sourced from frontend, not re-exported from types. And the `Arc<…>` wrapper persists (see F3 below for the Arc-side of this drift).

  `cranelisp-types` source: zero `SymbolTables` typedef; zero `ModuleAliases`; zero `ModuleAliasEntry` — confirmed by grep across `crates/cranelisp-types/src/`.

- **design-intent**:
  - **Principle 15 — Facade types live with their behavior**: "`cranelisp-types` holds *only* types referenced in two or more implementation-crate facades — the workspace's shared multi-consumer vocabulary." `SymbolTables<C, L>` is referenced in the frontend facade (`expand` parameter), the int facade (constructed at session init), and is structurally consumed by typecheck (per Decision 44's `check_forms` signature). Three consumers → types-crate is the canonical home per the placement heuristic.
  - **Decision 32 — `CodeStore` / `LinkerStore` empty-marker**: the boundary alias `SymbolTables<C, L>` is named at workspace-stable status; frontend, typecheck, and int all instantiate it at different `C, L` parameterisations. A per-frontend typedef defeats the workspace-stable claim — typecheck and int either re-derive `DashMap<ModuleFullPath, SymbolTable<C, L>>` inline (no shared name) or import the frontend's name (inverts the dep graph — typecheck has no business depending on frontend).
  - **BC §7** (`bounded-contexts.md:260`): `ModuleAliases = DashMap<ModuleFullPath, ModuleAliasEntry>` is named under the types-crate bounded context. By symmetric placement, `SymbolTables` belongs there too.
  - **Facade §5 self-declaration**: target-stating.

- **difference**: Source's `cranelisp_frontend::expand::SymbolTables` is the de-facto canonical name today (typecheck imports from `cranelisp_types::SymbolTable` directly and constructs `DashMap<..., SymbolTable<C, L>>` inline at its callers; int does the same). The facade's typedef-block claim of "canonical in `cranelisp-types`" is not delivered — `cranelisp-types` does not export the alias. Consumers writing `cranelisp_frontend::expand::SymbolTables<Code, ()>` import the alias from frontend (a dep inversion that violates Principle 15's hosted-with-behavior rule for shared vocabulary). Per F1, `ModuleAliases` does not exist in source at all.

- **proposed disposition**: **Source moves**.

  Concretely:
  1. Author `pub type SymbolTables<C, L> = DashMap<ModuleFullPath, SymbolTable<C, L>>;` in `crates/cranelisp-types/src/module.rs` (or a new `crates/cranelisp-types/src/aliases.rs`).
  2. Author `pub struct ModuleAliasEntry { … }` + `pub type ModuleAliases = DashMap<ModuleFullPath, ModuleAliasEntry>;` in same file. The `ModuleAliasEntry` shape needs spec'ing per spec §8.3.4 + §8.4.4 — minimum-viable fields are (a) the target full path the alias resolves to and (b) the alias's own visibility per BC §7's per-entry-visibility convention. /design's call on the field set; /arch's call if BC §7 needs to be amended to specify the shape.
  3. Delete `expand.rs:69–75` `pub type SymbolTables<C, L> = …`; replace with `use cranelisp_types::{SymbolTables, ModuleAliases};` (or thread through the existing `use cranelisp_types::{…}` block at lines 62–65).
  4. The H1 (S69 carry) `pub use expand::{expand, EXPANSION_DEPTH_LIMIT, SymbolTables};` line in `lib.rs` becomes `pub use expand::{expand, EXPANSION_DEPTH_LIMIT};` plus a separate convenience re-export `pub use cranelisp_types::{SymbolTables, ModuleAliases};` at the crate root if the facade endorses it. Per facade §"Re-export policy" the three current re-exports (`ResolutionGap`, `DefmacroInfo`, `MacroClause`) are inline-justified; adding `SymbolTables` + `ModuleAliases` requires an explicit `/arch` ratification because re-exports erode dep-graph clarity. **Recommendation: do not re-export; consumers import directly from `cranelisp_types`** (this is the Principle-15 default; the existing three exceptions are narrowly justified by enum-variant-pattern-match needs, which doesn't apply to type aliases).

- **rationale**: Three converging configuration facts: (i) Principle 15 grounds the multi-consumer types-crate placement (typecheck-frontend-int triple consumer); (ii) Decision 32 grounds the workspace-stable boundary-alias claim; (iii) BC §7 explicitly names `ModuleAliases` at types-crate scope, symmetric to `SymbolTables`. The facade's typedef-block annotation "Canonical declarations in `cranelisp-types`" is the target-stating commitment; source has not yet delivered. Per `feedback_facade_first_migration.md`: "for owed migrations from target-stated facade: push cranelisp-types to target first, accept broken build, fix consumers wave-by-wave; don't negotiate." F2 is the textbook case.

### Finding F3 — `SymbolTables` source typedef wraps `Arc<SymbolTable>`, facade typedef does not

- **Lens / Category**: Type alias shape (boundary-type structural definition).
- **Site**:
  - Facade: `frontend.md:55` — `pub type SymbolTables<C, L> = DashMap<ModuleFullPath, SymbolTable<C, L>>;` (no `Arc`).
  - Facade explicit drift note `frontend.md:61`: "Earlier facade text declared `pub type SymbolTables<C, L> = DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>;` (with `Arc<…>`). The canonical types-crate typedef does NOT wrap in `Arc` — the integration layer's `SharedState.symbol_tables: DashMap<ModuleFullPath, SymbolTable<Code, ()>>` holds the per-module `SymbolTable` values directly inside the DashMap shards. The `Arc` was an editorial drift on the frontend facade; the form above is the canonical shape."
  - Source: `expand.rs:75` — `pub type SymbolTables<C, L> = DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>;` (with `Arc`).
- **facade-expects**: no `Arc` wrapper. The DashMap shard directly owns the `SymbolTable<C, L>` value.
- **source-does**: `Arc<SymbolTable<C, L>>` wrapper present. Pub-api line 42 confirms.
- **design-intent**:
  - **Facade drift-note paragraph** explicitly grounds the canonical shape against the `int` crate's `SharedState.symbol_tables` field, which is the workspace-stable storage shape. The drift-note self-classifies the `Arc` as editorial (editorial drift, not a different architectural choice).
  - **No Decision or Principle authorises the `Arc`.** No grounding for the wrapper survives audit. The DashMap shard's per-shard `RwLock<HashMap<K, V>>` already provides the concurrent-access discipline (`Arc` adds reference-counted shared ownership; the use case here is per-shard ownership inside the map, not external sharing of individual `SymbolTable` values across threads).
  - **Per `memory/feedback_no_premature_perf.md`**: "get the single correct path first, tune later; don't keep v1 alive for speed." The `Arc` is a speculative concurrency-cheapness move (cheap `.clone()` of an `Arc` vs an owned `SymbolTable`); zero evidence in the configuration set that the `Arc` clone path is load-bearing.

- **difference**: Per-shard memory layout differs: `DashMap<K, Arc<SymbolTable>>` stores a 16-byte (8-byte pointer + 8-byte refcount) `Arc` cell per shard slot, dereferencing to a heap-allocated `SymbolTable`; `DashMap<K, SymbolTable>` stores the `SymbolTable` value inline in the shard's `HashMap<K, V>` bucket. The two shapes are not interchangeable at type-level — code that today writes `Arc::clone(&entry)` would not compile against the no-`Arc` form.

  Worker-side call sites and JIT-handle-stash points may rely on cheap `Arc::clone` semantics. The migration cost is concrete: every `Arc::clone(&symbol_table)` site rewrites to `symbol_table.clone()` (if `SymbolTable: Clone`) or restructures to hold a `&SymbolTable` reference.

- **proposed disposition**: **Source moves** — paired with F2 (the same edit lifts the typedef into types-crate AND drops the `Arc`).

  Migration sequencing:
  1. Author the no-`Arc` typedef in `cranelisp-types` per F2.
  2. Audit every call site that reads `Arc::clone(&entry)` or `dashmap_ref.value().clone()` — replace with the appropriate borrow / owned-clone shape.
  3. Verify `SymbolTable<C, L>: Clone` is satisfiable (likely yes — every field is `Clone`).

  Per `feedback_facade_first_migration.md`: push types-crate to target first; accept broken build; fix consumers wave-by-wave. F3 is the canonical case of this discipline — push the typedef, fix call sites in the resulting wave.

- **rationale**: The facade drift-note self-classifies `Arc` as editorial drift not architectural; no Decision/Principle grounds the wrapper; `int`'s `SharedState.symbol_tables` is the workspace-stable storage shape. Per `feedback_hold_to_facade_default.md` and `feedback_facade_first_migration.md`: configuration grounds source-moves; the cost-of-migration argument does not override the binary facade-as-binding.

### Finding F4 — `Sexp::Quote` constructor / `expand_quote_template` re-export status uncertain

- **Lens / Category**: Re-export coverage at root (paired with S69's H2).
- **Site**:
  - Facade §"Module layout" table row for `quasiquote`: "Root re-exports: yes (all three re-exported at the crate root)" — names `expand_quasiquotes`, `expand_quote_template`, `next_synthetic_span`.
  - Source: `lib.rs:44`: `pub use quasiquote::{expand_quasiquotes, next_synthetic_span};` — `expand_quote_template` omitted (S69 H2).
- **facade-expects**: all three at crate root.
- **source-does**: two of three (`expand_quote_template` missing). Pub-api line 64 (`cranelisp_frontend::quasiquote::expand_quote_template`) but no `cranelisp_frontend::expand_quote_template` line.
- **design-intent**: Identical to S69 H2 grounding (facade §132 names the three-name standing-API set; FIXME 0098 Phase 2 step 2 schedules migration). No new grounding emerges between S69 and S70.
- **difference**: Identical to S69 H2.
- **proposed disposition**: **Inherits S69 H2 source-moves disposition** — not re-dispositioned here; recorded as a duplicate-perspective entry to confirm Phase A did not action H2.
- **rationale**: S69 H2 grounding unchanged; Phase A did not action; the carry stands.

(F4 is provided for completeness of the S70 walk. /sprint may fold F4 into H2 or leave it as a duplicate-perspective audit row.)

### Finding F6 — `ExtractedDeclarations` is not `#[non_exhaustive]` in source; facade §66 prescribes it

- **Lens / Category**: DTO attribute discipline (`#[non_exhaustive]` on public DTOs).
- **Site**:
  - Facade `frontend.md:66`: `#[non_exhaustive] pub struct ExtractedDeclarations { … }` — attribute target-stated.
  - Facade `frontend.md:223–225`: §"`#[non_exhaustive]` DTOs" enumerates `ExtractedDeclarations` and `ExpansionError` as the two public DTOs both carrying `#[non_exhaustive]`.
  - Source `crates/cranelisp-frontend/src/module_extract.rs`: `#[derive(Debug, Clone)]\npub struct ExtractedDeclarations {` — only the derive, no `#[non_exhaustive]`. Pub-api line 44 confirms: `pub struct cranelisp_frontend::module_extract::ExtractedDeclarations` with no `#[non_exhaustive]` marker (compare line 17: `#[non_exhaustive] pub enum cranelisp_frontend::expand::ExpansionError` — the marker IS present on `ExpansionError`).
- **facade-expects**: `#[non_exhaustive]` on the struct definition.
- **source-does**: missing.
- **design-intent**:
  - Facade §"`#[non_exhaustive]` DTOs" (§220–226) names both public DTOs (`ExtractedDeclarations`, `ExpansionError`) as `#[non_exhaustive]`. The pattern is the workspace-wide DTO discipline (see also BC §7's "Field-level access on state types is discouraged outside the types crate" — `#[non_exhaustive]` is the structural mechanism that enforces it).
  - **Principle 18 — Enforce architectural invariants structurally**: `#[non_exhaustive]` is the structural mechanism preventing breaking pattern-matches at consumer sites when fields are added. Without it, every field addition (e.g., adding a `trait_decls: Vec<TraitDecl>` row to `ExtractedDeclarations` post-cascade) is breaking. With it, additions are non-breaking.
  - **Workspace convention**: `cranelisp-types`-hosted DTOs are uniformly `#[non_exhaustive]` (verified for `ExpansionError`; consistent with facade §220).
- **difference**: A field addition to `ExtractedDeclarations` today is a breaking surface change visible at every consumer call site (struct-update syntax, struct literal, pattern match). Once the marker lands, additions are minor-bump compatible.
- **proposed disposition**: **Source moves**. Add `#[non_exhaustive]` to `crates/cranelisp-frontend/src/module_extract.rs` immediately above `pub struct ExtractedDeclarations`. Regenerate pub-api baseline. One-line source-side edit.
- **rationale**: Facade §66 + §220–226 target-state the attribute; Principle 18 grounds the structural-enforcement reason; the sibling `ExpansionError` already follows the pattern in source. Zero counter-grounds.

### Finding F5 — Macro lookup narrative refers to a `ModuleAliasEntry` shape uncited in source-side rustdoc

- **Lens / Category**: Source-side documentation drift; facade-narrative-vs-source-rustdoc.
- **Site**:
  - Facade §59 (post-amendment): grounds the two-parameter `expand` signature on the need to "traverse an import or export alias on the way to the macro's defining module". `ModuleAliasEntry` carries the alias edge.
  - Source: `expand.rs:215–240` (the `lookup_macro_fq` helper) makes no reference to `ModuleAliasEntry` — it scans every module's symbols directly via `symbol_tables[module].symbols`. Source comment at lines 215–228 narrates "FQ" and "Bare" shapes; alias traversal is not mentioned.
- **facade-expects**: source rustdoc on `lookup_macro_fq` (and equivalents) acknowledges the alias path per facade §59 / BC §7 §"Module aliases live at session level".
- **source-does**: rustdoc narrates FQ + Bare shapes only; alias-traversal step is absent (consistent with F1 — the `module_aliases` parameter is absent, so alias traversal can't be invoked). Once F1 lands, the rustdoc will need refresh.
- **design-intent**: facade §59 + BC §7 + spec §8.6.6 ground the alias-traversal as an architectural step.
- **difference**: Source-side documentation drift downstream of F1's signature gap. Will close naturally as part of F1.a.
- **proposed disposition**: **No action standalone** — folds into F1.a as a doc-comment update accompanying the third-parameter introduction. Recorded here so /design's pickup of F1.a knows the rustdoc refresh is part of the change-set, not a separate item.
- **rationale**: F5 is a doc-symptom of F1's structural gap. Closing F1 closes F5.

---

## Verified-at-target items

These facade-prescribed items match the source surface cleanly. No 5-block needed; brief confirm-and-move-on lines.

- **Free function `parse`** — facade §16: `pub fn parse(source: &str) -> Result<Vec<Sexp>, CranelispError>` / pub-api line 117: matches. Module home: `reader`; root re-export present per `lib.rs:52–54`.
- **Free function `parse_preserving_comments`** — facade §149 / pub-api line 119: matches.
- **Free function `build_form`** — facade §23 / pub-api line 110: signature matches (`&Sexp` → `Result<Vec<ParsedEntry>, CranelispError>`). Module + root re-export both present.
- **Free function `build_expr`** — facade §25 / pub-api line 109: matches.
- **DTO `ExtractedDeclarations`** — facade §66–73 / pub-api lines 92–97: five fields match (`path`, `import_specs`, `export_specs`, `platform_specs`, `mod_decls`), `#[non_exhaustive]` present, dual-naming (module + root) endorsed by facade §75. Note: S69 audit U0 confirmed this already; verified unchanged.
- **DTO `ExpansionError`** — facade §96–105 / pub-api lines 17–25 (and root dup at 69–77): three variants (`Gap(ResolutionGap)`, `Malformed { message, span }`, `MacroAborted { fq, message, span }`) + `#[non_exhaustive]` marker. Matches.
- **Macro-resolver helpers** — `parse_defmacro`, `is_defmacro`, `is_begin`, `flatten_begin`, `synthesize_macro_clause_defn` all present at both `defmacro::` module path AND root. Two of three quasiquote helpers (`expand_quasiquotes`, `next_synthetic_span`) at root; one (`expand_quote_template`) missing at root — see F4 / S69 H2.
- **Public const `EXPANSION_DEPTH_LIMIT`** — present at `expand::EXPANSION_DEPTH_LIMIT` per pub-api line 40. Per S69 H1 carry: not at root.
- **Re-export `ResolutionGap`** — present at root per pub-api line 4. Inline-justified by facade §189.
- **Re-export `DefmacroInfo` + `MacroClause`** — present at root + `defmacro::` per pub-api lines 2, 3, 9, 10. Inline-justified by facade §191–193.
- **Six public modules** — `reader`, `ast_builder`, `module_extract`, `defmacro`, `quasiquote`, `expand` — present per pub-api lines 1, 5, 8, 16, 43, 62, 66. Match.
- **No `MacroResolver` trait** — facade §82 grounds the absence per Decision 43; source `lib.rs` does not export a `MacroResolver` trait. Verified absent.
- **`#[non_exhaustive]` on `ExpansionError`** — verified at `expand.rs:90`. Matches facade. (`ExtractedDeclarations` does NOT match — see Finding F6.)
- **`expand` is C/L-blind** — verified per source generics `<C, L>` + `where C: CodeStore, L: LinkerStore`. Match facade §32–34.
- **BC §1 invariants 1–8** — none of the eight invariants is structurally observable as a pub-api line; they are behavior contracts. The audit cannot disposition them through public-API walk; coverage rides on /qa's integration test suite and the per-PR /review audit. Not findings.

---

## Summary

| # | Category | Site | Proposed disposition | Grounding citation |
|---|---|---|---|---|
| **S69 H1** (carry) | root re-export missing | `lib.rs:30–48` | Source moves (still open) | Decision 32; Principle 13; FIXME 0098 Phase 2; facade §5 + §183 |
| **S69 H2** (carry) | `expand_quote_template` missing from root re-export | `lib.rs:44` | Source moves (still open) | Facade §142; FIXME 0098 Phase 2 step 2 |
| **S69 S1** (carry) | `extract_module_declarations` shape: `&ModuleFullPath` / role-named vs by-value | `module_extract.rs:28–30` | Source moves (still open) | Principle 2; facade §37 (role-naming); facade §5 |
| **S69 S2** (carry) | `synthesize_macro_clause_defn` parameter: `span` vs `_span` (feature-gap) | `defmacro.rs:337` | Source moves (still open) | Decision 39; BC §1 invariant 4 (uniqueness not blocking); facade §114 |
| **F1** | `expand` signature missing `module_aliases: &ModuleAliases` parameter | `expand.rs:142` | Source moves (F1.a recommended; F1.b deferral offered) | BC §7 §"Module aliases live at session level"; spec §8.6.6; Principle 2; facade §59 |
| **F2** | `SymbolTables<C, L>` defined in frontend, facade names types-crate as canonical home | `expand.rs:75` | Source moves (lift to `cranelisp-types`) | Principle 15; Decision 32; BC §7; facade §53 |
| **F3** | `SymbolTables` source typedef wraps `Arc<SymbolTable>`; facade typedef does not | `expand.rs:75` | Source moves (drop Arc paired with F2) | Facade §61 drift-note (self-classified editorial); `int::SharedState.symbol_tables` workspace-stable shape; `feedback_no_premature_perf.md` |
| **F4** | `expand_quote_template` missing from root re-export | duplicate of S69 H2 | Inherits S69 H2 disposition | (As S69 H2) |
| **F5** | Source rustdoc on `lookup_macro_fq` does not reflect alias traversal | `expand.rs:215–240` | No action standalone — folds into F1.a | (As F1) |
| **F6** | `ExtractedDeclarations` missing `#[non_exhaustive]` | `module_extract.rs` (struct definition) | Source moves | Facade §66 + §220–226; Principle 18; workspace convention |

Distribution: 4 inherited source-moves (S69 carries), 4 new source-moves (F1, F2, F3, F6), 1 duplicate-perspective (F4), 1 dependent (F5). **Zero facade-moves. Zero arbitrations.** Per `feedback_audit_per_item_analysis.md` — every finding cites at least one Decision/Principle/BC/FIXME ground. No under-grounded findings need /sprint clarification.

## Audit verdict

**FRONTEND HAS DRIFT.**

- **Severity**: moderate. The four S69 carries are small mechanical fixes (~10 LOC across `lib.rs`, `module_extract.rs`, `defmacro.rs`). The three new findings (F1/F2/F3) are tightly coupled — F1's `module_aliases` parameter depends on F2's `ModuleAliases` typedef in `cranelisp-types`, which depends on F2's authoring of `ModuleAliasEntry`. F3's `Arc` removal is paired with F2's lift. The three should land as one change-set in B3.
- **Configuration grounding state**: every finding cites a named Decision (32, 39, 43, 47), Principle (2, 13, 15, 17, 18), BC section (§1, §7), or FIXME (0098, 0175). Zero findings are under-grounded; zero require /sprint clarification.
- **Source-moves only**: zero facade-moves, zero arbitrations. The S70 facade amendments (i)/(ii)/(iii) are target-stated commitments resolved on Configuration. The S69 carries' grounding stands unchanged.

## Methodology notes / surprises

1. **S69 source-side dispositions remain entirely un-actioned.** The S69 audit explicitly named four source-moves (H1, H2, S1, S2) with concrete edits; S70 Phase A did not pick them up. Phase A was the Phase-3 cascade absorption (newtype opacity, ModuleEntry/Def shape changes) — orthogonal scope. This is a methodology data point: **per-crate audit dispositions need an explicit "claim" mechanism that moves them from disposition to a sprint's task list.** Without it, S69 audit became reference material that didn't drive change. /sprint may want to consider whether the audit memo's "Proposed disposition" should auto-file as a FIXME at audit-authoring time, or whether B3's actioning is the durable mechanism.

2. **The S70 facade amendment (i)/(ii)/(iii) was authored as a forward target-state.** The `module_aliases` parameter, the `ModuleAliasEntry` shape, and the canonical-in-types `SymbolTables` placement are all binding-but-not-yet-delivered. This is consistent with `feedback_facade_first_migration.md` discipline — facade leads, source follows wave-by-wave. The audit's job is to surface the gap; the next action is /sprint scoping B3 against capacity.

3. **F2 + F3 are textbook `feedback_facade_first_migration.md` scenarios.** "Push cranelisp-types to target first, accept broken build, fix consumers wave-by-wave; don't negotiate." If the user wishes to defer F2/F3, the principled framing is "we defer F2/F3 to S71 because B3 capacity is constrained" — NOT "we facade-move because source ships today's shape." The latter would walk back Principle 15 + Decision 32 + BC §7 simultaneously.

4. **No /sprint-clarification items.** S69 ended with one /qa work item folded to S70 (C1+C2+C3). S70's lens is source-vs-facade; the coverage-hole class continues to be a project-wide /qa concern, not a per-crate finding. If /qa has not scheduled the fourth mechanical test (signature-shape comparator), the gap that allowed S1/S2/F1 to survive remains open. That's a /sprint scoping observation, not a finding for this memo.

5. **The audit walked the public-API surface only**. The eight BC §1 invariants (no type inference, no codegen, super-resolved-at-frontend, synthetic-span uniqueness, `expand` re-entrancy, `expand` side-effect-free for resolution, `#[non_exhaustive]` DTOs, form-by-form processing) are behavior contracts and not surfaceable through `public-api.txt`. Coverage rides on /qa's integration suite. No finding emerges from a public-API walk.

## Out-of-scope (deferred to other audits)

- **BC §1 invariant 8 — "Form-by-form, not pre-pass"**: spec §9.3.4 is named in BC §1 invariant 8 as "to be revised; until then, the frontend does not implement [the module-wide-availability model]". This is a spec-side coordination question; not a frontend facade-vs-source finding.

- **Phase 3 cascade narrative ((iv) and (v) facade additions)**: the macro lookup paragraph + deftype expander section narrate downstream consumption of Phase 3's cascaded types (`DefKind::Macro`, `DefKind::Constructor`). If Phase A delivered the type-side shapes cleanly (per /arch's signoff of Phase A), source-side consumption in `cranelisp-frontend` is the next-wave item — `/design` and `/dev` per /sprint's plan. Not a facade-vs-source drift; a delivery question.

- **Per-crate design doc refreshes**: facade amended significantly; `design/frontend/frontend.md` may need to track. /design territory.

---

**End of audit memo. Awaiting user disposition per finding at Wave B2.**
