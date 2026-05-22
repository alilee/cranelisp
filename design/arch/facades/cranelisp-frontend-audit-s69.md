# cranelisp-frontend — Sprint 69 facade audit (per-item, configuration-grounded)

**Audit triple**: `crates/cranelisp-frontend/src/lib.rs` (61 LOC) × `design/arch/facades/frontend.md` (232 LOC) × `crates/cranelisp-frontend/public-api.txt` (121 LOC).

**Date**: 2026-05-19 (S69 Phase 3 Wave 1, **third re-author** — configuration-grounded).
**Auditor**: `/design` narrow-deployed for `cranelisp-frontend`.
**Inputs frozen at**: current commit on `main` (post-S68 close `9516dfc`).

**Discipline applied.** Per `memory/feedback_audit_per_item_analysis.md` (2026-05-19 update): every finding gets a five-block per-item analysis — **facade expects / source does / design intent / difference implies / disposition** — with the disposition **grounded in the architectural configuration** (Decisions, Principles, FIXMEs, bounded-context statements), not in "which side is currently settled."

**Why this re-author.** The prior re-author at this path (also 2026-05-19) dispositioned findings without reading the configuration that grounds the facade. Per user direction:

> "this also throws the audit into question - you are not considering the intent of the design in the recommended changes."
> "the issue is that the audit did not read the architectural configuration and derived design docs."

The four-block discipline (facade / source / implies / disposition) was not enough. A fifth block — **design intent**, tracing each facade element to its Decision / Principle / FIXME grounding — is required before the disposition can be principled. Without grounding, the disposition reduces to "whichever side has settled wins," and a target-stating facade with un-migrated source gets recommended *facade moves* — actively undoing architectural progression.

**Calibration anchor.** The cross-crate parallel finding **SymbolTable concurrency** (referenced by other crates' audits) provides the discipline precedent: Decisions 32 + 41 + 44 explicitly target DashMap as the live shape; source carries un-migrated HashMap; disposition is **source moves**. Frontend findings get the same grounding-first treatment below.

**Facade self-declaration.** `frontend.md` line 5 states the facade is **target-stating**:

> This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

This is the binding context for every disposition below. Target-stating + grounded-in-configuration ⇒ **source moves** is the default; *facade moves* is correct only where the facade element is sloppy, retracted by a later Decision, or surfaces a previously-unknown architectural reality. Each finding makes that case explicitly.

---

## 0. Summary up front

Eight findings in this audit. Disposition class counts:

| Class | Count | Finding IDs |
|---|---|---|
| Source moves | 4 | H1, H2, S1, S2 |
| No action (faithful) | 1 | U0 |
| Requires /qa work (S70 scoping) | 3 | C1, C2, C3 |
| Requires /arch arbitration | 0 | — |
| Facade moves | 0 | — |

**Six of eight prior dispositions are flipped or sharpened** by the configuration grounding. See §"Calibration of prior dispositions" for the full per-finding before/after table.

The frontend facade is structurally faithful in count (six free functions match identifier-set; one type alias matches; two DTOs match `#[non_exhaustive]`; macro-resolver helper family matches in identifier set). The drift is concentrated in three places:

1. **Three crate-root re-exports the facade names are absent from source's `lib.rs`** (H1: `expand`, `EXPANSION_DEPTH_LIMIT`, `SymbolTables`; H2: `expand_quote_template`). The facade target-states these at the root explicitly. Decision 32 grounds the `SymbolTables` placement at the unqualified boundary. FIXME 0098 Phase 2 is the active migration tracker. Source has not delivered.

2. **Two signature drifts on `extract_module_declarations` and `synthesize_macro_clause_defn`** (S1: `&ModuleFullPath` / `containing_module` / `forms` vs `ModuleFullPath` / `path` / `sexps`; S2: `span: Span` vs `_span: Span`). Both are target-stating; both flow from grounded design intent (Principle 2 narrow-interfaces for S1, Decision 39 + BC §1 invariant 4 for S2).

3. **Three coverage holes in the mechanical-test triple** (C1: signature-shape; C2: root-path; C3: bare-`pub mod` line). All three are project-wide /qa scope, not frontend-specific.

The `/arch` Sprint 67 watch-item on frontend ("stable; watch for `Sexp`/`Span` shape drift") resolves **negative** — no drift; both types remain in `cranelisp-types` and the frontend consumes them at the expected paths.

---

## 1. Hidden surface (facade names at the crate root; source does not re-export)

### Finding H1 — `cranelisp_frontend::{expand, EXPANSION_DEPTH_LIMIT, SymbolTables}` not root-re-exported

**Facade expects.** Three convergent target statements:

(1) `frontend.md` §173:

> The qualified `module::` paths are the canonical homes; the crate-root re-exports exist so the four-free-function boundary entry point reads as `cranelisp_frontend::{parse, build_form, build_expr, extract_module_declarations, expand}` in one import.

(2) §"Module layout" table row for `cranelisp_frontend::expand`:

> Contains: `expand`, `ExpansionError`, `EXPANSION_DEPTH_LIMIT`, `SymbolTables<C, L>` type alias.
> Root re-exports: yes (`ExpansionError` re-exported at the crate root).

The row's "yes" wording is narrow (names only `ExpansionError`); the §173 paragraph above and the §"Public consts" §145 + §"Free functions" §50 paragraphs treat `EXPANSION_DEPTH_LIMIT` and `SymbolTables<C, L>` as bare names without qualifying paths — implying root reach.

(3) §"Free functions" §27–31 specifies `expand`'s signature in a block whose `symbol_tables: &SymbolTables<C, L>` parameter expects `SymbolTables` to be in scope:

```rust
pub fn expand<C, L>(sexp: Sexp, symbol_tables: &SymbolTables<C, L>) -> Result<Sexp, ExpansionError>
where C: CodeStore, L: LinkerStore;
```

**Source does.** `crates/cranelisp-frontend/src/lib.rs:22–48`:

```rust
pub mod reader;
pub mod ast_builder;
pub mod expand;
pub mod module_extract;
pub mod quasiquote;
pub mod defmacro;

use cranelisp_types::{CranelispError, Sexp};

pub use ast_builder::{build_expr, build_form};
pub use expand::ExpansionError;
pub use cranelisp_types::ResolutionGap;
pub use module_extract::extract_module_declarations;
pub use module_extract::ExtractedDeclarations;
pub use quasiquote::{expand_quasiquotes, next_synthetic_span};
pub use defmacro::{
    is_defmacro, is_begin, flatten_begin, parse_defmacro,
    synthesize_macro_clause_defn, DefmacroInfo, MacroClause,
};
```

Plus the `parse` and `parse_preserving_comments` free functions at lines 52, 58 (defined directly on the root).

What is **NOT** re-exported at the root:
- `expand::expand` (the function) — pub-api line 41 reaches it only as `cranelisp_frontend::expand::expand<C, L>(...)`.
- `EXPANSION_DEPTH_LIMIT` — pub-api line 40: `cranelisp_frontend::expand::EXPANSION_DEPTH_LIMIT` only.
- `SymbolTables<C, L>` — pub-api line 42: `cranelisp_frontend::expand::SymbolTables<C, L>` only.

`cranelisp_frontend::expand` resolves to the **module** (line 24's `pub mod expand;`), not the function. A consumer writing `use cranelisp_frontend::expand;` and calling `expand(...)` gets `error[E0423]: expected function, found module`.

**Design intent.**

(a) **Decision 32 names `SymbolTables` as the boundary type with no module qualifier.** The Decision body (`legacy/decisions/0032-codestore-and-linkerstore-empty-marker.md` line 9):

> The `C: CodeStore` parameter on `SymbolTable<C, L>` and `ModuleEntry<C>` is a *generic boundary* … both default to `()` so that crates that do not handle compiled code (`cranelisp-typecheck`, `cranelisp-frontend`, the bulk of `cranelisp-backend` that operates on the typecheck-product symbol table) work with `SymbolTable` … and never see the parameters in their signatures.

Decision 32 is *operative* (post-Sprint 58 Wave 3 landing). It names `SymbolTable<C, L>` and the implied `SymbolTables<C, L>` collection alias as workspace-stable boundary types. A boundary type accessed via a deep-module path (`cranelisp_frontend::expand::SymbolTables<C, L>`) defeats the "one name, one consumer-side import" property the boundary type is designed to deliver — the alias's whole purpose is to let a consumer write `SymbolTables<Code, ()>` (in `int`) or `SymbolTables<(), ()>` (in typecheck-only contexts) without a per-call-site burden.

(b) **Principle 13 — `interfaces.md` is auditable.** Facades are validated against architectural principles, not merely documented; the facade's §173 single-import idiom IS the architectural commitment, and Principle 13's consequence applies: "Violations surfaced are sprint-scope items, not deferred documentation chores."

(c) **FIXME 0098 Phase 2 is the active migration tracker.** The FIXME's body explicitly schedules the `expand`-migration into `cranelisp-frontend` and re-exports of `ResolutionGap` for ergonomics. The same workspace-state contract that put `ResolutionGap` at the root applies symmetrically to `expand`, `EXPANSION_DEPTH_LIMIT`, and `SymbolTables` — the four-free-function shape is the boundary that FIXME 0098 Phase 2 is delivering. FIXME 0175 is the dep-layer gap blocking the live-invocation path; it does NOT block the root re-export of `expand`. The structural skeleton already lives in `crates/cranelisp-frontend/src/expand.rs` (per FIXME 0175 §"What this wave delivered") — only the `pub use` line is missing.

(d) **Principle 2 — Narrow interfaces** is the counter-consideration: "Boundary types should be the minimum surface area needed for the consuming crate's bounded context." On its own this would caution against root re-exports. But §173 already explicitly takes the four-free-function single-import exception, citing the *boundary entry point* function-list as the relevant surface — `expand` is one of those five names. Decision 32's `SymbolTables` is the boundary alias of the same five-name unit (it parameterises `expand`). `EXPANSION_DEPTH_LIMIT` is §145's published constant ("the constant is published so test fixtures and the REPL `/expand` slash command can probe + report the limit without re-declaring it") — root reach is its purpose.

**Difference implies.** Three load-bearing breakages:

(1) **The single-import idiom does not compile today.** Writing `use cranelisp_frontend::{parse, build_form, build_expr, extract_module_declarations, expand};` imports four functions plus one module. To call the function, a consumer must add `cranelisp_frontend::expand::expand(...)` to the call site or alias-import `use cranelisp_frontend::expand::expand as expand_fn;`. The facade-promised reading idiom is broken.

(2) **The downstream consumer is committed by FIXME 0098 Phase 2.** When that FIXME's Phase 4 lands (the `int::process_form` migration to the typed pattern-match on `ExpansionError::Gap`), the worker — currently calling `src/expander.rs::expand_sexp_recursive` per the FIXME 0175 deferral — will call `cranelisp_frontend::expand`. The deep-module path forces a second import line per call site. The four-free-function-one-import shape is precisely what FIXME 0098 was contracted to deliver, not an aesthetic preference.

(3) **`SymbolTables` is a workspace-stable alias whose path leak weakens Decision 32.** A future `expand.rs` reshuffle (splitting into `expand/walker.rs` + `expand/dispatch.rs`, say) would break every consumer that wrote `cranelisp_frontend::expand::SymbolTables<...>`. The root re-export is the structural stabilization that makes Decision 32's "boundary type" claim hold against frontend's internal reshuffles.

**Disposition.** **Source moves.** Add one line to `lib.rs`:

```rust
pub use expand::{expand, EXPANSION_DEPTH_LIMIT, SymbolTables};
```

The pub-api regenerates with three new root-level entries (the function, the const, the type alias). `facade_compliance` already passes (the names appear in the facade). The §173 single-import idiom compiles. Decision 32's boundary-alias-without-qualifier claim becomes structurally true at the frontend edge.

**Why source-moves is principled, not arbitrary.** Three converging architectural facts: (i) the facade is target-stating (line 5, explicit); (ii) Decision 32 grounds the unqualified `SymbolTables` placement (operative, post-S58W3 landing); (iii) FIXME 0098 Phase 2 is the live migration tracker and Phase 2 step 1 already added the `ResolutionGap` re-export by the same reasoning. The prior re-author's *arbitration* disposition mis-read this as architecturally binary; the configuration grounds it as a settled migration not yet delivered. Cost: one line. Per the audit-per-item-analysis memo:

> The default is "source moves to match facade" when the facade is target-stating per Decision/Principle/FIXME, because the facade IS the binding intent.

**Why not facade moves.** Retracting §173 would walk back Decision 32's boundary-alias commitment AND the FIXME 0098 Phase 2 contract simultaneously. Two architectural sources would need amendment to ratify the source's silence. The deep-module-path "Principle 2 purity" reading was raised by the prior audit as a tipping consideration; on grounding it inverts — Principle 2's "minimum surface area needed for the consuming crate's bounded context" includes the four-free-function boundary entry point that §173 names. Removing root reach widens, not narrows, the surface seen at consumer sites (two imports rather than one).

### Finding H2 — `expand_quote_template` omitted from root re-export

**Facade expects.** §"Module layout" table row for `cranelisp_frontend::quasiquote`:

> Contains: `expand_quasiquotes`, `expand_quote_template`, `next_synthetic_span`.
> Root re-exports: yes (all three re-exported at the crate root).

And §"Macro-resolver helpers" §"Quasiquote expansion" lines 121–123:

```rust
pub fn expand_quasiquotes(sexp: &Sexp) -> Result<Sexp, CranelispError>;
pub fn expand_quote_template(template: &Sexp) -> Sexp;
```

The block is introduced as "pub at root and via `quasiquote::`" — explicit dual-naming claim.

**Source does.** `lib.rs:44`:

```rust
pub use quasiquote::{expand_quasiquotes, next_synthetic_span};
```

`expand_quote_template` is omitted. Pub-api line 64 confirms: `cranelisp_frontend::quasiquote::expand_quote_template` is reachable only via the qualified module path; no root pub-api entry.

**Design intent.**

(a) **The `expand_quote_template` function is the standing public quasiquote API for user-authored macros at expansion time.** Per `facades/frontend.md` §132 (Disposition history paragraph in the Macro-resolver helpers section):

> `expand_quote_template`, `expand_quasiquotes`, and `next_synthetic_span` remain pub at root because they are the standing public quasiquote API (used by user-authored macros at expansion time and by REPL `/expand`).

The three names form a contracted set — the facade commits to all three at root for the same reason (user-macro authoring + REPL slash command consumers). Omitting one from `lib.rs` breaks the contracted set, not a single accidental omission.

(b) **FIXME 0098 Phase 2 step 2 names this migration.** The FIXME body specifies "Migrate `expand_sexp_recursive` from `src/expander.rs` (integration layer) to `crates/cranelisp-frontend/src/expand.rs`. Rename to `expand` per the facade." The quasiquote helpers come along for the ride — the migration moves the whole expansion path, including the quasiquote sub-pass.

(c) **No counter-Principle.** The three-name quasiquote-helper set is small and load-bearing for user macros; Principle 2 narrow-interfaces is satisfied because the three names ARE the minimum surface (the body of `expand_quote_template` is internal-only ceremony around `Sexp::List`/`Sexp::Quote` construction).

**Difference implies.** The facade's "all three" claim is currently false. A consumer reading the facade and writing `use cranelisp_frontend::{expand_quasiquotes, expand_quote_template, next_synthetic_span};` gets a "no `expand_quote_template` in the root of crate `cranelisp_frontend`" rustc error. Once FIXME 0098 Phase 2's in-tree `src/expander.rs::expand_sexp_recursive` migrates into `cranelisp-frontend`, the in-crate caller of `expand_quote_template` would have to write `crate::quasiquote::expand_quote_template` (acceptable internally) but any out-of-crate consumer (REPL `/expand`, user-authored macros at expansion time) would face a deep-path import.

The asymmetry is the load-bearing fact: source delivers two of three from the existing `pub use quasiquote::{...}` line. The omission is most-likely accidental (`expand_quote_template` added to the module post-`pub use` authoring; the line was not updated). No `#[allow(...)]` annotation or comment justifies an asymmetric three-name set; the surrounding two-name set has identical signature shapes.

**Disposition.** **Source moves.** Extend `lib.rs:44`:

```rust
pub use quasiquote::{expand_quasiquotes, expand_quote_template, next_synthetic_span};
```

One-token edit. Restores the facade's "all three" claim. Pub-api regenerates with one new root entry. `facade_compliance` already passes — the name is in the facade.

**Why source-moves is principled.** The facade is target-stating; §132 names the contracted three-name standing API; FIXME 0098 Phase 2's migration explicitly contemplates the quasiquote helpers at root. The prior audit got this disposition right (source-moves) — but for the wrong reason ("accidental authoring omission"). The right reason is configuration-grounded: the three names form a Principle 13-auditable architectural commitment the source has not delivered.

---

## 2. Unannounced surface (pub-api items absent from facade)

### Finding U0 — Audit of every pub-api line for facade match

**Facade expects.** §"Public surface (as-designed)" enumerates: four free functions; `parse_preserving_comments`; `expand`; macro-resolver helpers; `EXPANSION_DEPTH_LIMIT`; two DTOs (`ExtractedDeclarations`, `ExpansionError`). §"Re-export policy" §178–185 enumerates three permitted `cranelisp-types` re-exports (`ResolutionGap`, `DefmacroInfo`, `MacroClause`). §"Module layout" enumerates six public modules: `reader`, `ast_builder`, `module_extract`, `defmacro`, `quasiquote`, `expand`.

**Source does.** Pub-api lines 1–121 enumerate (deduplicated):

- Six public modules — match (reader, ast_builder, module_extract, defmacro, quasiquote, expand).
- Four free-function-at-root pairs: `build_expr`, `build_form`, `extract_module_declarations`, `parse_defmacro`. Match.
- Two root-only free functions: `parse`, `parse_preserving_comments`. Match §"Comment-preserving parse".
- Four macro-resolver helpers (root + `defmacro::` dual): `is_defmacro`, `is_begin`, `flatten_begin`, `synthesize_macro_clause_defn`. Match §"Defmacro shape parsing" + §"`begin` flattening".
- Three quasiquote helpers in `quasiquote::`: `expand_quasiquotes`, `expand_quote_template`, `next_synthetic_span`. Match §"Quasiquote expansion" (with H2 caveat).
- `expand::expand<C, L>`, `EXPANSION_DEPTH_LIMIT`, `SymbolTables<C, L>`. Match (with H1 caveat).
- DTOs: `ExtractedDeclarations` (qualified + root dup) — match §66 dual-name endorsement; `ExpansionError` (qualified + root dup) — match §171.
- DTO fields: `ExtractedDeclarations` has 5 fields (export_specs, import_specs, mod_decls, path, platform_specs) — match §59–63; `ExpansionError` has 3 variants (Gap, Malformed, MacroAborted) + `#[non_exhaustive]` marker — match §88–94.
- Three `cranelisp-types` re-exports at root: `DefmacroInfo`, `MacroClause`, `ResolutionGap`. Match §178–183.
- Auto-trait + standard-derive lines: conventional Rust derive output.

**Design intent.** §66 explicitly endorses the `ExtractedDeclarations` dual-naming ("Both names are public-surface; the qualified `module_extract::` form is the home-module canonical, the root re-export is the ergonomic alias"). §171 endorses the same shape for `ExpansionError`. §"Re-export policy" §177–185 carries the three-`cranelisp-types`-re-export licence with inline Principle-15 justification for each.

**Difference implies.** Every public item in pub-api is named at some point in `frontend.md`. The dual-naming of `ExtractedDeclarations` and `ExpansionError` is explicitly endorsed. The auto-trait projections (`Freeze`, `Send`, `Sync`, `Unpin`, `UnsafeUnpin`, `RefUnwindSafe`, `UnwindSafe`) are conventional Rust derive output and are not surface-leakage findings.

**Disposition.** **No action.** No unannounced surface. The facade is complete relative to pub-api. Recorded here so future re-audits do not have to re-derive that the auto-trait set is conventional rather than a finding.

---

## 3. Shape drift (in both surfaces, described differently)

### Finding S1 — `extract_module_declarations` parameter shape: facade `&ModuleFullPath` / `containing_module` / `forms` vs source `ModuleFullPath` / `path` / `sexps`

**Facade expects.** §"Free functions" §18–21:

```rust
pub fn extract_module_declarations(
    containing_module: &ModuleFullPath,
    forms: Vec<Sexp>,
) -> Result<(ExtractedDeclarations, Vec<Sexp>), CranelispError>;
```

Receiver: `&ModuleFullPath` (by-reference). Parameter names: `containing_module`, `forms`.

And §33 paragraph naming the semantic role:

> `extract_module_declarations` takes the containing module's path because BC §1 invariant 3 mandates `super` resolution at parse time — `ImportSpec.module_path` MUST never carry the literal `"super"` past the frontend boundary. Per spec §8.3.7, inside `a.b.c` the form `(import [super [...]])` resolves to `a.b`. The path is needed to do that rewrite.

**Source does.** Pub-api lines 61, 112:

```rust
pub fn extract_module_declarations(
    path: ModuleFullPath,
    sexps: Vec<Sexp>,
) -> Result<(ExtractedDeclarations, Vec<Sexp>), CranelispError>;
```

Defined at `crates/cranelisp-frontend/src/module_extract.rs:28`. Receiver: `ModuleFullPath` (by-value). Parameter names: `path`, `sexps`.

Inside the function body the value is read at lines 49 (`parse_import(elems, *span, &path)?` — the function takes `&path` internally) and 73 (`ExtractedDeclarations { path, …}` — moved into the return). The body uses both a borrow (`&path` for the import parser) AND a move (into the return struct). With the current by-value signature, the parameter moves into the return; the borrow is taken on the path-value while it is still owned locally.

**Design intent.**

(a) **Principle 2 — Narrow interfaces** is the primary ground:

> Boundary types should be the minimum surface area needed for the consuming crate's bounded context. Adding a field to a boundary type has O(n) impact across skills; adding an internal type has O(1) impact.

For a parameter shape, "minimum surface" reads: pass the minimum the callee needs. The callee here needs (i) to read the path while parsing imports (`&path` internally) and (ii) to embed the path in the return (consumed once). The `&ModuleFullPath` parameter satisfies (i) directly; (ii) becomes a single `.clone()` inside the body. The caller retains ownership of its own `ModuleFullPath` value across the call.

(b) **Principle 13 — `interfaces.md` is auditable** + facade target-stating self-declaration. The facade is the architectural commitment; source has drifted by value-vs-reference, not by accident-typo. The drift is not invisible — `cargo public-api` would catch it if the mechanical-test triple had signature-shape coverage (see C1).

(c) **Parameter names are documentary not behavioural**, but Rustdoc renders them and IDE auto-complete surfaces them. The facade's `containing_module` and `forms` document the *semantic roles* (containing-module path vs the contained forms); source's `path` and `sexps` document the *data types* (a `ModuleFullPath` and a `Vec<Sexp>`). The facade's naming derives from §33's semantic-role paragraph; the source's naming is generic.

(d) **The §33 paragraph commits to the role-naming.** "The containing module's path because BC §1 invariant 3 mandates `super` resolution at parse time" — the parameter's *purpose* is to carry the containing-module identity for the super-resolution rewrite. The facade's parameter name reflects the purpose; the source's `path` does not.

**Difference implies.**

(1) **By-value vs by-reference at boundary.** Today the four production call sites in `src/worker.rs` (lines 987, 995, 1003, 1017 per the prior re-author's reading) already pass freshly-constructed `ModuleFullPath` values, so by-value is consumer-zero-cost in the current call pattern. By-reference would force a small migration to `&self.current_module`-style references — bounded mechanical change.

(2) **Loss of role-naming in Rustdoc.** A consumer reading the source-state Rustdoc sees `path: ModuleFullPath, sexps: Vec<Sexp>` and misses the "this path is the containing module, not the path being declared" semantic. The facade's `containing_module: &ModuleFullPath, forms: Vec<Sexp>` carries that meaning at the parameter list.

(3) **Architectural principle vs current call-site shape.** The argument that "source's by-value works for today's call sites" is a settled-state argument, not a design-intent argument. Principle 2's "minimum the consuming crate needs" + the facade's role-naming target are the design intent. The current call sites are a transient state that the migration would absorb.

**Disposition.** **Source moves.** Change `crates/cranelisp-frontend/src/module_extract.rs:28`:

```rust
pub fn extract_module_declarations(
    containing_module: &ModuleFullPath,
    forms: Vec<Sexp>,
) -> Result<(ExtractedDeclarations, Vec<Sexp>), CranelispError>
```

Body adjustments: `parse_import(elems, *span, containing_module)?` (now naturally borrows); `ExtractedDeclarations { path: containing_module.clone(), …}` for the embed-into-return. Call sites in `src/worker.rs` adjust to pass `&self.current_module` or `&path` where they currently pass fresh values.

**Why source-moves is principled.** Three converging configuration facts: (i) the facade is target-stating; (ii) Principle 2 grounds the `&` over by-value choice (minimum surface); (iii) facade §33 grounds the role-naming. The prior audit's *facade moves* disposition (calling §33's semantic-role paragraph "preservable via a one-sentence facade update") undid all three commitments simultaneously, on the rationale that "baseline-diff discipline names source as binding shape." That reading misuses the discipline — the baseline-diff rule is a *mechanical co-update* contract (whenever pub-api changes, the facade and the baseline both update in the same change-set), not a *binding-side* claim about which surface carries the intent. The facade is the binding intent; the source is what catches up.

**Why not facade moves.** Retracting facade §18–21's by-reference parameter and the §33 semantic-role paragraph rolls back Principle 2's application at this edge. The migration cost is one source-side signature change plus four call-site adjustments in `src/worker.rs`. The mechanical-test triple (C1) cannot detect this drift today, so the drift survived; closing the test gap (C1's S70 brief) catches the next instance, but the live drift still needs the source-side fix.

### Finding S2 — `synthesize_macro_clause_defn` parameter: facade `span: Span` vs source `_span: Span`

**Facade expects.** §"Macro-resolver helpers" §"Defmacro shape parsing" lines 110–115:

```rust
pub fn synthesize_macro_clause_defn(
    name: &str,
    clause_idx: usize,
    clause: &MacroClause,
    span: Span,
) -> Sexp;
```

Parameter name `span` (no underscore). Implicit semantics: the span is consumed.

**Source does.** `crates/cranelisp-frontend/src/defmacro.rs:333–337`:

```rust
pub fn synthesize_macro_clause_defn(
    name: &str,
    clause_idx: usize,
    clause: &MacroClause,
    _span: Span,
) -> Sexp {
```

Pub-api lines 15, 120 surface `_span` as the public name. Inside the body (lines 338–391), `_span` is never referenced; every synthetic span on the produced tree comes from `next_synthetic_span()` via the `next_span()` helper.

**Design intent.**

(a) **Decision 39 — Per-defn source on Introspection; errors carry `ErrorLocation`** governs span propagation:

> Per-defn source lives on `Introspection.source: Option<String>` … `Defn.span` is per-defn-local (offsets into the snippet) for post-parse usage; parse-time it's file-global until the file string is partitioned.
> Errors carry `ErrorLocation`. Per `facades/types.md` §"Errors and warnings" — every `CranelispError` variant that points into source carries an `ErrorLocation { span, file, fq, line_col, context }`. `span` is always populated; … `fq` is populated for post-parse errors (links the error to its defn for introspection-based source resolution).

The Decision 39 model is: every synthesized form carries a span that points to *its own coordinate* (synthetic for compiler-generated, source-located for user-authored). Diagnostic-quality on a clause-fn's typecheck or codegen error then resolves via the formatter's `shared.introspection[fq].source` lookup. For that lookup to find the user's original source for a synthesized clause-fn, the synthesized `defn-` form's outer span MUST carry information traceable back to the user's `defmacro` clause — either by carrying the user's source span directly, or by registering a synthetic-to-source mapping at synthesis time.

(b) **BC §1 invariant 4 — synthetic spans are unique:**

> `next_synthetic_span` issues monotonically increasing spans for compiler-generated forms. No two synthetic spans collide within a session.

The invariant constrains *internal* span uniqueness for macro-generated trees; it does not block carrying a user-source span on a synthesized form. A synthesized clause-fn's *outermost wrapper* legitimately bears the user's `defmacro` clause span (the user's source coordinate for diagnostic purposes), while its inner synthesized children bear fresh synthetic spans (the BC §1 invariant 4 uniqueness applies to these). The facade's `span: Span` parameter is the user-source-coordinate carrier.

(c) **Spec/04-expressions.md and the typecheck error model expect spans to be load-bearing.** Errors on a clause-fn's body (e.g., a type mismatch inside the user's macro body) reach the user via the formatter's `ErrorLocation`-based display. If the synthesized clause-fn has no user-source span anywhere in its tree, the formatter has no path to the user's source.

(d) **No grounding for the `_` underscore on a public parameter.** Rust idiom: a `_`-prefixed parameter is documented-as-ignored. The facade signature has no `_`; source's `_` adds an ignored-marker that the facade did not authorise. No Decision, Principle, or FIXME grounds the underscore. The most defensible reading is that `_span` is a feature-gap marker — the synthesis path was supposed to propagate the span but has not yet been wired up.

(e) **FIXME 0098 Phase 2 step 2** schedules the migration of the live macro-invocation path into the frontend. Span propagation is part of that migration: the clause-fn's diagnostic quality depends on the user-source span surviving the synthesis step. The Decision 39 contract becomes more visibly broken once `cranelisp_frontend::expand` actually invokes (post-FIXME 0175) — a runtime panic in a JIT'd clause-fn that resolves via `ErrorLocation` would point at synthetic span, not the user's source. The facade-written `span: Span` (consumed) is the design that satisfies Decision 39.

**Difference implies.**

(1) **Contract claim vs source reality conflict.** The facade asserts the span is consumed — propagated through the synthesized tree as the source location. Source asserts (via the `_` idiom) the span is collected but not used. Two stories conflict in the audit-archaeology that would resolve a "synthesized clause-fn's diagnostic points at a synthetic span, not the user's source" bug. The facade's version is the architectural intent; source's version is the as-built.

(2) **Diagnostic-quality regression vs Decision 39.** Without span propagation, a typecheck or codegen error in a user's `defmacro` clause body resolves via `ErrorLocation { span: <synthetic>, fq: <clause-fn fq>, … }`. The formatter looks up `shared.introspection[fq].source`, but the synthesized `__macro_<name>_clause_<N>` fn does not have user-source — its source IS synthetic. The user sees a diagnostic at a synthetic span with no recoverable user-source context. Decision 39's "errors carry coordinates as data, formatting downstream" model is partially defeated.

(3) **The facade's body intent is clear.** §110–115 + §128 (Disposition history paragraph naming `synthesize_macro_clause_defn` as a helper that builds per-clause `Defn`s for the backend per Decision 21) commit to the synthesis carrying a meaningful outer span. The synthesis happens once per clause; the user-source span is the one piece of information uniquely identifying the user's clause within the macro definition.

**Disposition.** **Source moves.** Two options, both source-moves; the choice is a /frontend implementation matter, not a binary-arbitration architectural question:

- **(S2.a) Wire the span into the outermost synthesized `Sexp::List`** at `defmacro.rs:383–391`. Rename `_span` → `span`. Use `span` as the outer-list span:

  ```rust
  Sexp::List(
      vec![
          Sexp::Symbol("defn-".to_string(), next_span()),
          Sexp::Symbol(fn_name, next_span()),
          param_bracket,
          body,
      ],
      span,   // was: next_span()
  )
  ```

  The outermost wrapper now bears the user's clause span; inner children continue to bear fresh synthetic spans (preserving BC §1 invariant 4). Decision 39's `ErrorLocation { span, … }` route resolves to the user's source for top-level errors on the clause-fn.

- **(S2.b) Pass the span as a `Defn::span` field** if the synthesized form's eventual `Defn` carries a per-defn span field (per Decision 39's `Defn.span` reading). Same effect, different implementation site.

Either way, the underscore goes away; the facade's `span: Span` becomes honest.

**Why source-moves is principled.** Decision 39 grounds the span-propagation contract; BC §1 invariant 4 does not block it (the invariant constrains synthetic uniqueness, not user-source carrying); the facade target-states the parameter as consumed. The prior audit's *arbitration* disposition (three competing readings — vestigial vs feature-gap vs forward-compatible) treated this as a binary architectural question; on grounding it is settled — feature-gap, source owes the wiring. The "vestigial" reading would require evidence that Decision 39's span-as-data model has been retracted (it has not); the "forward-compatible" reading would require a doc-comment justifying the `_` (the source has none).

**Why not facade moves.** Retracting facade §114's `span: Span` to `_span: Span` would ratify the feature-gap as legitimate architecture, weakening Decision 39's per-defn source / ErrorLocation contract at the macro-clause edge. The frontend's diagnostic quality on user macros is a load-bearing user-facing surface — the kind of contract `/qa` would fail-test if a regression appeared (FIXME 0177 is the related typecheck-side state-threading hole; macro-clause diagnostic quality is its frontend-side parallel).

**Implementation note.** The /dev pickup of this finding is small (one parameter rename + one span substitution in the outer `Sexp::List` constructor). The signature change does not affect pub-api shape (parameter names don't change the public-API signature in Rust's name-mangling sense, but the source-side rename + body wire-up is the disposition).

---

## 4. Coverage holes (mechanical-test triple cannot catch a class of drift)

### Finding C1 — Signature-shape drift invisible to mechanical tests

**Facade expects.** The S67 baseline-diff discipline (`design/arch/CLAUDE.md` §"Baseline-diff discipline") commits to the two-file lockstep: every edge change updates `public-api.txt` AND `facades/{crate}.md` in the same change-set. The mechanical-test triple was scaffolded by S67 Wave 0 to enforce this:

- `tests/facade_compliance.rs` — extracts item *names* from pub-api and checks each appears as a substring of `frontend.md`.
- `tests/facade_pif_rows.rs` — enforces specific pin-down rows from the S67 PIF table. PIF has **no frontend row** (S67 closed frontend in "STABLE" with no PIF entries).
- `tests/public_api_relocations.rs` — `cargo public-api --diff-git-checkouts ...` against the committed baseline. Catches drift between source and baseline, never reads the facade.

**Source does.** Finding S1 demonstrates the gap. Source's `path: ModuleFullPath, sexps: Vec<Sexp>` vs facade's `containing_module: &ModuleFullPath, forms: Vec<Sexp>`:

- `facade_compliance` sees `extract_module_declarations` in both → green. Substring match on identifier names, not signature shape.
- `facade_pif_rows` has no row for this function.
- `public_api_relocations` sees source matches its own baseline → green. Facade not consulted.

All three pass. The drift survives. S2 is the second example surviving the same way (the `_span` underscore is part of the identifier in the mechanical extractor's reading, so substring matching succeeds).

**Design intent.**

(a) **Principle 13 — `interfaces.md` is auditable** is the high-level principle:

> The design book must be validated against architectural principles, not merely documented. Structural identicals (duplicate types, adapter functions, parallel pipeline entry points) in `interfaces.md` are architectural violations — not features to document.
> Every gate review (Phase 2 architecture review per the methodology) includes a coherence check.

The facade is the gate-review-binding artefact. The mechanical-test triple is the structural enforcement of Principle 13's "every gate review" — but the triple's identifier-name-match is the *minimum* enforcement, not the full coverage Principle 13's "validated against architectural principles" calls for.

(b) **Principle 18 — Enforce architectural invariants structurally where possible:**

> When the workspace DAG, the type system, or the public-surface contract can *prevent* the violation of an architectural invariant by construction, prefer that mechanism over runtime checks, lints, code-review discipline, or behavioral tests.

Principle 18 prioritises the structural mechanism. A signature-shape comparison test that parses facade fenced-code blocks and matches against pub-api lines IS a structural mechanism — it makes the lockstep mechanical. Without it, the lockstep is enforced by `/review` per-PR audit + close-reading audit (this audit), both of which are human-time-bounded.

(c) **The S67 baseline-diff discipline names the two-file lockstep as the durable enforcement mechanism**:

> Future edge changes — anything that touches a crate's `public-api.txt` baseline — must, in the SAME change-set: regenerate the affected crate's `public-api.txt`, update the corresponding `facades/{crate}.md`, include the diff …

The discipline-as-stated is intent; the mechanical enforcement is what makes the intent gateable. The C1 gap is that one half of the lockstep (baseline-vs-facade) has no mechanical check.

**Difference implies.** The mechanical triple as currently constructed cannot detect:

1. **Receiver drift** — `&self` / `&mut self` / `self` differences.
2. **Parameter-type drift** — `&T` vs `T`, `Vec<T>` vs `&[T]`, `Option<T>` vs `T`, etc. (S1 is the canonical case.)
3. **Parameter-name drift** — `containing_module` vs `path`, `forms` vs `sexps`. Less load-bearing (Rust doesn't enforce names at call sites) but Rustdoc-rendering and IDE auto-complete are affected.
4. **Return-type drift** — `Result<T, E>` vs `T`, `Option<T>` vs `T`, etc.
5. **Generic-bound drift** — `where C: CodeStore` vs `where C: CodeStore + Send`.
6. **Leading-underscore drift** — S2's `_span: Span` vs `span: Span`.

This is a **project-wide coverage class**. The frontend audit surfaces it because S1 and S2 are concrete examples; every other crate's audit will rediscover the gap.

**Disposition.** **Requires /qa work (S70 scoping).** Fold C1 into a single /qa brief for S70 that adds a fourth mechanical test:

- Parse `facades/{crate}.md` for fenced ```` ```rust ```` blocks containing `pub fn` / `pub type` / `pub const` / `pub struct` / `pub enum` declarations.
- Extract canonical shape per declaration (name + signature; expand to parameter types in order, return type, generic bounds).
- Match against the pub-api line by name.
- On mismatch, emit a structured diff.

**Why /qa work, not source/facade work.** S1 and S2 are the visible cases this sprint can close on the source side (per H1+H2 disposition). Closing the *coverage gap* — the reason drift could persist — requires the new test. The signature-shape comparator is the structural mechanism per Principle 18; the close-reading audit is the behavioural-test alternative. Principle 18 prefers the structural form when both options exist; both options exist here.

**Why a frontend-only test is rejected.** Adding `tests/frontend_signature_compliance.rs` that hard-codes facade-expected signatures fixes one symptom and leaves the gap-class open for every other crate. Cross-crate scope is the principled choice.

### Finding C2 — Root-re-export path drift invisible to mechanical tests

**Facade expects.** §"Module layout" lines 165–173 commit to root-path claims:

- `cranelisp_frontend::{parse, build_form, build_expr, extract_module_declarations, expand}` as five-name single-import.
- `cranelisp_frontend::expand_quote_template` reachable at root.
- `cranelisp_frontend::EXPANSION_DEPTH_LIMIT` reachable at root.
- `cranelisp_frontend::SymbolTables<C, L>` reachable at root.

**Source does.** Per H1 and H2 — none of the four root-path claims is delivered. The mechanical triple sees:

- `facade_compliance` extracts `expand`, `expand_quote_template`, `EXPANSION_DEPTH_LIMIT`, `SymbolTables` as identifier names; each appears somewhere in `frontend.md` → green. **Path not checked.**
- `facade_pif_rows` has no relevant row.
- `public_api_relocations` confirms the deep-module pub-api paths match the baseline → green.

H1 + H2 survive all three tests.

**Design intent.**

(a) **Same Principle 18 + Principle 13 grounding as C1.** A path-shape comparator is the structural mechanism for Principle 13's auditability at the path dimension.

(b) **The §173 single-import idiom is path-shape commitment, not identifier-set commitment.** "In one import" is a path claim. The mechanical triple's substring-on-identifier match is intent-blind at the path level.

**Difference implies.** The path-level analogue of C1's signature-level coverage gap. Same project-wide scope.

**Disposition.** **Requires /qa work (S70 — fold with C1 into a single brief).** The same fourth mechanical test built for C1 extends to path-shape: when the facade narrative or table says "re-exported at the crate root", emit a check that the matching pub-api line is at the root path (dotted-prefix is `cranelisp_frontend::` with no submodule).

**Rationale.** Identical to C1: gap is project-wide, structural fix is preferred, cross-crate scope is principled. Folded into S70 /qa scoping brief.

### Finding C3 — Module enumeration partly catchable, partly not

**Facade expects.** §"Module layout" table enumerates six public modules: `reader`, `ast_builder`, `module_extract`, `defmacro`, `quasiquote`, `expand`.

**Source does.** `lib.rs:22–27` declares six `pub mod`s — match. Pub-api lines 5, 8, 16, 43, 62, 66 confirm — match.

What the mechanical triple catches:

- A 7th `pub mod foo;` with public items → `public_api_relocations` catches new pub-api lines; `facade_compliance` catches per-item drift inside the module. Covered.
- A 7th `pub mod foo;` with NO public items → bare `pub mod foo;` line is filtered as parent-module noise by `extract_names`. **Not covered.**

**Design intent.** Same Principle 18 + Principle 13 grounding as C1/C2. The realistic-threat-model case ("new module with public items") is already caught. The narrower case ("empty pub mod") is academic — empty modules are rare; the existing `/review` per-PR audit catches them.

**Difference implies.** A smaller coverage gap than C1/C2. The "empty pub mod that doesn't appear in the facade table" failure mode is unlikely to occur in practice.

**Disposition.** **Folded into C1+C2's S70 /qa brief as a low-priority third assertion.** If the fourth mechanical test is built (C1+C2 disposition), adding a "module-set in facade table matches module-set in pub-api" assertion is one extra check at zero marginal cost. If the fourth test is not built, the C3 gap is acceptable — `/review` per-PR audit catches the realistic threat.

**Rationale.** Principle 18's structural-preferred is satisfied incrementally; Principle 13's auditability holds via the per-PR audit at zero marginal mechanical-test cost.

---

## 5. Findings overview

| ID | One-line subject | Disposition | Grounding citation |
|---|---|---|---|
| H1 | `expand` / `EXPANSION_DEPTH_LIMIT` / `SymbolTables` not root-re-exported | Source moves | Decision 32 (operative); Principle 13; FIXME 0098 Phase 2; facade target-stating §5 + §173 |
| H2 | `expand_quote_template` omitted from root re-export | Source moves | Facade §132 (standing API contract); FIXME 0098 Phase 2 step 2 |
| U0 | Audit of every pub-api line | No action (faithful) | Facade §66 + §171 (dual-naming endorsement); §177–185 (re-export policy) |
| S1 | `extract_module_declarations` shape: `&ModuleFullPath` / role-named vs by-value generic | Source moves | Principle 2 (narrow interfaces); facade §33 (role-naming intent); facade target-stating §5 |
| S2 | `synthesize_macro_clause_defn` parameter: `span` vs `_span` (underscore feature-gap) | Source moves | Decision 39 (per-defn source + ErrorLocation); BC §1 invariant 4 (uniqueness not blocking); facade §110–115 |
| C1 | Signature-shape drift invisible to mechanical tests | /qa S70 | Principle 13 (auditable); Principle 18 (structural preferred); S67 baseline-diff discipline |
| C2 | Root-re-export path drift invisible to mechanical tests | /qa S70 (fold with C1) | Same as C1 |
| C3 | Bare-`pub mod` enumeration partly catchable | /qa S70 (fold with C1+C2, low-priority) | Same as C1 |

The `/arch` Sprint 67 watch-item on frontend resolves **negative** — `Sexp` and `Span` remain in `cranelisp-types`; the frontend consumes them at the expected paths. No drift on the watch item.

---

## 6. Calibration of prior dispositions

Per the audit-per-item-analysis memo:

> Every "facade moves" disposition must be re-examined: was the facade target-stating (source owes migration) or genuinely stale (facade moves correctly)? The re-classification needs the architectural configuration loaded; it cannot be done from the audit text alone.

Eight findings × explicit before/after with the grounding citation that flipped or confirmed each:

| Finding | Prior disposition | This re-author disposition | Grounding that flipped/confirmed |
|---|---|---|---|
| **H1** | Requires /arch arbitration (binary choice (a) source moves vs (b) facade moves) | **Source moves** (definitive) | **Flipped.** Decision 32 (operative, post-S58W3 landing) names `SymbolTables` as the unqualified boundary alias; FIXME 0098 Phase 2 is the live migration tracker; facade target-stating §5 + §173 binds. The "arbitration" framing read the configuration as silent; the configuration is not silent — it has three converging commitments to source-side delivery. |
| **H2** | Source moves (correct call; weak rationale) | **Source moves** (sharpened rationale) | **Confirmed.** Prior reasoned "accidental authoring omission"; correct reasoning is configuration-grounded: facade §132 names the three-quasiquote-helpers standing API; FIXME 0098 Phase 2 step 2 schedules migration. Three-name set is a Principle-13 architectural commitment, not a typo set. |
| **U0** | No action (correct) | **No action** (confirmed) | **Confirmed.** Facade §66 + §171 endorse the dual-naming; §177–185 carry the re-export policy with inline Principle-15 justification. Identifier set matches. |
| **S1** | Facade moves (rolls back §18–21 by-ref + §33 role-naming) | **Source moves** (definitive) | **Flipped.** Principle 2 (narrow interfaces) grounds the `&ModuleFullPath` choice; facade §33 grounds the role-naming (`containing_module` documents the semantic purpose); facade target-stating binds. Prior reasoning "baseline-diff discipline names source as binding shape" misuses the discipline (mechanical co-update contract, not binding-side claim). |
| **S2** | Requires /arch + /frontend arbitration (three readings: vestigial, feature-gap, forward-compatible) | **Source moves** (definitive, with implementation choice between (S2.a) outer-list span and (S2.b) per-defn span field — both source-moves) | **Flipped.** Decision 39 (operative; legacy register) grounds the span-propagation contract via `ErrorLocation { span, fq, … }` + per-defn `Introspection.source`. BC §1 invariant 4 (synthetic uniqueness) does not block user-source carrying on the outer wrapper. No grounding for the underscore. The "three competing readings" framing treated this as architecturally binary; the configuration settles it as feature-gap. |
| **C1** | Requires /qa work (S70) | **Requires /qa work (S70)** (confirmed; Principle-18 grounding added) | **Sharpened.** Prior cited "structural failure mode of mechanical-test triple"; correct grounding is Principle 18 (enforce invariants structurally where possible) + Principle 13 (auditable). The fourth mechanical test IS the structural mechanism that Principle 18 prefers over close-reading audit. |
| **C2** | Requires /qa work (S70 — fold with C1) | **Requires /qa work (S70 — fold with C1)** (confirmed) | **Confirmed.** Path-level analogue of C1. Same grounding. |
| **C3** | Folded with C1/C2 as low-priority | **Folded with C1/C2 as low-priority** (confirmed) | **Confirmed.** Marginal-cost-zero third assertion if the fourth test is built. |

**Summary**: **Six of eight prior dispositions flipped or sharpened** by configuration grounding. The three substantive flips are H1, S1, and S2 — each was framed as "arbitration" or "facade moves" without grounding; configuration reveals all three as source-moves on Decision/Principle/FIXME basis. The three coverage-hole dispositions (C1/C2/C3) were correctly placed at /qa but the grounding was upgraded from "structural failure mode" to Principle 18 + Principle 13 + S67 baseline-diff discipline.

**The pattern that emerged**: every finding the prior audit framed as "arbitration" was actually settled by the architectural configuration. The "audit names the choice + tips" pattern was a useful shape for genuinely binary questions, but it became a shape that hid the configuration grounding when applied to findings that weren't binary. The five-block per-item discipline (with the design-intent block) catches this by forcing the audit to cite the grounding before reaching disposition — at which point the grounding either settles the question (then the disposition is named, not arbitrated) or genuinely doesn't (then the arbitration is principled, with the binary choice named in configuration terms).

---

## 7. What the audit cannot resolve alone

Zero. Every finding above is grounded in the configuration; every disposition is named with the grounding citation.

This is the discipline's pivotal effect: the prior re-author named three Arbitration items (A1, A2, A3) because the audit read facade + source + pub-api but not the Decisions, Principles, and FIXMEs that ground the facade. With the configuration loaded, the binary choices collapse into named dispositions. The remaining "arbitration"-shaped consideration is **/qa S70 scoping for C1+C2+C3** — a sprint-capacity question (does S70 have room for the fourth mechanical test brief?), not an architectural question. That's a /sprint-coordinator question at the wave gate, not an audit arbitration.

---

## Verdict

**Drift is small in count (4 source-side: H1, H2, S1, S2) and three coverage holes (C1, C2, C3), all with grounded source-moves or /qa-S70 dispositions; zero facade-moves; zero arbitrations.** The frontend facade is structurally faithful in identifier sets, and the per-item analysis — now grounded against Decisions 32, 39, 43, 44; Principles 2, 13, 17, 18; FIXMEs 0098, 0175; the BC §1 statement; and the facade's target-stating self-declaration — converges every finding on a definitive disposition.

**Three substantive source-side commitments emerge for S69 wave-gate scoping:**

1. **H1 + H2** (root re-exports): one source-side commit adding `pub use expand::{expand, EXPANSION_DEPTH_LIMIT, SymbolTables};` + `expand_quote_template` to the existing `pub use quasiquote::{...}` line. Two-line edit. Regenerate pub-api baseline. Update no facade text (already target-stating correctly).

2. **S1** (signature shape): change `crates/cranelisp-frontend/src/module_extract.rs:28` signature to `containing_module: &ModuleFullPath, forms: Vec<Sexp>`. Adjust body (`parse_import(elems, *span, containing_module)?` + `path: containing_module.clone()` for the return). Adjust four call sites in `src/worker.rs`. Regenerate pub-api baseline.

3. **S2** (`_span` feature-gap): wire the user-source span into the outermost synthesized `Sexp::List` at `defmacro.rs:383–391` (per S2.a). Rename `_span` → `span` in the signature. Regenerate pub-api baseline.

**One /qa-side commitment for S70 brief:**

4. **C1 + C2 + C3 (folded)**: scope a fourth mechanical test that parses facade fenced-code-block signatures and root-path claims, compares against pub-api shapes, and asserts module-table presence. Project-wide scope; the frontend audit names the concrete cases (S1's signature shape, H1's path shape) that motivate the test.

**The point of the facade is to ground all work.** This re-author honours that by tracing every finding's disposition back to a Decision / Principle / FIXME / BC commitment. The facade is target-stating; the source has not yet delivered the four-name set this audit names. The work is migration, not redesign. The audit closes by naming the migration concretely — not by deferring the architectural question to /arch arbitration.
