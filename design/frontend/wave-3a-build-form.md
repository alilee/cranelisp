# Frontend — Sprint 66 Wave 3a — `build_form` shape pivot + `expand` migration

> Subordinate topic doc for `crates/cranelisp-frontend/`. Owned by `/design`.
>
> **Master.** `design/frontend/frontend.md` (this doc is an elaboration).
> **Public surface contract.** `crates/cranelisp-frontend/src/lib.rs` //! preamble + per-item rustdoc; `bounded-contexts.md` §1 (target public surface; normative — the per-crate `facades/frontend.md` document was retired in S70 Phase B group B3-C).
> **Slice.** `design/frontend/implementation-slice-s66.md` (predates FIXME 0156 resolution; rows 5/6 are SUPERSEDED by this doc — `build_ast`/`build_expr` per-form pair is collapsed into `build_form -> Vec<ParsedEntry>` plus `build_expr -> Expr`).
> **Driving FIXMEs.** 0156 (`build_form` shape), 0098 Phase 2 (`expand` migration), 0167 + 0168 (Decision 44 amendments — cluster-atomic shape).

This doc specifies the concrete delta `/dev` must land in Wave 3a-β for the frontend crate. It does not edit source. It supersedes rows 5/6 of `implementation-slice-s66.md` and refines row 7 (`expand`) against the now-final cluster-atomic shape (Decision 44, Pattern B per Decision 45, locality per Principle 17, Decision 46 sequencing).

---

## 1. Wave 3a frontend deliverables — restatement

Per `sprints/SPRINT.md` Wave 3a (lines 230–238):

> frontend: `build_form -> Vec<ParsedEntry>` (FIXME 0156); `expand` migration completes (FIXME 0098 Phase 2)

These are the two frontend rows of the **critical-path triad** (frontend + typecheck + int — Wave 3a-β). The architectural prerequisites for typecheck and int — Pattern B impl storage, Principle 17 locality, FQ-at-registration, match exhaustiveness via FQ home module — all landed in Wave 3a-α and are not in frontend scope. Frontend's job is purely the producer-side change at the parse → typecheck boundary so the orchestrator can drive cluster-atomic typecheck on a per-`ParsedEntry` granularity.

---

## 2. Target shape of `build_form`

### 2.1 Signature

```rust
pub fn build_form(sexp: &Sexp) -> Result<Vec<ParsedEntry>, CranelispError>;
```

`Vec<ParsedEntry>` (not `ParsedEntry`) because some source shapes yield more than one entry per source form:

- **`(defmacro name clause₁ clause₂ ...)`** → one `ParsedEntry::Macro { info: DefmacroInfo { clauses: [...] , ... } }` carrying ALL clauses. The clauses are inside `DefmacroInfo`; `build_form` does NOT emit one `ParsedEntry::Macro` per clause. (The per-clause `Defn` synthesis is `int`'s work via `synthesize_macro_clause_defn` after typecheck stages the macro entry.)
- **`(deftype Name … (Variant₁ fields₁) (Variant₂ fields₂) ...)`** → one `ParsedEntry::TypeDef { ... }` PLUS one `ParsedEntry::Constructor { ... }` per variant. So a 3-constructor sum type yields a 4-element vector: 1 TypeDef + 3 Constructors.
- **`(defn name [params] body)`** → exactly one `ParsedEntry::Def`. The DefnMulti shape (multiple `(params body)` arms inside one `defn`) is represented in `DefnVariant`s inside the single `Def`'s `variants` field — still one `ParsedEntry`.
- **`(deftrait Name … (method sig)*)`** → exactly one `ParsedEntry::TraitDecl`.
- **`(impl Trait Type method-defns…)`** → exactly one `ParsedEntry::TraitImpl`.

### 2.2 Dispatch

`build_form` is the single public form-shape entry. It dispatches on the form head (after the existing `parse_def_visibility` peel for `defn`/`deftype`/`deftrait` visibility variants, and explicit head match for `impl`/`defmacro`). The dispatcher calls `pub(crate)` helpers:

```rust
pub fn build_form(sexp: &Sexp) -> Result<Vec<ParsedEntry>, CranelispError> {
    match peel_head(sexp)? {
        FormHead::Defn { vis, .. }      => parse_defn(sexp, vis).map(|e| vec![e]),
        FormHead::Deftype { vis, .. }   => parse_deftype(sexp, vis), // returns Vec — TypeDef + Constructors
        FormHead::Deftrait { vis, .. }  => parse_deftrait(sexp, vis).map(|e| vec![e]),
        FormHead::Impl                  => parse_impl(sexp).map(|e| vec![e]),
        FormHead::Defmacro { vis, .. }  => parse_defmacro_form(sexp, vis).map(|e| vec![e]),
        FormHead::OtherTopLevel(head, span) => Err(parse_err(format!("unknown top-level form: {head}"), span)),
        FormHead::Expr => Err(parse_err("bare expressions are not top-level forms; use build_expr", sexp.span())),
    }
}
```

Two helpers warrant naming:

- `parse_deftype` returns `Result<Vec<ParsedEntry>, _>` (the only multi-entry per-form helper); the TypeDef appears first, followed by Constructors in source-declaration order.
- `parse_defmacro_form` wraps the existing `parse_defmacro` (which already returns `DefmacroInfo`) and packages it as `ParsedEntry::Macro { info }`. The existing `parse_defmacro` stays `pub(crate)` per facade row 12 + 16.

### 2.3 What `build_form` does NOT accept

- **`(begin ...)`** — never reaches `build_form`. The orchestrator (`int::process_cluster`) unwraps `(begin form₁ … formN)` at the REPL-input boundary BEFORE calling `build_form`, and calls `build_form` on each inner form independently. The resulting `ParsedEntry` lists are concatenated to form the cluster's parsed-entry list. The flatten helper is the existing `cranelisp_frontend::flatten_begin` (public, unchanged by this wave). See §4 below for the orchestrator-side contract.
- **Structural decls (`mod`/`mod-`/`import`/`export`/`platform`)** — peeled off by `extract_module_declarations` BEFORE `build_form` ever runs (per Decision 33 + BC §1 invariant 3, structural extraction precedes form-by-form processing). If a structural-decl shape reaches `build_form`, that is a caller bug — surfaced as a parse-error.
- **Bare expressions** — REPL eval calls `build_expr(sexp) -> Expr` directly. `build_form` rejects bare expressions because top-level forms have a defined vocabulary (`defn` / `deftype` / `deftrait` / `impl` / `defmacro`); anything else is either a structural decl already peeled off, or a bare expression for `build_expr`. The classifier at the REPL/batch rim decides which.

### 2.4 Lifecycle invariants

The `ParsedEntry` values returned by `build_form` are **transient**: they live in orchestrator-local memory for the duration of one cluster's processing (Decision 44; FIXME 0167's Approach B). They are passed to `check_form_signatures` and then `check_form_body` (one cluster's Pass 1 and Pass 2 respectively); on Pass 2 success the orchestrator commits staging into live and the `ParsedEntry` values drop with the function frame.

The frontend's commitment:

1. **`ParsedEntry` NEVER lands in `SymbolTable`** — `build_form`'s output is owned by the orchestrator and consumed exhaustively. Nothing the frontend produces aliases into the live or staging tables.
2. **`ParsedEntry` is `Clone`** — orchestrator may clone for retry-on-Gap (Decision 44 §"On Err(Gap) from any pass, the orchestrator retries the same pass"). The clone is cheap because parser-stage payloads are small (a few owned strings + a `Sexp` body subtree); resolved-stage payloads (callees, schemes, code) are not yet attached.
3. **`ParsedEntry` is NOT `Serialize`/`Deserialize`** — transient, never persisted to module cache. The cache writes `ModuleEntry` (post-typecheck/post-codegen) only.

These match the as-already-authored `cranelisp-types::parsed::ParsedEntry` per `cranelisp-types/src/parsed.rs:23–61`. The types crate is correct; the frontend producer side is the gap.

---

## 3. `ParsedEntry` type — already authored

`ParsedEntry` and `DefmacroInfo` are already in `cranelisp-types::parsed` (per public-api.txt line 122–129; FIXME 0156 Wave B already executed the types-side authoring). The frontend's wave does not author new types; it consumes the existing types-crate shape.

The variants in `cranelisp-types::parsed::ParsedEntry` are: `Def`, `TypeDef`, `TraitDecl`, `TraitImpl`, `Macro`, `Constructor`. These match the facade exactly. **No FIXME against `/arch` is needed for new types.**

One field-level note: `DefmacroInfo::clauses` is `Vec<MacroClause>` (where `MacroClause` is also in `cranelisp-types::parsed`) carrying `body_sexp` per clause, because the frontend's `synthesize_macro_clause_defn` consumes it after the orchestrator stages the macro entry. This is the producer/consumer shape Decision 21 commits to.

---

## 4. How `(begin ...)` clusters parse into multiple `ParsedEntry` values

The cluster boundary is **orchestrator-side**, not frontend-side. The frontend is form-shape-blind to whether a form is part of a cluster.

### 4.1 REPL input — one cluster per input line

Per spec §5.13.2 (extended by /spec to non-macro defns per FIXME 0167 resolution context):

- **Non-`begin` REPL input** `(defn f [] 1)` → one cluster of one `ParsedEntry` (`Def`). The orchestrator calls `build_form(&sexp)` once, gets `vec![ParsedEntry::Def { name: "f", … }]`, treats that one-element vector as the cluster's parsed-entry list.
- **`begin` REPL input** `(begin (defn f [] (g 1)) (defn g [x] x))` → one cluster of two `ParsedEntry::Def`s. The orchestrator detects the `begin` head (via existing `cranelisp_frontend::is_begin`), unwraps via `flatten_begin`, calls `build_form` on each inner form, concatenates the resulting `Vec<ParsedEntry>` lists, and treats the concatenated list as the cluster's parsed-entry list. Pass 1 (`check_form_signatures`) runs across all entries; Pass 2 (`check_form_body`) runs across all entries; staging commits atomically on Pass 2 Ok.

The frontend's contribution is purely the `build_form` per-form call. It does **not** know about clusters. `is_begin` and `flatten_begin` remain public helpers (facade rows 15) for the orchestrator's use.

### 4.2 `begin` invariants — orchestrator-enforced

Two `begin`-shape invariants live on the orchestrator side, NOT the frontend:

1. **`begin` is invalid at batch top-level.** A `.cl` file's non-structural forms are themselves one cluster (per spec §5.13.1's MAY-reference-freely rule at file scope); wrapping any subset in `(begin …)` is redundant and the orchestrator rejects it with a clear error. The frontend's `build_form` is form-shape blind; if the orchestrator passes a `begin` form to `build_form`, that is an orchestrator bug and surfaces as the existing `reject_pre_ast_forms` error ("begin should be handled before AST building"). The reject path already exists in `ast_builder.rs:178` and is preserved.
2. **Module-phase decls forbidden inside begin clusters.** `(begin (import [m]) (defn f [] …))` is rejected — `import`/`export`/`mod`/`platform` must appear at the source top level, not nested inside a `begin`. The orchestrator enforces this by walking each form's head BEFORE calling `build_form`; if any nested form head is a structural-decl head, the orchestrator emits the rejection. `build_form` itself does not see structural decls (they're already peeled off at the source top level by `extract_module_declarations`), so this is purely an orchestrator-side check inside the `flatten_begin` consumption path.

Both invariants are documented in the orchestrator's `facades/int.md` §"`process_cluster` — the cluster-atomic orchestration loop". They are NOT frontend concerns; this design doc records the contract so `/dev` frontend knows what `build_form` does NOT need to validate.

### 4.3 Empty `begin` and one-form `begin`

- `(begin)` (empty) → orchestrator-side handling: empty cluster, no-op, returns success. `build_form` is never invoked. Documented in `facades/int.md`; not a frontend concern.
- `(begin (defn f [] 1))` (one-form) → orchestrator processes as a one-element cluster; `build_form` called once for the inner `defn`; semantically equivalent to the bare `(defn f [] 1)` REPL input but legal (Decision 44 — `begin` is the **explicit** multi-form cluster boundary, but the orchestrator does not reject single-form `begin`s as they are useful for macro-generated code that may or may not produce multiple forms).

---

## 5. `expand` migration (FIXME 0098 Phase 2)

Per the master design §5 and the facade §"Free functions" (`expand` row), the migration moves `expand_sexp_recursive` from `src/expander.rs` into `crates/cranelisp-frontend/src/expand.rs` with three target-state shapes:

### 5.1 Target signature

```rust
pub fn expand<C, L>(sexp: Sexp, symbol_tables: &SymbolTables<C, L>) -> Result<Sexp, ExpansionError>
where
    C: CodeStore,
    L: LinkerStore;

pub type SymbolTables<C, L> = DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>;

#[non_exhaustive]
pub enum ExpansionError {
    Gap(ResolutionGap),
    Malformed { message: String, span: Span },
    MacroAborted { fq: FQSymbol, message: String, span: Span },
}
```

`ResolutionGap` re-exported from `cranelisp-types` via the narrow ergonomic exception per Principle 15 (facade §"Types originated here").

### 5.2 What changes from the source-of-truth in `src/expander.rs`

1. **No `MacroResolver` trait.** Per Decision 8 (retracted as part of D43/Principle 15 reframing): lookup goes directly against `&symbol_tables`. Macro entries are reachable through `SymbolTables[module].get(&name)` as `ModuleEntry::Def { kind: DefKind::Macro { clauses_meta }, .. }` parent entries (per S69 Submission 13 macro-unification — `ModuleEntry::Macro` retired); the JIT'd code pointer for each clause is on its mangled-variant `ModuleEntry::Def`'s `code: Option<C>` field (`{macro}$clause-{N}` entries). Frontend never names `Jit` / `Linker` — only `Some(code)`.
2. **Single uniform Gap variant.** Per the BC contract (`bounded-contexts.md` §1 invariant #6 + the `ExpansionError` per-item rustdoc on `crates/cranelisp-frontend/src/expand.rs`): every dependency-not-ready case (`module unregistered`, `typecheck incomplete`, `code missing`) surfaces as `Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))`. The orchestrator decides what to wait on after retrieving the entry post-wait (macro-vs-fn discrimination is scheduler-side knowledge — see `facades/int.md` for the wait sequence). The frontend does NOT distinguish "module not registered" from "code not loaded" — both become the same Gap variant.
3. **Depth limit becomes a `Malformed` diagnostic.** Per master §5.2: the existing `EXPANSION_DEPTH_LIMIT = 100` defensive guard is retained but surfaces as `ExpansionError::Malformed { message: "macro expansion depth exceeded (NN)", span }` rather than silent truncation. This is a behaviour preservation (limit fires only on runaway expansion) plus a diagnostic upgrade (the user sees what happened).
4. **`Send + Sync` free function.** Multiple workers may call `expand` concurrently against the same `&symbol_tables` (per Decision 38 — `SymbolTable`'s inner DashMap supports concurrent read). No internal synchronisation needed beyond what `SymbolTable` provides.
5. **`expand` IS re-entrant.** A macro expansion may produce a form that itself contains macro calls; `expand` recursively expands the output. The depth limit applies to total nesting, not per-call.

### 5.3 What stays the same

- Quasiquote desugaring (`` ` ``/`~`/`~@`) — already lives in `cranelisp_frontend::quasiquote::expand_quasiquotes`, runs unconditionally on every form before macro-call dispatch. Public surface unchanged.
- `is_defmacro`, `is_begin`, `flatten_begin` — public helpers unchanged.
- `next_synthetic_span` — public atomic counter unchanged.
- `parse_defmacro`, `synthesize_macro_clause_defn` — public functions retained per facade rows 12, 13. (Internally, `parse_defmacro` is called by `parse_defmacro_form` inside `build_form`'s dispatcher; the standalone public `parse_defmacro` continues to exist for callers that consume `DefmacroInfo` directly — primarily `int`'s post-`build_form` macro-clause-defn synthesis path.)

### 5.4 `MacroResolver` removal (cross-skill coordination)

The frontend wave authors the new `cranelisp_frontend::expand` and the `SymbolTables<C, L>` alias. The `MacroResolver` trait deletion in `src/expander.rs` is `int`-wave work (Phase 4 of FIXME 0098). Frontend's wave delivers a callable replacement; `int`'s wave switches call sites and deletes the trait. The two waves may proceed in parallel after this design lands, and `int` waits on the frontend wave landing for the deletion to be sound.

---

## 6. Frontend's facade-compliance delta

Cross-referencing `crates/cranelisp-frontend/public-api.txt` (as-built) against the lib.rs //! preamble (as-designed; post-S70 B3-C the canonical home for the frontend surface contract):

### 6.1 Entries to add

| New public item | Origin |
|---|---|
| `pub fn build_form(sexp: &Sexp) -> Result<Vec<ParsedEntry>, CranelispError>` | §2 above |
| `pub fn build_expr(sexp: &Sexp) -> Result<Expr, CranelispError>` | Facade §"Free functions"; lifted from existing internal helper in `ast_builder.rs` (extract the inner `build_expr` already used by `build_repl_input` and make it `pub`) |
| `pub fn expand<C, L>(sexp: Sexp, &SymbolTables<C, L>) -> Result<Sexp, ExpansionError>` | §5 above |
| `pub type SymbolTables<C, L> = DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>` | Facade §"Free functions" — type alias generic over `<C: CodeStore, L: LinkerStore>` per Decision 32 |
| `#[non_exhaustive] pub enum ExpansionError { Gap, Malformed, MacroAborted }` | §5.1 above (already partly in `public-api.txt` at lines 19–27; finalises shape) |
| `pub use cranelisp_types::ResolutionGap` (narrow ergonomic re-export) | Facade §"Types originated here" — re-export from `lib.rs` |

### 6.2 Entries to remove (or demote to `pub(crate)`)

| Existing public item | Disposition |
|---|---|
| `pub fn build_program(sexps: &[Sexp]) -> Result<Program, CranelispError>` | DELETE. Replaced by `int`-side classifier driver that calls `build_form` per residual-form. Existing callers in `src/` migrate to the new per-form path. |
| `pub fn build_repl_input(sexp: &Sexp) -> Result<TopLevel, CranelispError>` | DELETE. The REPL classifier moves to `int`; it calls `build_form` (top-level forms) or `build_expr` (bare expressions) based on form-head dispatch. |
| `pub fn build_repl_input_from_sexps(sexps: &[Sexp]) -> Result<TopLevel, CranelispError>` | DELETE. The multi-sexp annotation collapse (`:Type expr` → `Expr::Annotate`) moves into `build_expr`'s caller or into a small `int`-side helper; the frontend no longer publishes whole-input shape. |
| `pub fn parse_import_sexp` / `parse_export_sexp` / `parse_mod_sexp` / `parse_platform_sexp` | DEMOTE to `pub(crate)`. Their only legitimate callers are `extract_module_declarations` (internal) and (potentially) REPL slash commands like `/import` which should route through `extract_module_declarations` with a single-form input. Facade row 16. |
| `pub fn parse_macro_params` (current public; line 125) | DEMOTE to `pub(crate)`. Only `parse_defmacro` calls it inside the frontend; nothing in `src/` should call it directly. |

### 6.3 Entries unchanged

`parse`, `parse_preserving_comments`, `next_synthetic_span`, `parse_defmacro`, `synthesize_macro_clause_defn`, `is_defmacro`, `is_begin`, `flatten_begin`, `expand_quasiquotes`, `ExtractedDeclarations` (note: facade calls this `StructuralDecls`; rename is row 4 of `implementation-slice-s66.md` and is a SEPARATE concern from this wave's `build_form` shape pivot — `StructuralDecls` rename is out of scope for Wave 3a-β and stays as a follow-up).

### 6.4 What does not need a FIXME against `/arch`

- **No new types in `cranelisp-types`.** `ParsedEntry`, `DefmacroInfo`, `MacroClause`, `ConstructorDef`, `FieldDef`, `DefnVariant`, `TraitDecl`, `TraitImpl`, `ResolutionGap`, `FQSymbol`, `ErrorLocation`, `CodeStore`, `LinkerStore`, `SymbolTable`, `ModuleEntry`, `Sexp`, `Expr`, `Span` are all already present per `cranelisp-types/src/{parsed,ast,module,error,…}.rs`. The facade is internally coherent; the implementation gap is purely producer-side.
- **No public-surface-contract changes.** The lib.rs //! preamble (post-S70 B3-C facade retirement) already specifies `build_form -> Vec<ParsedEntry>`, `build_expr -> Expr`, `expand`/`ExpansionError`/`SymbolTables` exactly as needed. No FIXME against `/arch` for contract-edit.

---

## 7. Open questions / unresolved escalations

None that block `/dev`. Two minor points that may surface during implementation:

1. **Should `build_form` accept a `Sexp::Comment` at the top level and silently skip?** The current `build_program` filters comments at line 100 of `ast_builder.rs`. For per-form `build_form`, the caller (the orchestrator) is responsible for skipping `Sexp::Comment` forms before calling `build_form`. This pushes the comment-skip up one level — a small simplification because the orchestrator already iterates the residual-form vector from `extract_module_declarations`. `/dev` confirms: the comment skip moves to the orchestrator side; `build_form` errors on `Sexp::Comment` as "expected top-level form".

2. **`build_expr` extraction granularity.** The existing internal `build_expr` already returns `Expr`; promoting it to public requires no signature change. The only consideration is whether annotation collapse (`:Type expr`) handling stays in `build_expr` or moves to its caller. Per §6.2, the multi-sexp annotation collapse logic (in `build_repl_input_from_sexps`) is sufficiently REPL-specific that it lives `int`-side; `build_expr` operates on a single fully-annotated `Sexp`. This decision is recorded here for `/dev` and the matching `int` slice to honour.

Neither point requires `/arch` escalation; both are clarifications of producer-side behaviour `/dev` carries forward into the implementation.

---

## 8. Quality attributes touched by this wave

Per the master design §7 attribute table:

| Attribute | Touched? | Note |
|---|---|---|
| Simplicity | Yes | Collapses three publishing entries (`build_program`, `build_repl_input`, `build_repl_input_from_sexps`) into one per-form publisher (`build_form`) plus one expression publisher (`build_expr`). The classifier policy difference between REPL and batch (REPL accepts bare expressions; batch does not) moves up to `int` — a single classifier at the rim per target-state §3.2 item 5. |
| Maintainability | Yes | `build_form` is a single dispatcher with `pub(crate)` per-shape helpers; new top-level forms add one match arm + one helper. The existing duplication between `build_top_level` (used by `build_program`) and the REPL classifier inside `build_repl_input` (HIGH-2 in the audit) is eliminated. |
| Observability | No-change | Same error-value model; `ExpansionError::Malformed` for depth-limit + `MacroAborted` for runtime macro failure both carry `span` for span-anchored diagnostics. |
| Concurrency-safety | No-change | `expand` becomes a `Send + Sync` free function; symbol-tables read access is per-Decision-38. `build_form` is pure on owned input; no state. |
| Performance | No-change | The classifier collapse removes one level of indirection (the REPL was calling `build_repl_input` which called `build_top_level` which called `build_defn`); the new shape calls `build_form` which dispatches directly to `parse_defn`. Marginal improvement, not a perf goal. |
| Testability | Yes | `build_form` is independently unit-testable per shape (defn → 1 entry; deftype → N+1 entries; defmacro → 1 entry with N clauses); `expand`'s gap-return contract is independently testable with a stub `SymbolTables` instance, which the current `src/expander.rs` placement blocks (master §7.6). |

---

## 9. Implementability check

This design is implementable by `/dev` in a single D/D/R cycle:

- **Source touched.** `crates/cranelisp-frontend/src/{lib.rs, ast_builder.rs, expand.rs (new), defmacro.rs}` — bounded to one crate. No edits in `cranelisp-types` (the types already exist). No edits in `src/expander.rs` deletion (that's `int`'s same-wave parallel work).
- **Test cover.** Frontend unit tests on `build_form` per shape (defn, deftype with N constructors, deftrait, impl, defmacro with N clauses); unit tests on `expand` with a stub `SymbolTables`. Integration tests in `tests/process_form_dispatch.rs` are already authored (failing-not-ignored) and become the acceptance gate when the matching typecheck + int waves also land.
- **No spec change.** Spec §5.13.2 already extends to non-macro defns per FIXME 0167 resolution context; spec §8.12.1 already covers structural-decl ordering.
- **No `arch` escalation.** All necessary types exist; all necessary facade text is already authored.
- **No `qa` escalation.** The Wave 3a-β acceptance tests already exist in `tests/process_form_dispatch.rs`.

The wave's risk concentration is `expand` migration (§5) — ~520 LOC source port plus the `MacroResolver`-to-direct-`SymbolTables`-lookup rewrite. The `build_form` shape pivot (§2) is mechanical extraction from existing `build_top_level` + repackaging into `Vec<ParsedEntry>`.

---

## 10. Cross-references

- `crates/cranelisp-frontend/src/lib.rs` //! preamble — public-API contract (canonical home post-S70 Phase B group B3-C facade retirement)
- `crates/cranelisp-types/src/parsed.rs` rustdoc (`ParsedEntry`), `crates/cranelisp-types/src/view.rs` rustdoc (`View`) — boundary types
- `design/arch/facades/int.md` §"`process_cluster` — the cluster-atomic orchestration loop" — orchestrator contract (consumer-side)
- `design/arch/facades/typecheck.md` §"`check_form_signatures` + `check_form_body`" — consumer signatures
- `design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md` — cluster-atomic shape
- `design/arch/decisions/0045-traitimpl-storage-in-trait-defining-module.md` — Pattern B impl storage (Wave 3a-α)
- `design/arch/decisions/0046-wave3a-locality-refactor-precedes-triad.md` — Wave 3a α/β sequencing
- `design/arch/fixmes/0098-dev-frontend-typecheck-int-resolutiongap-checkerror-expansionerror-migration.md` — Phase 2 (this wave)
- `design/frontend/frontend.md` — master design (§§ 4–5 elaborated here)
- `design/frontend/implementation-slice-s66.md` — slice (rows 5, 6 SUPERSEDED by this doc)
- `crates/cranelisp-types/src/parsed.rs` — `ParsedEntry`, `DefmacroInfo`, `MacroClause` (authored, ready to consume)
- `crates/cranelisp-frontend/src/{lib.rs, ast_builder.rs}` — source-side implementation target
- `tests/process_form_dispatch.rs` — Wave 3a-β acceptance gate
