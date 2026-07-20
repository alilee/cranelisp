# Frontend — Master Design

> Per-crate master design document for `crates/cranelisp-frontend/`. Owned by `/design`.
>
> **Contract sources** (canonical, normative):
> - `design/arch/bounded-contexts.md` §1 — Frontend bounded context (including BC invariants 1–8 and the FIXME 0175 marshal-deps note).
> - `crates/cranelisp-frontend/src/lib.rs` //! preamble — as-designed public surface (the canonical home post-S70 Phase B group B3-C facade retirement; the per-crate `facades/frontend.md` file is retired).
> - Per-item rustdoc on each public item — per-item contract; browse with `cargo doc -p cranelisp-frontend --no-deps`.
> - `crates/cranelisp-frontend/public-api.txt` — authoritative as-built enumeration; gated at PR time.
>
> This document describes HOW the crate fulfills the contract. It does not restate the public-surface signatures (the source rustdoc is the single source of truth for those) and does not redefine the bounded context (BC §1 is the single source). Where the design intent differs from current source, the gap is named and tracked.

---

## 1. Bounded context recap

Per BC §1, `cranelisp-frontend` is responsible for: source bytes → S-expression trees → expanded S-expression trees → AST values. It is purely structural. Type inference, code generation, scheduling, and module-loading orchestration belong elsewhere; the frontend's contribution is a well-formed tree shape that every downstream stage can consume uniformly regardless of input origin (file, REPL, or another macro).

The BC names five in-scope responsibilities — lex/parse, macro expansion, AST construction, module-identity normalisation (`super` resolution + structural-decl extraction), and synthetic-span allocation. The frontend is the **only** crate that touches raw source bytes; this is the narrowest responsibility surface in the workspace and the strongest dependency-flow guarantee (Principle 3 — dependency flows toward stability).

The BC's "what crosses the boundary" is uniformly value-passing — no windows. Inputs are owned `&str` (or owned `String` for source-text retention by the integration layer); outputs are owned AST values. The single `&` parameter on the public surface is the symbol-tables map passed to `expand` (read-only multi-shard access). No mutable state crosses out.

---

## 2. Public surface — where it lives

The crate-root rustdoc `crates/cranelisp-frontend/src/lib.rs` //! preamble is the canonical and normative spec for the public surface (the per-crate `facades/frontend.md` document was retired in S70 Phase B group B3-C; its content folded into the source rustdoc + BC §1). The summary below names which public-surface item lives where in the source layout, and where the as-built differs from the as-designed.

| Facade item | As-designed home | As-built home | Status |
|---|---|---|---|
| `parse(source) -> Result<Vec<Sexp>, _>` | `lib.rs` | `lib.rs` (delegates to `reader::parse`) | conformant |
| `parse_preserving_comments(source) -> Result<Vec<Sexp>, _>` | `lib.rs` | `lib.rs` (delegates to `reader::parse_preserving_comments`) | conformant |
| `extract_module_declarations(forms) -> Result<(StructuralDecls, Vec<Sexp>), _>` | `module_extract.rs` re-exported via `lib.rs` | `module_extract.rs` (returns `ExtractedDeclarations`, not `StructuralDecls`; signature requires extra `path` parameter) | drift — see FIXME 0098 (Phase 2 — frontend signature alignment) |
| `build_ast(defn_sexp) -> Result<Defn, _>` and `build_expr(sexp) -> Result<Expr, _>` (per-form, no AST union) | `ast_builder.rs` | `ast_builder.rs` exposes `build_program` / `build_repl_input_from_sexps` / `build_repl_input` (whole-input shape; not per-form `Defn`/`Expr` split) | drift — facade per-form split is target-state |
| `parse_type_expr(source) -> Result<TypeExpr, _>` | `ast_builder.rs` re-exported via `lib.rs` | NOT YET — new named API (FIXME 0230); the production exists privately as `build_type_expr` | S76 target — see `s76-syntactic-only.md` §3 |
| ~~`expand(sexp, &symbol_tables) -> Result<Sexp, ExpansionError>`~~ | ~~frontend~~ | **RETIRED (S76 W-Macro).** Macro recognition → typecheck (via `cranelisp_types::resolve_macro_head`); execution → int (via `cranelisp_types::MacroExpander`); the `expand` skeleton + `ExpansionError` are **deleted** from the frontend boundary | retired — see `s76-syntactic-only.md` §1 + `design/arch/macro-expansion-ownership.md` |
| `parse_import_sexp` / `parse_export_sexp` / `parse_mod_sexp` / `parse_platform_sexp` | (facade withdrawn) | `pub(crate)` `#[allow(dead_code)]`, **zero callers** (`module_extract.rs:454-522`) | **dead retained sub-parsers** — the per-form classification path uses `extract_module_declarations` directly, not these wrappers. Delete candidates (audit R6 hygiene batch, `/dev`); the facade-re-export framing was aspirational and never wired |
| `next_synthetic_span() -> Span` | `quasiquote.rs` (atomic counter) | `quasiquote.rs` (atomic `AtomicU32`, base 1_000_000, monotonic) | conformant |
| `parse_defmacro(sexp) -> Result<DefmacroInfo, _>` and `synthesize_macro_clause_defn(info, idx) -> Defn` | `defmacro.rs` | `defmacro.rs` | conformant |
| `is_defmacro` / `is_begin` / `flatten_begin` / `expand_quasiquotes` | `defmacro.rs` + `quasiquote.rs` | same | conformant |

**Real contract work tracked under FIXME 0098** (do not paper over). FIXME 0098 (`*-resolutiongap-checkerror-expansionerror-migration`) is the multi-crate migration covering both prior frontend issues:

- Phase 1 (types) — land `ResolutionGap`, `CheckError` enums in `cranelisp-types`. Prerequisite for the frontend-side migration.
- Phase 2 (frontend) — **REVISED by S76 W-Macro.** The original Phase 2 "migrate `expand` into frontend" is **withdrawn**: `expand` does NOT migrate into frontend — it is **deleted** (recognition → typecheck, execution → int; see `s76-syntactic-only.md` §1 + `design/arch/macro-expansion-ownership.md`). What survives of Phase 2 is the syntactic-signature alignment only: `extract_module_declarations` / `parse_import_sexp` thread `containing_module`/`path` for `super` resolution (BC §1 invariant 3). Assess any residual against W-Absorb at landing.

> **S76 W-Macro supersedes the macro-migration framing throughout this doc.** Macro expansion is no longer a frontend responsibility. Frontend is purely syntactic: parse, quasiquote desugar, `build_form`/`build_expr`. See `s76-syntactic-only.md` (the S76 target) and §5 below. The `MacroExpander`-trait / `MacroResolver` / `expand`-as-free-function narrative in earlier sections is obsolete; recognition uses the `cranelisp_types::resolve_macro_head` primitive (typecheck + int callers), execution uses the `cranelisp_types::MacroExpander` callback (int impl).

The bounded-context invariants enumerated in the facade (no type inference, no codegen, `super` resolved at frontend, synthetic spans unique, `expand` re-entrant + side-effect-free for dependency resolution, form-by-form not pre-pass) are the contract this design must keep current with.

---

## 3. How the crate is structured to fulfill the contract

### 3.1 File-level partition

The facade is small (≈15 free functions plus 3 DTOs); the source partitions cleanly along five files plus `lib.rs`. Current LOC and role:

| File | LOC | Responsibility | Audit-named tension |
|---|---|---|---|
| `lib.rs` | 392 (~340 rustdoc) | Public re-exports + thin `parse`/`build_program`/`build_repl_input` wrappers | None directly; carries the implicit contract that unexpanded macros reaching `build_ast` become generic applications and fail later |
| `reader.rs` | 1004 | Hand-written recursive descent: source bytes → `Vec<Sexp>` (with optional comment preservation) | Documentation drift — the stale `plan-frontend.md` names `peg`; reality is hand-written (audit HIGH-5/F3, `/dev` fixes the crate-local plan doc) |
| `ast_builder.rs` | 2216 | Sexp → AST: top-level dispatch, expression lowering, type-expression parsing, pattern lowering, trait/impl lowering, vec literal lowering | HIGH-1/F1: single accretion point (function-budget clean, but the one place new forms land); §3.2 split is the target |
| `module_extract.rs` | 585 | Walks top-level forms, peels `mod`/`mod-`/`import`/`export`/`platform` into `ExtractedDeclarations`, normalises `super` against the parsing module's path; `mod`/`platform` simple-symbol guards | Carries `path` for super-resolution (correct); the 4 `parse_*_sexp` wrappers are dead-retained (R6) |
| `defmacro.rs` | 704 | Parses `(defmacro name [params] body)` shapes into `DefmacroInfo` + `MacroClause` lists; synthesises one ordinary `Defn` per clause for the integration layer to compile | HIGH-4/F2: manual synthetic-Sexp construction parallel to `quasiquote.rs` (R4 shared `synth` kit) |
| `quasiquote.rs` | 445 | Sexp-level desugaring of `` ` ``/`~`/`~@` into calls into the synthetic `macros/` module's constructors; hosts the monotonic synthetic-span counter | HIGH-4 partner; constructor helpers duplicated with `defmacro.rs` |
| `preamble.rs` | 269 | Leading `;;` comment-block capture (spec §8.16); keeps its tests inline (the documented sibling-file asymmetry) | None; current (`module-preamble.md`) |

Total ≈ 5,615 prod LOC, 378 unit tests passing (counts verified S114 Phase 3).

### 3.2 Target-state restructure (the design intent)

The audit's target-state diagram (`audits/frontend-20260423-target-state.mmd`) committed five structural moves that this design adopts. Each discharges a specific audit finding:

1. **Thin `lib.rs` facade** — public-API surface stays minimal (per-form trio + structural sub-parsers + helpers + `next_synthetic_span`). No business logic in `lib.rs`. Status: largely held today; will need expansion when `expand` migrates in (FIXME 0098 Phase 2).
2. **Reader unchanged in role**, documented as hand-written. Status: the current `reader.md` correctly says hand-written; the cross-cutting `plan-frontend.md` says `peg` and is stale (audit HIGH-5).
3. **Module extract unchanged** — still rewrites `super` at the boundary. Status: source-level correct; facade-text gap on signature only (FIXME 0098 Phase 2).
4. **Macro pipeline facade** — `quasiquote.rs` + `defmacro.rs` share a canonical synthetic-Sexp toolkit (`SexpKit` in the diagram). Eliminates HIGH-4. Status: not yet implemented; `/dev`-narrow work for a future wave.
5. **Shared top-level classifier** — one classifier consumed by both batch and REPL entry, with thin batch/REPL policy wrappers (REPL accepts bare expressions; batch rejects them). Eliminates HIGH-2. Status: **the single `build_form`/`build_forms` path landed** (S87 confirmed); the *residual* is the smaller F7/audit-R3 skew — "what is a top-level form" is expressed in three prod sites plus a verbatim test mirror that can drift. The R3 fix (one `classify_head(head) -> HeadKind` consumed by all three sites + the test adapter calling production) is a `/dev`(frontend) task (FIXME 0678, third-carry accepted S114).
6. **`ast_builder` split by subsystem** — `ast/top_level.rs`, `ast/expr.rs`, `ast/types.rs`, `ast/patterns.rs`, `ast/common.rs`. Eliminates HIGH-1. Status: not yet implemented; the current `ast_builder.rs` is a single ~2,216-LOC file (function-budget clean, no god function — the tension is accretion locality, not algorithmic complexity). The split happens at `/dev`-narrow time; this design commits to it.

Per Principle 6 (complexity has a budget) and Principle 2 (narrow interfaces), the split is *not* premature: it removes existing duplication and existing single-file policy concentration, not future complexity.

### 3.3 The implicit pipeline contracts (audit MEDIUM-3)

Three contracts cross file boundaries inside the crate and currently have no crate-local home:

- **Macro expansion must precede AST building.** Unexpanded macro calls reaching `build_ast` are silently treated as function calls and fail downstream at typecheck or codegen with confusing diagnostics.
- **`module_extract` rewrites `super` eagerly.** Downstream code (and downstream crates) must never assume the literal `"super"` survives past `extract_module_declarations`. (BC §1 invariant 3.)
- **Synthetic Sexp emitted by `defmacro.rs` must match `ast_builder.rs`'s expected shape exactly.** `defmacro.rs` knows `build_annotated_params()` expects `:` + type-expr + name as separate bracket items; this shape lock is implicit.

The audit's recommended-remediation item 3 calls for a crate-local `crates/cranelisp-frontend/CLAUDE.md` documenting these. That file is `/dev`-narrow ownership; this master design cannot author it directly. This design **commits to the target shape** (single classifier, split `ast_builder`, shared `SexpKit`) which makes each contract explicit by structure rather than by convention.

---

## 4. Form-classification + dispatch model

> **S66 Wave 3a update.** The per-form pair `build_ast` + `build_expr` named in earlier drafts of this section collapses into `build_form -> Vec<ParsedEntry>` + `build_expr -> Expr` per FIXME 0156. See `wave-3a-build-form.md` for the wave-specific shape; the model description below is the pre-pivot reading and remains accurate at the chain-composition level (parse → expand → per-form build → typecheck).
>
> **S76 W-Macro update.** The `expand` step in the chain below is NOT a frontend call post-S76 — macro expansion is int's Pass-1 loop (recognition via `cranelisp_types::resolve_macro_head`, execution via `cranelisp_types::MacroExpander`), running before the expanded forms reach frontend's `build_form`. Frontend's contribution to the chain is now: `parse` → quasiquote desugar → (int/typecheck expand) → `build_form`/`build_expr`. Read the `expand`-as-frontend-call references below as historical. See `s76-syntactic-only.md` §0.

The form-by-form scheduler (Decision 30) processes one source form at a time. The per-form chain — `expand` + `build_ast` + `check_form` — is composed by `int::process_form` (`facades/int.md` §"`process_form` — the gap-orchestration retry loop"); the frontend's role inside that chain has three calls:

1. **`parse` runs once per source unit** (file load or REPL submission). It returns `Vec<Sexp>` — flat, source-ordered, including any comments if the comment-preserving variant was called.
2. **`extract_module_declarations` runs once per source unit, immediately after `parse`.** It walks the form vector, peels off structural declarations (`mod`/`mod-`/`import`/`export`/`platform`), normalises `super` against the parsing module's path, and returns `(StructuralDecls, Vec<Sexp>)` where the second value is the residual form vector for per-form processing. Per Decision 33 + 38, the integration layer's `register_module` Phase 0 takes `StructuralDecls` and calls `SymbolTable::write_structural_decls` while still holding `&mut SymbolTable`.
3. **For each residual form**, `int::process_form` calls `expand(sexp, &symbol_tables)`. Expand walks the form recognising registered macros (FQ or imported short names) by consulting `symbol_tables`, and dispatching them via the JIT'd code address found through the GOT (per Decision 23). The frontend never names `Jit` or `Linker` — it sees only `code: Some(_)` on the per-clause `ModuleEntry::Def` entries (mangled `{macro}$clause-{N}` names; the parent `Def { kind: DefKind::Macro { clauses_meta }, .. }` carries dispatch metadata only, per S69 Submission 13 macro-unification). Once expansion succeeds, `build_ast` (or `build_expr` for REPL bare expressions) consumes the fully-expanded Sexp and returns a `Defn` (or `Expr`). `build_ast`/`build_expr` are pure structural transforms — no symbol-tables lookup, no gap returns.

Per Decision 30 (form-by-form scheduler; mutual-import deadlock), there is **no defmacro pre-pass**. Each form is processed in source order; macros become available to subsequent forms only after their own `defmacro` form has been processed. This is the operative model regardless of what `spec/09-macros.md §9.3.4` currently says about "module-wide availability" (FIXME `0005-spec-macro-availability-form-by-form` carries the spec revision).

The shared top-level classifier (target-state §3.2 item 5) is the entry point both batch and REPL drive, with thin policy wrappers — REPL accepts bare expressions, batch rejects them. Today the two paths (`build_program` for batch, `build_repl_input` / `build_repl_input_from_sexps` for REPL) duplicate the rejection-of-pre-AST-forms and the `parse_def_visibility` dispatch; the target collapses to one classifier with the policy difference at the rim.

### 4.1 Quasiquote/quote desugar fold (S111, FIXME 0613)

**Desugaring is folded into the AST chokepoints `build_forms`/`build_form` as
their first step**, so every form is desugared before dispatch and no caller can
forget it (the single-codepath lever; Principle 7, Principle 18). This closes
FIXME 0613 — quote/quasiquote templates in ordinary `defn` bodies and top-level
exprs (legal wherever an expression is legal, ruled (A) by the user S111) that
previously died at the `ast_builder.rs:1167` backstop because the only production
caller of `expand_quasiquotes` was `macro_clause.rs:67`.

The post-fold per-form chain: `parse` → (int Pass-1 macro expansion, quote-shielded)
→ `build_program_compat`/`flatten_begin` → **`build_forms`/`build_form` [desugar
fold]** → `build_form_inner`/`build_expr`. Key contracts, elaborated in
`design/frontend/quasiquote-fold.md`:

- **Chokepoint set** = `build_forms` (universal, via `build_program_compat`) +
  `build_form` (save.rs re-parse). `build_expr` has no production direct caller,
  is the internal recursion primitive, does NOT fold, and keeps the backstop.
- **Idempotence** — `expand_quasiquotes` is a fixpoint (no quote-family head
  survives one pass, span/gensym-stable), so the pre-existing `macro_clause.rs:67`
  call becomes redundant-but-harmless and is **retained, not removed**.
- **Backstop invariant** — the `ast_builder.rs:1167+` rejection stays: a surviving
  `quote`/`quasiquote` head is now always a bug (a chokepoint bypassed the fold);
  a surviving `unquote`/`unquote-splicing` head may also be a genuine
  outside-a-template user error.
- **Currency fix** — the `lib.rs:48` claim ("Quasiquote desugaring runs before
  `build_form`") is currently FALSE and becomes TRUE (`/dev` sharpens the rustdoc).
- **Named int seam** — the fold runs AFTER macro expansion, so macros receive raw
  `(quote …)`/`(quasiquote …)` argument sexps (conservative). The complementary
  obligation that int's `src/expander.rs::expand_scoped` not rewrite quoted-literal
  interiors is int's **quote shield** (separate `/design`(int) dispatch), landing
  ≤ the frontend fold. Frontend states its side; the shield is out of this surface.

The implicit pipeline contract — unexpanded macros reaching `build_ast` become silent generic applications — is preserved (the spec needs it for forward-compatibility with new macros that expand to function-shaped applications) but is documented in the target-state `crates/cranelisp-frontend/CLAUDE.md` (`/dev`-narrow follow-up).

### 4.2 Qualified binder-head rejection (S113, SPRINT §Scope-C)

**Every declaration head is a binder, not a reference** (spec §5, user ruling
2026-07-18, generalized to all binder heads S112) — it binds a NEW name into the
CURRENT module and MUST be bare; a qualified head (`(defn fmt/foo …)`,
`(deftype fmt/Point …)`, `(deftrait (fmt/Foo f) …)`, `(defmacro fmt/m …)`) is a
compile-time error. Fix shape (`/arch` Q3): ONE shared
`reject_qualified_binder_head` primitive beside `reject_reserved_binder_name`,
applied at every head site — `get_defn_name` (defn/defn- **and** impl-body method
defns), `build_type_head`, `build_trait_head`, `parse_defmacro` name, and
`build_method_sig` (deftrait method-signature name — beyond arch Q3's list, per
BD-M1 + §5.3.3, spec-enumeration gap routed to /spec) — never per-form copies
(Principle 7). `def`/`const` are stdlib macros (no native `def`);
their heads flow through the SAME seam **post-expansion** (§5 macro-surface rule).
Full design — the helper, the exhaustive head-site enumeration, the con_var
sibling cell (BD-M4), the spec-diff, and the **load-bearing span-provenance
finding** (int's macro-expansion pipeline discards source provenance, so the
macro-route span MUST needs a paired int-side re-anchoring seam) — in
`design/frontend/binder-head-reject.md`. The **0589** sibling (qualified-lowercase
annotation `:user/int` mints a `TypeVar` carrying `/`) is folded in as a distinct
**annotation-path** seam (`parse_annotation_name` routing, §5 of that doc), NOT
the binder-head seam.

### 4.3 Operand-position, annotation-lexing, and value-level binder enforcement (S114, SPRINT §Scope-D)

The frontend-s113 audit (§2.2/§2.7) named two enforcement-matrix holes that are
NOT binder heads, and S113 deferred the value-level binder reject. S114 Track D
closes them, anchoring the two **standing** matrices `/qa` maintains
(`s114-test-plan.md` §5):

- **BD-A — operand-position ascription/trailing (M1).** `:Type body` ascription
  (spec §2.3.8) and trailing-form rejection are enforced at nine positions and
  wrong at four (`build_let` body, `build_impl_method` body, `build_method_sig`
  default body, `build_trace` operand). Fix: ONE shared `build_body_to_end` seam
  (`build_one_expr_at` + consumed-to-end), so every single-body position routes
  identically (Principle 7). Includes the deftype-ctor trailing-form completion
  (the pre-existing RED). Full design: `enforcement-matrices.md` §1–§2.
- **RA — annotation/reference qualified-name lexing (0682 ruling).** The
  dangling-qualifier reject (`:foo/`, `foo/`, `/bar`) lives at the **reader**
  (un-swallow the two `read_qualified_tail` sites via ONE fallible
  `consume_dotted_module_path`; a `/bar` empty-module guard at `read_operator`);
  bare `/` division stays legal (RA-N4, Principle 16). The bound-form-must-be-a-
  type-expression reject (RA-N5) lives at `try_consume_annotation`. Full design:
  `enforcement-matrices.md` §3.
- **Value-level binder reject re-landing (0670-gated).** Once int's expansion
  pass skips binder slots (0670 path 1, Track C), the deferred
  `reject_qualified_binder_head` re-lands at `build_annotated_params` /
  `build_let_bindings` / `build_pattern`. Full design: `binder-head-reject.md`
  §3.4.

BD-A and RA are **independent** of the S114 carrier work and of 0670; only the
value-level re-landing is 0670-gated (F8 strict three-wave order).

---

## 5. Macro expansion moved OUT (S76 W-Macro)

> **SUPERSEDED 2026-06-03 by the LOCKED W-Macro decision.** The frontend no longer owns macro expansion. The subsections 5.1–5.4 below describe the pre-S76 frontend-owned expander (`expand` free function, `MacroResolver`, `Gap`/depth-limit, the `ExpansionError` surface) and are retained only as the historical reading. The current target is `design/frontend/s76-syntactic-only.md` §0–§2, grounded in `design/arch/macro-availability-model.md` §0 (the LOCKED decision) and `design/arch/macro-expansion-ownership.md`:
>
> - **Recognition** (walk + macro-vs-fn discrimination + clause match) → **typecheck**, via the `cranelisp_types::resolve_macro_head` primitive (module-local; no "probe every module" loop).
> - **Execution** (marshal + signal-protected JIT call) → **int**, behind the `cranelisp_types::MacroExpander` callback.
> - **Frontend** keeps only **quasiquote desugaring** (`expand_quasiquotes` / `expand_quote_template` / `next_synthetic_span`, in `quasiquote.rs`) — pure Sexp→Sexp, no execution. That is the entirety of frontend's remaining macro-adjacent role, and it is syntactic.
>
> The `expand` skeleton (`crates/cranelisp-frontend/src/expand.rs`) + `ExpansionError` + `EXPANSION_DEPTH_LIMIT` are **deleted** from the frontend boundary (Principle 7 — no duplicate walk). Deletion inventory + baseline/rustdoc impact: `s76-syntactic-only.md` §1, §2, §4.

### 5.1 Internal arrangement (historical — pre-S76)

- **`quasiquote.rs`** desugars `` ` `` / `~` / `~@` into calls into the `macros` synthetic module's constructor functions (`macros/SexpSym`, `macros/SexpInt`, `macros/SCons`, etc.). It runs unconditionally on every form, before macro-call dispatch. It also handles `(quote ...)` (pure structural quotation, no unquote semantics).
- **`defmacro.rs`** parses `(defmacro name [params] body)` shapes into `DefmacroInfo` (one entry per clause). Each clause is synthesised as an ordinary `Defn` via `synthesize_macro_clause_defn`. The integration layer compiles each clause defn through the normal pipeline and registers them as separate `ModuleEntry::Def` entries under mangled `{macro}$clause-{N}` names (each with `kind: DefKind::UserFn`, `got_slot: Some(_)`, `ast: Some(_)`, `code: Some(_)`). A parent entry — `ModuleEntry::Def { kind: DefKind::Macro { clauses_meta: Vec<MacroClauseInfo> }, .. }` — is registered under the macro's bare name carrying dispatch metadata only (no callable runtime address, `got_slot: None`). Per S69 Submission 13 macro-unification, the prior `ModuleEntry::Macro` variant retired in favour of this Def-based shape (per Decision 21 cross-reference).
- **`expand` (in target state, frontend; in current state, `src/expander.rs`)** runs the loop: recognise macro calls (resolve head symbol → `ModuleEntry::Def { kind: DefKind::Macro { clauses_meta }, .. }` via `&symbol_tables`), walk `clauses_meta` to match the call sexp against each clause's shape, GOT-dispatch to the matched clause's mangled-variant `Def` via the JIT-loaded function pointer on that variant's `code: Option<C>`, marshal the result Sexp tree back, and recurse (re-expansion of the macro's output). Bare-symbol zero-arg macros are recognised and expanded the same way. (Migration tracked under FIXME 0098 Phase 2 — the invocation-path migration is gated on FIXME 0175.)

### 5.2 Termination + recursion-depth

The current implementation uses `EXPANSION_DEPTH_LIMIT = 100` (`src/expander.rs`). The facade invariant says termination is the macro author's responsibility ("no recursion-depth limit imposed by the frontend"). These differ: the depth limit is a defensive guard against infinite expansion, not a contract guarantee. The design intent reconciles them by treating the depth limit as a **diagnostic** — when reached, surface a `MacroError`-like variant; do not silently truncate. The contract remains that termination is the macro author's responsibility; the limit only fires on demonstrably-runaway expansion.

When `expand` migrates into `cranelisp-frontend` (FIXME 0098 Phase 2), the depth limit comes with it. No spec change required.

### 5.3 Dependency-not-yet-ready signals

Per Decision 30 + facade invariant 6, `expand` surfaces dependencies as **values**. It NEVER calls the scheduler, NEVER blocks, NEVER registers modules — the frontend has no `Sess` dependency by Principle 3.

When `expand` encounters an FQ (or resolvable-to-FQ) symbol whose target's `ModuleEntry` isn't yet ready in `symbol_tables`, it returns:

```
Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))
```

This **single gap variant is uniform** across all "FQ ref expansion can't fully resolve" cases — regardless of whether the cause is "module unregistered", "typecheck incomplete", or "code missing". Expand stays uniform; the **orchestrator owns the macro-vs-fn discrimination** because that classification depends on scheduler-side knowledge (what the entry contains *after* the typecheck wait completes).

The orchestrator's response — `ensure_registered`, then `wait_for_typecheck_symbol`, then peek at entry, conditionally `priority_boost_jit` + `wait_for_inmem` — is documented in `facades/int.md` §"`process_form` — the gap-orchestration retry loop". Frontend does not encode any of that policy.

`build_ast` / `build_expr` do not produce gaps — they are pure transforms on a fully-expanded Sexp.

The other `ExpansionError` variants (`Malformed`, `MacroAborted`, …) are genuine failures, not gap signals. `MacroAborted { fq, message, span }` carries enough information for the integration-layer formatter to produce a useful diagnostic.

### 5.4 Why `MacroResolver` is not the public boundary

The integration layer today defines a `MacroResolver` trait used by `expand_sexp_recursive` to abstract macro lookup. Worker.rs has a `SymbolTableMacroResolver` impl that compiles macro clauses on demand; `session_v4.rs` has a `ReadOnlyMacroResolver` impl for batch reads. Both depend on integration-layer types.

The trait is fine as an integration-layer convenience while it remains there; it is **not the public boundary**. When `expand` migrates to the frontend (FIXME 0098 Phase 2), the trait is replaced by direct symbol-tables lookup — Decision 8's retraction. The on-demand-compile responsibility moves to the orchestrator: the `wait_for_inmem` call in `handle_gap` is the trigger, not a callback into the expander. This narrows the frontend's input contract from "&mut dyn MacroResolver" (which can mutate) to "&symbol_tables" (read-only) — Principle 1 (decoupling over convenience) and Principle 5 (testability is structural).

---

## 6. Module-identity normalisation

The frontend is the boundary at which `super` is resolved. `module_extract.rs::parse_import` requires `containing_module: &ModuleFullPath` to rewrite `super` → parent path per spec §8.3.7. Past the frontend, no `ImportSpec.module_path` contains the literal `"super"` (BC §1 invariant 3).

Three structural-declaration families are extracted at parse time, before macro expansion:

- `(mod name)` / `(mod name forms...)` / `(mod- name)` — submodule declarations + optional inline body
- `(import [module-spec names-list ...])` — pairs of (module-spec, names-list); module-spec may be a symbol, `super`, or `(module alias)`; `super` is rewritten in this pass
- `(export [name ...])` — re-export list
- `(platform [...])` — platform DLL binding

The order matters: structural declarations are extracted **before** macro expansion (per spec §8.12.1) so that the integration layer can populate the symbol table's structural fields before any form-processing begins. A macro cannot, therefore, expand into a `(mod ...)` or `(import ...)` form — these are recognized syntactically.

This is a frontend design choice, not a forced one. Allowing macros to produce structural decls would invert the order (you can't run macros before you know what's imported) and is explicitly out of scope.

---

## 7. Quality attributes

### 7.1 Simplicity (Principle 6 — complexity has a budget)

The crate is simple at file level: one entry point per concern, direct logic, few abstraction layers. The hand-written recursive descent reader is simpler than introducing a parser library for a grammar this small (the historical `peg` decision in `plan-frontend.md` is stale; the audit confirms reality matches "hand-written" and "doc says peg" is the documentation drift, not the reality drift).

**Audit findings driving this attribute (all unresolved as of this design pass):**

- **HIGH-1** (`ast_builder.rs` carrying too much policy) — the file's complexity is structural, not algorithmic. Splitting into `ast/{top_level,expr,types,patterns,common}.rs` is the §3.2 target. Complexity within each smaller file becomes locally bounded.
- **MEDIUM-4** (manual synthetic-Sexp builders in `quasiquote.rs` + `defmacro.rs`) — each manual construction is simple in isolation; the duplication across files is the cost. A shared `SexpKit` helper module collapses the duplication without adding indirection.

The trade-off: keeping all `ast_builder` policy in one file *was* simpler when the language was smaller. The audit's MEDIUM-1 finding ("`ast_builder.rs` mixes top-level forms, expr lowering, trait and impl lowering, types, patterns, special cases") signals the simplicity inversion has happened.

### 7.2 Maintainability

The 6-sprints-out-blast-radius test is the right lens. New language forms today land predominantly in `ast_builder.rs` (largest file, most likely to grow); a new macro feature lands in some combination of `defmacro.rs`, `quasiquote.rs`, and `expander.rs` (currently in `src/`).

**Audit findings driving this attribute:**

- **HIGH-1** (single-file policy concentration) — bounded blast radius requires per-subsystem files. New forms land in one of {top_level, expr, types, patterns} rather than always in the same monolith.
- **HIGH-2** (`build_repl_input` vs `build_top_level` duplication) — drift-prone. New forms accumulate to one path before the other; the audit-named risk is precisely this. Remediation: single classifier with thin REPL/batch wrappers (target-state §3.2 item 5).
- **HIGH-5** (documentation drift — `peg` named in plan but reader is hand-written; `ast_builder.rs` header still claims "Ring 0, non-Ring-0 rejected" while the file handles traits/impls/strings/vec literals/trace forms) — stale design docs create false mental models. This master doc + the §9 staleness register is the partial remediation; the full fix requires `/design` follow-up sprints to refresh subordinate docs.
- **MEDIUM-3** (hidden cross-file pipeline contracts) — must surface as crate-local `CLAUDE.md` content (audit item 3, owned by `/dev`-narrow). This master doc cannot edit `crates/cranelisp-frontend/CLAUDE.md`; instead, it commits to the target shape that makes each contract explicit.

FIXME 0098 (multi-crate `ResolutionGap`/`CheckError`/`ExpansionError`/`expand` migration) is also maintainability-relevant: a facade that drifts from source forces every reader to triangulate, and the facade-vs-source gap covered by Phase 2 (`expand` not yet in frontend) is a sustained tax until resolved.

### 7.3 Observability

The frontend produces error values; it never logs or `eprintln!`. Per Decision 39, every `CranelispError` carries an `ErrorLocation` with `span` always populated, plus `file`/`fq`/`line_col`/`context` populated as available. The parser populates `context` with surrounding lines so parse errors are self-contained even after the source string drops.

`ExpansionError::MacroAborted { fq, message, span }` carries enough for the integration-layer formatter to produce a useful diagnostic ("macro X failed during expansion of Y") with span-anchored context.

The crate has no internal tracing surface and does not need one. Debugging-time observability is the integration layer's `CRANELISP_CODEGEN_TRACE` story plus REPL slash commands (`/expand`, `/sexp`, `/source`). The frontend's contribution to those is being inspectable: every public function is callable in isolation and returns inspectable data, which is what `/expand` etc. depend on.

This sprint did not introduce any frontend-internal observability surface.

### 7.4 Concurrency-safety (Principle 1, Principle 4)

The frontend has no internal concurrency. All public functions are pure transforms on owned inputs (or `&` references). Shared state is read-only via the symbol-tables map passed into `expand`; per Decision 38, the per-module `SymbolTable` enforces its own per-entry locking via the inner DashMap.

The only shared mutable state owned by the frontend is the synthetic-span counter behind `next_synthetic_span()` — process-monotonic via `AtomicU32` (`quasiquote.rs::SYNTHETIC_SPAN_COUNTER`, base 1_000_000 to avoid collision with real source spans). Any thread allocating a synthetic span receives a fresh one. The "uniqueness across session" facade invariant is satisfied by the atomic backing.

Multiple workers may call `expand` concurrently against the same `&symbol_tables`. Per Decision 38's per-symbol mutability discipline, each `SymbolTable`'s internal DashMap permits shard-read access without whole-module locking; `expand` runs from any worker without further synchronisation. There is no callback into the scheduler — gap returns surface dependencies as values.

The migration in FIXME 0098 Phase 2 preserves these properties: `expand` becomes a `Send + Sync` free function; the symbol-tables type is generic in `<C: CodeStore, L: LinkerStore>` so frontend stays C/L-blind (per Decision 32's marker traits).

### 7.5 Performance

Frontend performance is dominated by the reader (lexing) and `ast_builder`'s tree walk. Both are linear in source size. No subordinate `performance.md` exists; this sprint did not touch performance, and the audit does not flag perf concerns.

Pathological cases identified:

- Deeply nested quasiquoted expansions can produce wide synthetic-Sexp trees. Current builders allocate per-node; no pooling. Acceptable for now — macro footprint is small.
- The form-by-form scheduler invokes `parse` once per source unit but `expand` + `build_ast` once per top-level form. Re-parsing on REPL eval is the dominant cost; that's the integration layer's territory (Principle 3 — frontend is upstream, owns lexing once).

Premature-abstraction checks: the `SexpKit` consolidation proposed by audit item 4 is **not** premature — it removes existing duplication, not future duplication. Per Principle 6, this is paying down debt, not budgeting for the future.

### 7.6 Testability (Principle 5 — testability is structural)

The frontend already meets the structural testability bar: it can be unit-tested without the typechecker, backend, or runtime. 234 tests pass against `parse` / structural-extraction / `build_program` / `build_repl_input` / `expand_quasiquotes` / `parse_defmacro` directly.

**Audit finding LOW-6** (test bulk inside production files makes file-scrolling expensive) — addressed by audit item 6: move large test blocks to `*_tests.rs` siblings while keeping `#[cfg(test)] mod tests` locality. This is `/dev`-narrow; the design endorses it.

`expand`'s gap-return contract is independently testable: stub `symbol_tables` to lack the FQ macro entry, assert `Err(ExpansionError::Gap(MacroInMem(fq)))`. This is structural testability of the dependency-surfacing mechanism without needing a running scheduler. Today this test cannot exist at the frontend boundary because `expand` is in `src/`; FIXME 0098 Phase 2 unblocks it.

---

## 8. Decision register (frontend-relevant)

Per `design/arch/CLAUDE.md`'s active-vs-legacy split: active Decisions carry forward-handoff or pre-implementation work; legacy Decisions are fully embodied in the architecture and preserved for narrative continuity. Below split accordingly.

### Active

| # | Decision | Frontend takeaway |
|---|---|---|
| 30 | Form-by-form scheduler; mutual-import deadlock | **S76 W-Macro:** frontend no longer has `expand`, so it no longer produces gaps. Macro recognition/execution + the gap-orchestration retry are typecheck's + int's (`CheckError::Gap`, int `process_cluster`). Frontend stays gap-free and block-free by being syntactic-only. The defmacro-before-use rule (no pre-pass) is now normative per `macro-availability-model.md` §0.2 |

### Legacy — embodied

| # | Decision | Frontend takeaway |
|---|---|---|
| 1 (legacy — embodied) | 7+1 crate DAG | Frontend is one crate; depends only on `cranelisp-types` |
| 2 (legacy — embodied) | `cranelisp-types` data-only | `Sexp`, `Expr`, `TopLevel`, `Defn`, `TypeExpr`, `ImportSpec`, `ExportSpec`, `ModDecl`, `PlatformSpec`, `MacroClauseInfo`, `MacroParam` (and target-state `ResolutionGap`, `StructuralDecls`) all live in types; frontend consumes them |
| 6 (legacy — embodied) | `Type::from_name` / `type_name` | Frontend uses `TypeName` (syntactic), never `Type`. Lift to `Type` happens in typecheck per the `TypeName → FQTypeName` boundary |
| 8 (legacy — embodied) | `MacroExpander` trait deleted (Ring-era dependency-inversion) | **S76 W-Macro:** the question is moot for frontend — frontend owns no expander at all post-S76. A *new* `cranelisp_types::MacroExpander` callback exists (int impls it; typecheck calls it), but it is NOT frontend's and is unrelated to the deleted Ring-era trait |
| 21 (legacy — embodied) | TC-sourced call graph on `ModuleEntry` | Frontend extracts `MacroClauseInfo` shapes; integration layer + typecheck populate `callees` on the per-clause `ModuleEntry::Def` entries (the `{macro}$clause-{N}` mangled-variant Defs). The parent `ModuleEntry::Def { kind: DefKind::Macro { clauses_meta }, .. }` is metadata-only (no `callees` payload, no GOT slot). Frontend does NOT compute callees |
| 23 (legacy — embodied) | Uniform codegen; mode is a Module property; two-GOT model | Macro invocation goes through the GOT slot; frontend sees only `code: Some(_)` on the entry, never names `Jit` |
| 32 (legacy — embodied) | `CodeStore` / `LinkerStore` marker traits | `expand`'s symbol-tables parameter is generic in `<C: CodeStore, L: LinkerStore>` so frontend stays C/L-blind |
| 33 (legacy — embodied) | Structural decls as fields on `SymbolTable` | `extract_module_declarations` returns the bundle that integration layer writes via `SymbolTable::write_structural_decls` at Phase 0 |
| 38 (legacy — embodied) | `SharedState`; per-symbol mutability discipline | `expand`'s `&symbol_tables` is the post-Phase-0 shared-read access shape — per-entry inner-DashMap locks, no whole-module write locks |
| 39 (legacy — embodied) | `ErrorLocation`; per-defn source on Introspection | Parse errors populate `ErrorLocation.context` directly; post-parse errors leave `context: None` and let the formatter resolve via introspection. `Span` always populated (synthetic spans use the monotonic allocator) |

---

## 9. Subordinate topic docs — staleness register

This master doc does NOT edit the subordinate docs. The register below records each one's current status against the post-FIXME-resolution target. Refreshing them is `/design`'s follow-up work.

| Topic | File | Status |
|---|---|---|
| Reader internals | `design/frontend/reader.md` | **Mostly current.** Correctly says "hand-written recursive descent". Cross-cutting `crates/cranelisp-frontend/plan-frontend.md` says `peg` and is the actual stale doc (audit HIGH-5) |
| AST builder | `design/frontend/ast-builder.md` | **Stale on ring-gating + S69 fused-tuple cascade** (the older body); **current for S91 Thread B/C** — carries the D-qual-impl-target fix (`build_impl_target` routes through `type_ref_from_name`; frontend-only) and the FIXME 0365 frontend half (dotted field-accessor `Type.member` is verbatim pass-through, no frontend change; resolution is typecheck's). Older body claims "Ring 0, non-Ring-0 rejected" while the file handles traits, impls, strings, vec literals, trace forms (HIGH-5); additionally pre-dates S69 Submissions 23/24/26/27 (fused `params: Vec<(Symbol, Option<TypeExpr>)>` on DefnVariant/Lambda; `TraitMethodSig.params: Vec<(Symbol, TypeExpr)>`; `TraitImpl.target: TypeExpr`). Pre-dates the §3.2 target split |
| Comment preservation | `design/frontend/comment-preservation.md` | **Current.** Describes `Sexp::Comment` variant and `parse_preserving_comments` entry point as implemented |
| Module preamble capture | `design/frontend/module-preamble.md` | **Current (authored S88 Step 3.2).** The leading comment-block preamble capture (`capture_module_preamble: &str -> Option<String>`, pure), the frontend→int wiring seam, and the regen byte-stable round-trip contract reconciled with FIXME 0423. Names the §8.16 comment-block model; one additive `public-api.txt` line; FIXME `target: /int` for wiring + regen |
| S76 syntactic-only target | `design/frontend/s76-syntactic-only.md` | **Current (authored S76 Phase 3).** The W-Macro deletion inventory (`expand`/`ExpansionError`/`EXPANSION_DEPTH_LIMIT` deleted), the quasiquote-only role confirmation, the FIXME 0230 `parse_type_expr` API shape, and the baseline/rustdoc impact. The operative frontend target for S76 |
| Macro plan | `design/frontend/macro-plan.md` | **Superseded by S76 W-Macro for the ownership framing** (was: Decision 8 retraction + S69 macro-unification cascade). Multi-clause shape + marshalling + span-rewriting still accurate; the `MacroExpander` trait dependency-inversion framing is retracted by Decision 8; the `MacroEnv` references throughout (per S69 Submission 13) are retired — clause bodies live in the symbol table under mangled names rather than in a separate dispatch map, and the parent metadata is `ModuleEntry::Def { kind: DefKind::Macro { clauses_meta }, .. }` (no separate `ModuleEntry::Macro` variant) |
| Modules | `design/frontend/modules.md` | **Partially stale.** Module-system concept accurate; specific function names + parallel-store framing predates Decisions 33 + 38. `super` rewrite at frontend boundary still correct |
| Frontend plan | `crates/cranelisp-frontend/plan-frontend.md` | **Stale (architectural).** Names `peg` 0.8 as the parser; reality is hand-written. This is the highest-impact doc-drift item per audit HIGH-5 |
| S66 Wave 3a-β (`build_form` + `expand`) | `design/frontend/wave-3a-build-form.md` | **Current.** Authored 2026-05-12 for FIXME 0156 + FIXME 0098 Phase 2 under Decision 44 (amended 0167, 0168) — `/dev` implementation target |
| Quasiquote/quote desugar fold | `design/frontend/quasiquote-fold.md` | **Current (authored S111 Phase 3).** The FIXME 0613 fold of `expand_quasiquotes` into `build_forms`/`build_form`: fold point + chokepoint set, idempotence/fixpoint contract, backstop invariant, family coverage, `lib.rs:48` currency fix, and the named int quote-shield seam. `/dev` Phase-5 target. Makes `s76-syntactic-only.md:74`'s aspirational "quasiquote desugaring runs before `build_form`" literally accurate |
| Qualified binder-head rejection (S113–S114) | `design/frontend/binder-head-reject.md` | **Current (authored S113 Phase 3; §3.3/§8 + §3.4 updated S114 Phase 3).** ONE shared `reject_qualified_binder_head` at the head sites (S1–S5) + con_var; §3.3 records the deftype-ctor/field/platform family LANDED (FIXME 0660 closed); §3.4 designs the value-level binder reject re-landing (0670-gated, F8 wave 2). Folds 0589 (annotation-path routing) + disposes 0590 (re-targeted typecheck). The span-provenance finding + int re-anchoring seam stand |
| Enforcement matrices (S114 Track D) | `design/frontend/enforcement-matrices.md` | **Current (authored S114 Phase 3).** The BD-A operand-position one-seam (`build_body_to_end`, M1 anchor), the deftype-ctor trailing completion, and the RA dangling-qualifier/bound-form-type reject placement (reader `consume_dotted_module_path` + `read_operator` `/bar` guard; `try_consume_annotation` RA-N5). The annotation/operand family sibling of `binder-head-reject.md`. `/dev`(frontend) + `/review` Track-D target |
| Trait/impl head parse (S112 b0) | `design/frontend/trait-impl-head-parse.md` | **Current (authored S112 Phase 3, leg b0).** The echo-the-head `impl` slot-1 change: `parse_impl` accepts bare `Display` (`head_con_var: None`) OR `(Functor f)` (`head_con_var: Some`), slot 2 rides the existing `build_impl_target`; NO kind classification / echo validation in the parser (typecheck's §7.3.5 Case-3 seam — Principle 24). Single-sources the head-shape grammar with `build_trait_head` (Principle 7); malformed-slot-1 diagnostics; additive-green at b0; pretty/​save form-agnostic round-trip (no change). `/dev`(frontend) + `/review` target. Consumer: `design/typecheck/hkt.md` §5.4 |

Refresh order, in priority of audit blast radius (post-S114 R5 prune):

1. `crates/cranelisp-frontend/plan-frontend.md` — fully-stale architectural decision (still names `peg`); refresh to "hand-written recursive descent" (crate-local file, `/dev`(frontend) — FIXME 0680 remaining half)
2. `ast-builder.md` — refresh against the §3.2 split shape (defer until §3.2 split lands)
3. `macro-plan.md` — retained-with-caveat: multi-clause shape + marshalling + span-rewriting still accurate; the `MacroExpander`-trait dependency-inversion framing is retracted (Decision 8 / S76 W-Macro). Refresh or fold into `macro-plan`'s live half when macro work next deploys
4. `modules.md` — refresh against Decisions 33 + 38
5. `reader.md` — minor refresh

**S114 R5 prune (executed):** `macro-resolver-trait.md` (superseded ~37
sprints), `implementation-slice-s66.md` (one-shot executed S66 slice — its
live `build_form` shape lives in `wave-3a-build-form.md`), and
`sprint-70-cascade-plan.md` (one-shot executed S70 cascade) DELETED to git
history. The remaining R5 half — the crate-local `plan-frontend.md` (item 1
above) and the `defmacro.rs` ↔ `lib.rs` narrowing-contract contradiction — is
`/dev`(frontend)'s (FIXME 0680, updated). The `/dev` narrowing-story ruling is
recorded at §9.1 below.

The audit's recommended-remediation item 5 ("refresh or replace stale design docs immediately") aligns with this register.

### 9.1 The defmacro-helper narrowing story — the ONE contract (R5, /dev half)

The audit (§2.5) named a shipped **contradiction**: `defmacro.rs:16-18/:210-212/:354`
promise the helper family "narrows back to `pub(crate)` at FIXME 0098 Phase 2
close", while `lib.rs:167-169` states "Post-S76 … there is no 'narrow back'
framing — these helpers stand on their int consumers alone." One is the
contract; both are shipped rustdoc.

**Ruling (this design picks the surviving story):** `lib.rs` is CORRECT — there
is **no "narrow back"**. FIXME 0098 Phase 2's "migrate `expand` into frontend"
was **withdrawn** by S76 W-Macro (`expand` is deleted, not migrated; §2 + §5),
so the event the `defmacro.rs` rustdoc conditions its narrowing on **never
happens**. The `parse_defmacro` / `synthesize_macro_clause_defn` /
`is_defmacro` helper family is a permanent part of the public boundary, consumed
by int's macro pipeline; it stands on those consumers, not on a future
re-narrowing. **The losing rustdoc is `defmacro.rs:16-18/:210-212/:354`** — the
"narrows back to `pub(crate)`" sentences. `/dev`(frontend) deletes them (FIXME
0680 remaining half); no `public-api.txt` change (the surface is already public).

---

## 10. Cross-references

- `crates/cranelisp-frontend/src/lib.rs` //! preamble + per-item rustdoc — public-API contract (canonical home post-S70 Phase B group B3-C facade retirement)
- `crates/cranelisp-frontend/public-api.txt` — authoritative as-built enumeration
- `design/arch/facades/int.md` §"`process_form` — the gap-orchestration retry loop" — orchestration partner contract
- `design/arch/bounded-contexts.md` §1 — bounded context statement
- `design/arch/principles.md` — principles cited above (1, 2, 3, 4, 5, 6)
- `design/arch/CLAUDE.md` — Decisions 1, 2, 6, 8, 21, 23, 30, 32, 33, 38, 39 (frontend-relevant; 30 active, others legacy)
- `design/arch/fixmes/0098-dev-frontend-typecheck-int-resolutiongap-checkerror-expansionerror-migration.md` — multi-crate migration covering `extract_module_declarations`/`parse_import_sexp` signatures (Phase 2) and `expand`/`ExpansionError`/`ResolutionGap` placement (Phase 1 types → Phase 2 frontend)
- `audits/frontend-20260423.md` — current-state ground truth (point-in-time; supersession-marked)
- `audits/frontend-20260423-current-state.mmd`, `audits/frontend-20260423-target-state.mmd` — current and target diagrams
- `design/frontend/{ast-builder,reader,comment-preservation,module-preamble,macro-plan,modules,quasiquote-fold,trait-impl-head-parse,binder-head-reject,enforcement-matrices}.md` — subordinate topic docs (staleness register §9)
- `crates/cranelisp-frontend/src/{lib,reader,ast_builder,module_extract,quasiquote,defmacro}.rs` — implementation
- `crates/cranelisp-frontend/plan-frontend.md` — pre-Ring-0 plan (architectural drift; staleness register item 1)
- `src/expander.rs` — current home of `expand_sexp_recursive`; migrates per FIXME 0098 Phase 2
