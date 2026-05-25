# cranelisp-types solidness sweep — Sprint 70 Phase 3

**Status**: authored, awaiting user disposition per finding.
**Filed**: 2026-05-25
**Filed by**: `/arch`

## Scope

A focused, four-lens sweep over `crates/cranelisp-types/` after Sprint 70 Phase 3
surfaced two un-cascaded items in `DefKind::Macro` (variant absent though
rustdoc-cited at 8 sites; then pre-D41 shadow fields `sexp` / `source` added &
withdrawn). The two-find depth opened the question of how many more such items
the types crate carries. This sweep checks four specific failure modes — it is
*not* a full re-audit of every public-API item (S69's
`types-audit-s69.md` exhaustively dispositioned the public surface 2026-05-19;
this sweep checks only items dispositioned *cleanly* in S69 against the
post-Phase-3 source state, and surfaces anything that fits one of the four
lenses).

**The four lenses**

1. **Un-cascaded S69 decisions** — rustdoc-cited types/variants/fields that
   don't exist in source; or Submission narratives ruling structural changes
   that never landed.
2. **Dead fields** — `Option<T>` / `Vec<T>` fields written `None`/`empty` at
   every construction site AND/OR never read at any consumer site (or whose
   readers are themselves dead).
3. **Struct-vs-rustdoc drift** — field rustdoc citing a sibling, decision, or
   invariant that no longer holds.
4. **D41-violation shapes** — storage of introspection-adjacent data
   (`source`/`sexp`/`expanded`/`clif_ir`/`disasm`/`code_size` / `*_ir`
   / `*_meta`) on a types-layer struct that competes with the
   canonical Introspection record at `src/session_v4.rs:566`.

**Out of scope.** The full S69 audit register; consumer-crate cascade work
already FIXME-tracked (e.g., `param_annotations` retirement on the typecheck
side; `ModuleEntry::Macro` consumer arms in `int`); items the S69 audit
dispositioned + closed cleanly; serializing `Introspection` (user-excluded —
lazy file re-read is the future path at FIXME 0220); re-introducing shadow
fields on any types-layer struct (user-excluded).

## Method

Per `memory/feedback_audit_per_item_analysis.md` — each finding carries five
blocks: facade-expects (canonical configuration), source-does, design-intent
(grounded in named Decision / Principle / FIXME — not manufactured), difference,
proposed disposition. Default disposition is **source moves** per
`memory/feedback_hold_to_facade_default.md`; `cranelisp-types` lacks a separate
facade since S69 Sub 42 retired `facades/types.md`, so the "facade" here is the
crate-root `//!` rustdoc in `lib.rs` + the per-item `///` rustdoc + the
governing `bounded-contexts.md` §7 + Decisions register. Configuration grounds
the sweep (`memory/feedback_configuration_grounds_facade.md`).

The sweep covered every `*.rs` file in `crates/cranelisp-types/src/`
(ast / check / error / got / heap / lib / marshal / module / newtype /
parsed / pipeline / scheduling / sexp / span / types / view) — read in full,
cross-checked against the canonical configuration named above.

## Findings

### Finding 1 — `ModuleEntry::TypeDef.sexp: Option<Sexp>` is dead and D41-violating

- **Lens**: 2 (dead field) + 4 (D41 violation).
- **Site**: `crates/cranelisp-types/src/module.rs:653-658` — the `TypeDef`
  variant's `sexp: Option<Sexp>` field declaration; reader at
  `src/save.rs:241-243` pattern-matches `sexp: Some(sexp)` to drive
  deftype regeneration.
- **facade-expects** — per the crate-root `//!` (`lib.rs:33`) the variant
  is part of THE per-module store; per Decision 41 (canonical operative)
  the introspection record at `src/session_v4.rs:566` is the canonical
  store for `source` / `sexp` / `expanded` / `clif_ir` / `disasm` /
  `code_size` for ALL Def variants; per the `DefKind::Macro` rustdoc
  (`module.rs:957-1006`, freshly amended in Phase 3 row #6) introspection
  storage is symmetric across all DefKinds; per
  `design/arch/sequences/exec-flow-compilation.mmd` lines 111 & 211–221
  the introspection DashMap is populated by frontend + backend keyed on
  `FQSymbol`, NOT carried on the symbol-table variant.
- **source-does** — `TypeDef` carries `sexp: Option<Sexp>` directly on
  the variant. Every construction site writes `None`:
  `crates/cranelisp-typecheck/src/builtins.rs:347 / :438 / :582 / :648`
  (primitives bootstrap — registering Vec / IO / Option etc.) and
  `crates/cranelisp-typecheck/src/adt.rs:67 / :139 / :171` (user deftype
  registration). Reader `src/save.rs:238-253` (`generate_types`) walks
  symbols, pattern-matches `TypeDef { sexp: Some(sexp), .. }`, and emits
  the deftype sexp — the `Some` arm IS NEVER REACHED.
- **design-intent** — Decision 41 (`design/arch/decisions/0041-*.md`,
  amended Sprint 64 + Sprint 66) names Introspection as the canonical
  store, populated by frontend's `populate_introspection_after_expand`
  pass (sequence line 111) and backend's direct writes during
  `compile_to_module`. Symmetry across DefKinds is explicit in the
  `DefKind::Macro` rustdoc (just-amended Phase 3, lines 957–1006) —
  "introspection lives elsewhere — symmetric across all DefKind
  variants". The same principle applies to non-Def variants holding
  introspection-adjacent data: TypeDef's `sexp` exists for the same
  REPL regeneration purpose (deftype `.cl` regen per
  `repl/spec.md` §15.4); the canonical store for that data is
  Introspection keyed by FQSymbol — same path UserFn uses (and as the
  amended Macro variant points consumers to).
- **difference** — A field declared on the types-layer variant that no
  producer ever populates and no consumer ever effectively reads,
  competing with the D41 canonical store. This is the exemplar pattern
  that motivated Phase 3's `DefKind::Macro.sexp` removal — applied
  there but not swept here.
- **proposed disposition** — **source moves**: drop `sexp: Option<Sexp>`
  from `ModuleEntry::TypeDef`. The save.rs `generate_types` arm migrates
  to read from `introspection: &DashMap<FQSymbol, Introspection>` (the
  same path already used by `generate_fns_and_macros` for ordinary
  defns). Cache-hit residual gap (Introspection not rehydrated from
  cache) applies symmetrically to TypeDef as to UserFn — tracked at
  FIXME 0220 (no new architectural debt).
- **rationale for disposition** — Default is source-moves; the field
  competes with the D41 canonical store; every construction site
  writes None; the reader is dead-arm by construction; the cleanup is
  exactly parallel to the Phase 3 D41-violating-shadow-fields cleanup
  on `DefKind::Macro`. Consumer cascade is small (one save.rs arm + 7
  construction-site field removals — all noisy `sexp: None,` lines).

---

### Finding 2 — `ModuleEntry::TraitDecl.sexp: Option<Sexp>` is dead and D41-violating

- **Lens**: 2 + 4.
- **Site**: `crates/cranelisp-types/src/module.rs:691-695` — the `TraitDecl`
  variant's `sexp: Option<Sexp>` field declaration; reader at
  `src/save.rs:222-228` (`generate_traits`).
- **facade-expects** — same as Finding 1.
- **source-does** — Every TraitDecl construction site writes `sexp: None`:
  `crates/cranelisp-typecheck/src/traits.rs:137` + `:227`. Search for any
  `TraitDecl { sexp: Some(_), .. }` population — zero hits. Reader
  `src/save.rs:220-235` pattern-matches `Some` — dead-arm.
- **design-intent** — Same as Finding 1: Decision 41 names Introspection
  canonical for trait-decl regeneration; D41's symmetry-across-Def-variants
  invariant (just-amended Macro rustdoc) extends to non-Def variants
  holding introspection-adjacent data for the same `.cl` regen purpose.
- **difference** — Same structural pattern as Finding 1: field declared,
  never populated, dead-arm reader.
- **proposed disposition** — **source moves** (bundled with Finding 1):
  drop `sexp: Option<Sexp>` from `ModuleEntry::TraitDecl`; `save.rs`
  arm reads from Introspection.
- **rationale for disposition** — Identical reasoning to Finding 1; the
  two fields share a single architectural error (carrying regeneration
  sexp on the types-layer variant rather than in Introspection per D41).
  Bundle for a single coherent cascade.

---

### Finding 3 — `ParsedEntry::TypeDef.type_params: Vec<TypeName>` newtype mismatch

- **Lens**: 1 (un-cascaded — the S69-era newtype-discipline cascade
  missed this site).
- **Site**: `crates/cranelisp-types/src/parsed.rs:38`. Compare
  `TopLevel::TypeDef.type_params: Vec<Symbol>` (`ast.rs:560`) +
  `TypeDefInfo.type_params: Vec<Symbol>` (`check.rs:137`) +
  `TraitDecl.type_params: Vec<Symbol>` (`ast.rs:497`).
- **facade-expects** — per the crate-root `//!` `lib.rs:94-97`
  ("Newtype discipline — no bare `String` for anything that names
  something in the language") + `src/CLAUDE.md` §"Naming Conventions"
  + `design/arch/CLAUDE.md` §"String Newtypes" — type parameters are
  the lowercase value-level vars (`a`, `b`, `c` per spec §3 + §5.2),
  semantically `Symbol`s (binding-name newtype), NOT `TypeName`s
  (upper-case type identifier newtype). Every downstream destination
  for the same data — `TopLevel::TypeDef.type_params`,
  `TypeDefInfo.type_params`, `TraitDecl.type_params` — agrees on
  `Vec<Symbol>`. Spec §5.2 EBNF for `type_params` produces lowercase
  symbols; the `TypeName` newtype is reserved for upper-case named
  types per `design/arch/CLAUDE.md` §"String Newtypes".
- **source-does** — `ParsedEntry::TypeDef.type_params: Vec<TypeName>`,
  populated at `crates/cranelisp-frontend/src/ast_builder.rs:368` by
  string-converting from `Vec<Symbol>` (`TypeName::from(s.as_ref())`),
  then consumed at `crates/cranelisp-typecheck/src/form.rs:263` by the
  inverse conversion (`Symbol::from(t.as_ref())`). The cross-newtype
  churn is purely a marshalling artefact; both sides have the right
  data in the right newtype already.
- **design-intent** — Principle 7 (single source of truth — same
  semantic concept has one structural form) + the String-Newtypes hard
  rule (newtype identifies semantics, not just shape). `TypeName` and
  `Symbol` exist precisely so that a reader can tell at-a-glance
  whether a field names a type vs. a binding. Type parameters are
  bindings (introduced by the type's quantification; spec §5.2.4
  scope rules treat them as binders identical to value-level let
  bindings). The mismatch on `ParsedEntry::TypeDef` is editorial drift
  — no Decision authors `Vec<TypeName>` here, and every downstream
  store target-states `Vec<Symbol>`.
- **difference** — A newtype-discipline regression. The producer
  converts `Symbol → TypeName` only for the consumer to convert
  `TypeName → Symbol` immediately. Readers tracing
  "where do type params come from?" hit the `TypeName` newtype which
  is the wrong semantic anchor.
- **proposed disposition** — **source moves**: narrow
  `ParsedEntry::TypeDef.type_params: Vec<TypeName>` →
  `Vec<Symbol>`; delete the two conversion sites
  (`ast_builder.rs:365-371` lift retired;
  `form.rs:260-273` conversion retired) and pass `Vec<Symbol>`
  through.
- **rationale for disposition** — Default is source-moves; no Decision
  grounds the `TypeName` choice on this field; every downstream
  store uses `Symbol`; the newtype-discipline rule (`lib.rs:94-97`)
  is unambiguous. Tiny consumer cascade (two conversion sites and
  the test fixture at `form.rs:344`).

---

### Finding 4 — `Pattern::Constructor.name: Symbol` (vs. constructor-FQ semantics post-D47)

- **Lens**: 1 (un-cascaded — Decision 47 FQ-binding ruled at
  resolved-stage boundaries; the constructor name on a `Pattern` reaches
  the resolved stage but stays bare `Symbol`).
- **Site**: `crates/cranelisp-types/src/ast.rs:62-68`.
- **facade-expects** — Per Decision 47
  (`decisions/0047-fqtypename-binding-at-resolved-stage-boundaries.md`)
  FQTypeName is binding at resolved-stage boundaries with two narrow
  named exceptions (syntactic-lift at `check_form`; receiver-pinned
  helpers). Pattern matching is consumed *post-typecheck* by backend
  codegen — that is a resolved-stage boundary.
- **source-does** — `Pattern::Constructor.name: Symbol` carries the
  bare constructor name through to backend. Backend's `compile_match`
  takes the symbol and resolves it module-locally to a Def +
  `DefKind::Constructor { type_name: FQTypeName, tag, .. }` — the
  resolution happens at codegen time, not at typecheck time.
- **design-intent** — D47's two-exception clause is narrow and named;
  this site is not one of them. Spec §6.2 (Pattern grammar) is
  agnostic to the resolved-stage shape (it's a grammar production).
  Decision 47's intent — eliminate "bare name slips through" — is the
  governing pattern; the post-typecheck shape should carry the FQ
  reference, parallels TypeExpr::Named → Type::ADT(FQTypeName, _) lift
  at the same boundary.
- **difference** — A site where the bare `Symbol` survives past
  typecheck without one of D47's two named exceptions justifying it.
- **proposed disposition** — **File FIXME** `target: /arch`. This
  warrants more analysis than a straight `source moves` because the
  resolution work for constructor names in patterns is non-trivial
  (the constructor's owning ADT must be discoverable from the
  scrutinee type — typecheck already does this work to produce
  `Expr::ConstrADT` on the constructor *expression* side; the
  symmetric work would lift `Pattern::Constructor.name: Symbol` to
  `name: FQSymbol` post-typecheck). The pattern's place in the AST
  also raises the question of whether typecheck annotates the pattern
  in-place (parallel to `Expr.inferred_type`) or whether `Pattern`
  variants gain an `Option<FQSymbol>` annotation field.
- **rationale for disposition** — Not a clear source-moves like
  Findings 1–3. Architectural design call needed: whether to lift the
  whole `Pattern::Constructor` to FQ (and how — direct replacement vs.
  annotation field), which has cross-crate consumer ramifications
  (frontend builder, typecheck checker, backend codegen). FIXME the
  analysis; do not block consumer-crate cascade on it now.

---

### Finding 5 — `ConstrainedFn.defn: Defn` carries the pre-decomposition Defn (asymmetric with the post-S69-S35 ast-narrow)

- **Lens**: 3 (struct-vs-rustdoc / Decision drift).
- **Site**: `crates/cranelisp-types/src/module.rs:1057-1061`.
- **facade-expects** — S69 Submission 35 narrowed `ModuleEntry::Def.ast`
  from `Option<Defn>` to `Option<DefnVariant>` per minimum-mechanism +
  Principle 7 (single source of truth). The rationale in the
  `Def.ast` rustdoc (`module.rs:546-580`) is explicit: the outer
  `Defn` wrapper carries only duplicate metadata (name, docstring,
  variants, visibility, span) that the entry's own fields already
  canonicalise; "the outer `Defn` wrapper does not propagate past
  that decomposition boundary."
- **source-does** — `ConstrainedFn` carries `defn: Defn` (the outer
  wrapper, including the `Vec<DefnVariant>`) plus `scheme: Scheme`.
  This pre-dates Submission 35.
- **design-intent** — S69 Submission 35's narrative (audit memo
  §"S-DRIFT-6") names the structural reason for narrowing: a
  constrained-fn template stores the single meaningful payload — its
  variant — alongside the polymorphic scheme. The outer `Defn`
  wrapper duplicates metadata already canonical on the parent
  `ModuleEntry::Def` (the entry that holds the
  `DefKind::UserFn { constrained_fn: Some(Box<ConstrainedFn>) }`).
  Submission 35's logic applies symmetrically: a `ConstrainedFn`
  inside a `Def`'s `kind` field has the same "outer wrapper carries
  only duplicate metadata" problem. The `ConstrainedFn.defn.name`
  duplicates the parent Def's symbol-table key; `defn.variants` is
  again `.len() == 1` for the single-variant template case (multi-
  variant constrained-fn templates being a separate question per
  the `add$Int+Int` etc. decomposition path).
- **difference** — The S35 narrowing landed on `Def.ast` but did not
  cascade to `ConstrainedFn.defn` — leaving Principle 7 unevenly
  applied across the two sibling sites that hold the "function body"
  payload.
- **proposed disposition** — **File FIXME** `target: /arch` for
  detailed analysis. Confirmation needed that single-variant
  constrained-fn templates are universal (multi-sig + constrained
  poly interaction noted in `memory/MEMORY.md` as "not yet
  supported"); if confirmed, narrow `defn: Defn → variant: DefnVariant`
  by the same minimum-mechanism logic. If multi-sig + constrained
  poly DOES need multi-variant constrained-fn templates eventually,
  the structural shape may need to remain `Defn` (or move to
  `Vec<DefnVariant>`); either way, the asymmetry deserves a deliberate
  resolution rather than the current "S35 cascaded to one site, not
  the other".
- **rationale for disposition** — Not a clear source-moves; the
  narrowing logic depends on a design call about multi-sig +
  constrained-poly interaction. FIXME for `/arch` analysis without
  blocking the lens 1–4 source-moves.

---

### Finding 6 — `Sexp::Comment` variant relevance check (minor — informational)

- **Lens**: 2 (dead field — partial).
- **Site**: `crates/cranelisp-types/src/sexp.rs:23`.
- **facade-expects** — `lib.rs` re-exports `Sexp` as the reader's
  output type. The crate-root `//!` does not enumerate variants.
- **source-does** — `Sexp::Comment(String, Span)` variant exists,
  rustdoc names "preserved only in comment-preserving reader mode".
- **design-intent** — Need to verify "comment-preserving reader mode"
  is a live concept. If no reader path produces `Sexp::Comment` in
  the v4 pipeline, the variant is dead-discriminator.
- **difference** — Possibly a dead variant; possibly an aspirational
  surface waiting for a comment-preserving reader. Out-of-sweep
  rather than load-bearing finding.
- **proposed disposition** — **No action** within this sweep; flag for
  follow-up consumer-trace (search for `Sexp::Comment(_, _)`
  population sites). If zero hits, file as a separate FIXME; if hits
  exist, the variant is justified.
- **rationale for disposition** — The variant might be live in
  reader paths I didn't enumerate; verifying takes more time than
  the sweep budgets. Defer to a focused follow-up trace.

---

## Summary

| # | Lens | Site | Proposed disposition |
|---|---|---|---|
| 1 | 2 + 4 | `module.rs:653-658` `ModuleEntry::TypeDef.sexp` | source moves (drop field; migrate to Introspection) |
| 2 | 2 + 4 | `module.rs:691-695` `ModuleEntry::TraitDecl.sexp` | source moves (drop field; bundled with Finding 1) |
| 3 | 1 | `parsed.rs:38` `ParsedEntry::TypeDef.type_params: Vec<TypeName>` | source moves (narrow to `Vec<Symbol>`) |
| 4 | 1 | `ast.rs:62-68` `Pattern::Constructor.name: Symbol` (post-D47 FQ binding) | file FIXME `target: /arch` |
| 5 | 3 | `module.rs:1057-1061` `ConstrainedFn.defn: Defn` (post-S35 asymmetry) | file FIXME `target: /arch` |
| 6 | 2 | `sexp.rs:23` `Sexp::Comment` variant — verify-live check | no action (out-of-sweep trace) |

## Sweep verdict

**TYPES SOLID — 5 actionable findings (3 source-moves, 2 FIXME-deferrable) + 1 informational.**

The lens-1 / lens-2 / lens-4 patterns surfaced exactly the kind of un-cascaded
residue Phase 3 was searching for. Findings 1 and 2 are the same architectural
error as the Phase 3 `DefKind::Macro` finding — introspection-adjacent data
carried on a types-layer variant in violation of Decision 41. Finding 3 is a
clean newtype-discipline regression with no Decision grounding for the wrong
choice. Findings 4 and 5 are subtler — they need design analysis before
source action.

**This does NOT block consumer-crate cascade.** Findings 1 + 2 + 3 are
internal to `cranelisp-types` (with a small `save.rs` follow-up for 1 + 2)
and can land in a focused `/dev (types)` fire without touching consumer
crates' Phase 3 cascade work. Findings 4 + 5 are FIXME-deferrable.

**Phase 3's open consumer cascade work (e.g., the `ModuleEntry::Macro` arm in
`src/save.rs` + `src/session_v4.rs:3470` + `src/worker.rs:1325-1340`) remains
the next step regardless** — those are downstream of the now-amended
`DefKind::Macro { clauses_meta }` shape, and the lens-2 cleanup proposed here
in Findings 1 + 2 sits alongside (does not gate) that work. FIXME 0219 already
covers the macro-arm unification.

## Out-of-sweep (deferred to other lenses)

- **`Sexp::Comment` variant liveness** — Finding 6 (deferred pending a focused
  consumer-trace; if dead, file a separate FIXME).
- **`SchedulingClass::Default` derive** — S69 Sub 37 kept this as a small
  forward-compat courtesy; no action.
- **`ModuleEntry::Ambiguous.visibility: Visibility`** — S69 confirmed this as
  variant-uniformity stub; no action.
- **`SymbolTable` concurrency complex** (HashMap → DashMap; `next_got_slot`
  AtomicUsize) — S69 audit named source-moves; tracked in /dev wave-3
  concurrency-cluster brief (out of scope for this sweep; not lens-1/2/3/4
  shape).
- **`pub mod` exposure of submodules** — S69 Sub 41 reduced all to
  `pub(crate)`; sweep confirms current state matches.
- **Per-name span on imports/exports + per-field span on FieldDef** — S69
  audit (H11 / S-DRIFT-4 / S-DRIFT-12) named source-moves grounded in
  Decision 39; in /dev wave-3 brief.
- **`MacroClause.body_sexp`** — Per `parsed.rs` rustdoc this is a legitimate
  parse-time-only transient consumed by `synthesize_macro_clause_defn`. No
  D41 violation (data does not persist on `SymbolTable`).
- **`ConstrainedFn.scheme: Scheme`** — D47-compliant (`constraints:
  HashMap<TypeId, Vec<FQTraitName>>` at `types.rs:115`). Confirmed solid.
- **`Sexp` variant set** — Reader's output (frontend-internal-facing across
  crate boundary); shape solid; no D41 / dead-field issues.
- **All `error.rs` / `newtype.rs` / `span.rs` / `marshal.rs` / `got.rs` /
  `heap.rs` / `scheduling.rs` / `pipeline.rs` types** — swept; no findings
  in the four lenses. Items dispositioned by S69 (Sub 37–39, 41) are
  confirmed at-target.
