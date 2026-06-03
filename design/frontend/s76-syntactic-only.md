# Frontend S76 — purely syntactic role (W-Macro deletion + 0230 `parse_type_expr`)

> Subordinate topic doc under `design/frontend/frontend.md` (the master). Owned by `/design`.
> Authored 2026-06-03 (Sprint 76 Phase 3). Pins the `/dev (frontend)` implementation target for the two S76 frontend scope items: **W-Macro** (delete the `expand` skeleton) and **FIXME 0230** (`parse_type_expr` named API).
>
> **Contract sources (canonical, normative):**
> - `design/arch/macro-availability-model.md` §0 — LOCKED decision (2026-06-03): defmacro-before-use; three-pass model; frontend is quasiquote-only.
> - `design/arch/macro-expansion-ownership.md` §2.1, §5 — the two-jobs split; frontend after the split; cascade map.
> - `design/arch/bounded-contexts.md` §1 — Frontend BC (already cascaded to the post-S76 shape: `expand`/`ExpansionError` retired; quasiquote stays).
> - `design/arch/fixmes/0230-frontend-parse-type-expr-named-api.md` — the named-API request.
>
> This doc is HOW frontend lands the change. It does not relitigate the LOCKED decision (that is `/arch`'s, settled). It does not edit source (that is `/dev (frontend)`'s) or `cranelisp-types`/`design/arch/` (those are `/arch`'s).

---

## 0. The post-S76 role — confirmation

After this sprint the frontend is **purely syntactic**: it owns three operations and nothing else.

1. **Parse** — source bytes → `Vec<Sexp>` (`reader.rs`; `parse`, `parse_preserving_comments`).
2. **Quasiquote desugar** — `` ` `` / `~` / `~@` / `(quote …)` → `macros/`-qualified constructor calls (`quasiquote.rs`; `expand_quasiquotes`, `expand_quote_template`, `next_synthetic_span`). Pure Sexp→Sexp, no execution.
3. **Build form** — expanded `Sexp` → AST (`ast_builder.rs`; `build_form`, `build_expr`) + module-identity normalisation (`module_extract.rs`; `extract_module_declarations`, with `super` resolution).

The frontend performs **no macro recognition and no macro execution** post-S76 (BC §1 invariant 2, as cascaded). Recognition is a `cranelisp-types` query (`resolve_macro_head`) driven by typecheck's within-form descent + int's Pass-1 loop; execution is int's, behind `cranelisp_types::MacroExpander`. Frontend neither looks up macro entries nor calls JIT'd clause code. This is the confirmation the sprint brief asked for: **frontend's only remaining macro-adjacent role is quasiquote desugaring, which is syntactic.**

The defmacro-shape helpers (`parse_defmacro`, `is_defmacro`, `is_begin`, `flatten_begin`, `synthesize_macro_clause_defn`) stay — they are *syntactic shape recognition + synthesis*, not recognition-of-a-macro-head-against-the-symbol-table. `int::process_cluster` consumes them to build per-clause `Defn`s (Decision 21); they are unaffected by the recognition/execution move and remain `pub`-at-root internal-but-exposed per the existing FIXME 0098 Phase 2 disposition. The W-Macro move does NOT narrow them; only `expand`/`ExpansionError` go.

---

## 1. W-Macro — the deletion inventory

### 1.1 What is DELETED (`crates/cranelisp-frontend/src/expand.rs`, whole file)

The entire `expand.rs` module is deleted (`macro-expansion-ownership.md` §2.1: "the structural-walk skeleton … is DELETED, not kept private", grounded in Principle 7 — keeping it private would mean two implementations of the same walk in two crates). The file's contents and their disposition:

| Item in `expand.rs` | Disposition | Why |
|---|---|---|
| `pub fn expand<C, L>(sexp, symbol_tables, module_aliases) -> Result<Sexp, ExpansionError>` | **DELETE** | The walk+recognize job moves to typecheck (its within-form descent calling `cranelisp_types::resolve_macro_head`) + int's Pass-1 loop. Frontend no longer owns it. |
| `pub enum ExpansionError` (`Gap` / `Malformed` / `MacroAborted`) | **DELETE** | `Gap`'s carrier role is now `CheckError::Gap` (typecheck-owned, already exists); the macro-execution error shape is `cranelisp_types::MacroInvokeError` (`Aborted`/`Malformed`, already authored). `Malformed`'s depth-limit role moves to typecheck's loop bound. |
| `pub const EXPANSION_DEPTH_LIMIT: usize = 100` | **DELETE from frontend** (relocates to typecheck interior) | The depth bound is now typecheck's expand-fixpoint loop invariant (`macro-expansion-ownership.md` §2.1). `/dev (typecheck)` lands the relocated const; frontend just drops it. |
| `fn expand_recursive<C, L>(…)` | **DELETE** | The recursive walk typecheck now owns. |
| `fn lookup_macro_fq<C, L>(…)` | **DELETE** | The bare-name "probe every module in `symbol_tables`" loop is the exact Principle-17 violation the LOCKED decision eliminates. Its replacement is the `cranelisp_types::resolve_macro_head` primitive (module-local, single-hop) — authored in `cranelisp-types` by `/arch`, called by typecheck + int, **not** by frontend. Net Principle-17 improvement. |
| `fn macro_entry_present<C, L>(…)` | **DELETE** | Subordinate to `lookup_macro_fq`; same disposition. |
| `#[cfg(test)] mod tests` (12 tests) | **DELETE** | All assert the skeleton's `Gap`-return behaviour or its `Malformed` depth-limit shape — both behaviours the LOCKED decision retires from frontend. There is no frontend-boundary behaviour left to assert (recognition/execution are gone). The `quasiquotes_desugared_before_macro_dispatch` test's *intent* (quasiquote runs before dispatch) is preserved by `quasiquote.rs`'s own tests, which already cover `expand_quasiquotes` directly. No test migrates to typecheck/int from here — `/qa`/`/dev (typecheck)`/`/dev (int)` author recognition/execution coverage against the new owners (per the W-Macro /dev wave breakdown, SPRINT.md §"/dev wave breakdown"). |

### 1.2 What STAYS (the syntactic core)

- **`crates/cranelisp-frontend/src/quasiquote.rs`** — `expand_quasiquotes`, `expand_quote_template`, `next_synthetic_span`, and all private `make_sexp_*` / `expand_qq_*` helpers + the `SYNTHETIC_SPAN_COUNTER`. **Unchanged.** This is the standing public syntactic API (used by user-authored macros at expansion time and by REPL `/expand`). The crate-root re-export `pub use quasiquote::{expand_quasiquotes, expand_quote_template, next_synthetic_span}` stays.
- **`reader.rs`**, **`ast_builder.rs`**, **`module_extract.rs`**, **`defmacro.rs`** — all unchanged by W-Macro (0230 touches `ast_builder.rs` — see §3).

### 1.3 `lib.rs` edits (W-Macro)

`crates/cranelisp-frontend/src/lib.rs` is `/dev (frontend)`-owned source; this doc states the target shape `/dev` must land.

1. **Module declaration** — delete `pub mod expand;` (line 383).
2. **Re-export** — delete `pub use expand::{expand, ExpansionError, EXPANSION_DEPTH_LIMIT};` (line 395).
3. **`ResolutionGap` re-export** — **delete** `pub use cranelisp_types::ResolutionGap;` (line 404). Its sole stated justification (lib.rs preamble §"Re-export policy" item 1) is "`ExpansionError::Gap(ResolutionGap)` consumers always need `ResolutionGap` in scope." With `ExpansionError` deleted, that justification evaporates — the re-export becomes a Principle-15 violation (a `cranelisp-types` item re-exported with no frontend-signature consumer). Consumers that still need `ResolutionGap` import it from `cranelisp_types` directly (it now travels with `CheckError::Gap`, a typecheck/types concern). **Baseline delta:** removes the `pub use cranelisp_frontend::ResolutionGap` line. *(Flag for /arch — see §5.)*
4. **Crate-root `//!` preamble** — the substantive rustdoc rewrite. Detailed in §2.

### 1.4 `Cargo.toml` — no change

Frontend's dep set is unchanged: it still depends only on `cranelisp-types` (BC §1, lib.rs preamble §"Consumed surface"). `expand.rs` named only `cranelisp-types` items, so deleting it removes no edge. `parse_type_expr` (0230) also names only `cranelisp-types` (`TypeExpr`, `CranelispError`). **No `Cargo.toml` edit.**

---

## 2. Crate-root `//!` preamble rewrite (the rustdoc-is-the-facade impact)

Per the retired-facade discipline (BC §1 "Per-surface documentation": the source rustdoc IS the facade), the crate-root `//!` is the canonical surface statement and MUST be rewritten in the same change-set. The current preamble carries ~120 lines of obsolete `expand`/FIXME-0175/MacroResolver/Gap-protocol narrative. The required edits:

| Preamble section (current) | Edit |
|---|---|
| Title line ("…with macro expansion as a frontend step") | **Rewrite** — "source text → S-expressions → AST, with quasiquote desugaring as the only syntactic-rewrite step." Macro expansion is no longer a frontend step. |
| §"Public surface — the form-by-form boundary" — the `ignore` block listing `expand<C,L>` | **Remove** the `expand` signature from the block. The boundary is now `parse`, `extract_module_declarations`, `build_form`, `build_expr`, plus the quasiquote trio + (new) `parse_type_expr`. |
| "Macro expansion MUST run BEFORE `build_form`…" paragraph | **Replace** — the ordering constraint is now int's Pass-1-before-`check_forms` concern (three-pass model). Frontend's local statement: "quasiquote desugaring runs before `build_form`; macro expansion is performed by int/typecheck before the expanded forms reach `build_form`." |
| §"Why the shape" — `[expand()]` bullet | **Delete** the `expand()` bullet; keep the `parse`/`extract`/`build_form`/`build_expr` bullets; **add** a `parse_type_expr` bullet (§3). |
| §"Expand and the FIXME 0175 invocation gap" (entire section) | **DELETE** — the gap is resolved by the W-Macro re-architecture; there is no frontend `expand`. |
| §"Gap protocol — uniform single-variant" (entire section) | **DELETE** — gap protocol moved to typecheck/int (`CheckError::Gap` + int's `process_cluster` retry). Not a frontend concern. |
| §"Module layout" table — `[mod@expand]` row | **DELETE** the `expand` row; keep the other five rows. |
| §"Macro-resolver helpers — internal-but-exposed" | **Keep, trimmed** — `parse_defmacro`/`is_defmacro`/`is_begin`/`flatten_begin`/`synthesize_macro_clause_defn` stay (Decision 21 consumer = int's `process_cluster`); `expand_quasiquotes`/`expand_quote_template`/`next_synthetic_span` stay (standing quasiquote API). Drop the "until FIXME 0098 Phase 2 migrates the invocation path" framing — there is no invocation path to migrate. |
| §"Types originated here" — "originates exactly one type … `ExpansionError`" | **Rewrite** — frontend now originates **zero** fully-own public types. `ExtractedDeclarations` remains the one public DTO (structural sugar over `cranelisp-types` items). `ExpansionError` is deleted. |
| §"Re-export policy" — item 1 (`ResolutionGap`) | **DELETE** item 1 (the `ResolutionGap` re-export goes — §1.3.3). Items 2 (`DefmacroInfo`) + 3 (`MacroClause`) stay (they back the `parse_defmacro`/`synthesize_macro_clause_defn` signatures, which stay). |
| §"`#[non_exhaustive]` DTOs" — "`ExtractedDeclarations` and `ExpansionError`" | **Rewrite** — "`ExtractedDeclarations`" only. |
| §"Bounded-context invariants" — invariant 5 (`expand` re-entrant), invariant 6 (`expand` side-effect-free), invariant 7's `ExpansionError` mention | **Rewrite to match BC §1's cascaded form**: invariant 5 + 6 retire (moved to typecheck §2 per BC §1); invariant 2 gains "post-S76 the frontend performs no macro recognition or execution"; invariant 7's `#[non_exhaustive]` clause drops the `ExpansionError` example (keep `ExtractedDeclarations`). Mirror BC §1 invariants 1–8 (the canonical cascaded text). |
| §"See also" — FIXME 0175 / FIXME 0098 rows | Replace FIXME 0175 link with `macro-availability-model.md` §0 + `macro-expansion-ownership.md`; keep FIXME 0098 reference only if a residual remains (assess at landing). |

**Net:** the preamble shrinks substantially. The deletion is the bulk; the only addition is the `parse_type_expr` per-item documentation (§3).

---

## 3. FIXME 0230 — `parse_type_expr` named API

### 3.1 The shape

```rust
/// Parse a single type-expression S-expression into the canonical
/// `TypeExpr` AST shape.
///
/// Bounded: **string in, one `TypeExpr` out**. The source must be a single
/// type-expression form (a bare type name, a `(Fn [..] R)`, or an applied
/// `(Name arg..)`) — NOT a program form, NOT a sequence. More than one form,
/// or zero forms, is a `CranelispError`.
///
/// Reuses the existing `parse` reader + the type-expression production
/// already in `ast_builder` (`build_type_expr`). No new grammar.
pub fn parse_type_expr(source: &str) -> Result<TypeExpr, CranelispError>;
```

### 3.2 Placement + implementation

- **Home:** `ast_builder.rs` (the type-expression production lives there: the private `build_type_expr` / `build_type_expr_from_list`, lines 1499–1547). Promote a thin public wrapper there; re-export at the crate root (`pub use ast_builder::parse_type_expr;`) so the boundary reads `cranelisp_frontend::parse_type_expr` in one import (matching the `build_form`/`build_expr` pattern).
- **Body:** `parse(source)` → assert exactly one `Sexp` (else `CranelispError::ParseError` naming the arity) → `build_type_expr(&sexps[0])`. `build_type_expr` is currently `fn` (private); `/dev (frontend)` either calls it from the same module (no visibility change needed since `parse_type_expr` lives in `ast_builder.rs`) or promotes the wrapper only. The wrapper is ≤ ~15 lines; the grammar already exists.
- **Signature note:** FIXME 0230's sketch shows `parse_type_expr(src, source_id: …)`. **Drop the `source_id` parameter.** No other frontend entry threads a source-id; `parse` itself takes only `&str` and produces `Span`s from byte offsets. A type-sig string from a DLL descriptor has no meaningful source file; the resulting `TypeExpr` spans are byte-offsets into the sig string, consistent with every other frontend parse. Keeping the signature `(&str) -> Result<TypeExpr, CranelispError>` matches the existing `parse` shape and the narrow-interface principle (Principle 2). *(This is a refinement of the FIXME's sketch, not a divergence from its intent — flag noted in §5 for /arch visibility, but it is within frontend's signature-shaping latitude.)*

### 3.3 What frontend does NOT do (the boundary with typecheck/int)

`parse_type_expr` returns `TypeExpr` (syntactic), **not** `Type` (resolved). This is BC §1 invariant 1 (no type inference; frontend never names `Type`/`Scheme`/`TypeId`). The int-side `parse_platform_type_sig` / `sexp_to_type` it replaces (in `src/platform.rs`) does TWO jobs conflated:

1. **syntactic** — string → form shape (`Fn`/`IO`/named). ← **this is frontend's `parse_type_expr`**
2. **resolution** — `Type::from_name`, `(IO T)` → ADT, unknown-name rejection. ← **this is typecheck's** (FIXME 0231 — platform sig typecheck entry; produces the resolved `Type`/`Scheme` for the `ModuleEntry::Def`).

So 0230 delivers only job 1. The int loader (FIXME 0233 — `parse_type_sig` removal) calls `cranelisp_frontend::parse_type_expr(sig)` → hands the `TypeExpr` to the typecheck entry (0231) → gets back the resolved `Type`. This is the clean two-stage split the FIXME's "frontend+typecheck pipeline" phrasing intends. Frontend owns no part of the resolution. **Sequencing:** 0230 (frontend, this doc) + 0231 (typecheck) are upstream producers; 0229/0233 (int) consume them (SPRINT.md Q3 confirms this ordering within the platform host-wiring wave).

### 3.4 Per-item rustdoc + baseline

- Per-item `///` on `parse_type_expr` carrying the bounded contract (string in / one `TypeExpr` out / single-form-not-program), per FIXME 0230's "Operational implication."
- Add a `parse_type_expr` bullet to the crate-root `//!` §"Why the shape" and a row to the §"Module layout" table (under `ast_builder`).

---

## 4. Baseline (`public-api.txt`) impact — full delta

`/dev (frontend)` regenerates `crates/cranelisp-frontend/public-api.txt` in the same change-set (baseline-diff discipline, `design/arch/CLAUDE.md`), via
`cargo public-api --omit blanket-impls,auto-derived-impls -p cranelisp-frontend > crates/cranelisp-frontend/public-api.txt`.

**REMOVED lines (W-Macro):**
- `pub mod cranelisp_frontend::expand`
- the entire `cranelisp_frontend::expand::ExpansionError` enum + variants + `Display`/`Error`/auto-trait impl lines (both the `expand::` and the root-re-export `cranelisp_frontend::ExpansionError` duplicate blocks)
- `pub const cranelisp_frontend::expand::EXPANSION_DEPTH_LIMIT` + `pub const cranelisp_frontend::EXPANSION_DEPTH_LIMIT`
- `pub fn cranelisp_frontend::expand::expand<C, L>(…)` + `pub fn cranelisp_frontend::expand<C, L>(…)`
- `pub use cranelisp_frontend::ResolutionGap`

**ADDED lines (0230):**
- `pub fn cranelisp_frontend::ast_builder::parse_type_expr(source: &str) -> core::result::Result<cranelisp_types::ast::TypeExpr, cranelisp_types::error::CranelispError>`
- `pub fn cranelisp_frontend::parse_type_expr(source: &str) -> …` (root re-export)

**UNCHANGED:** `parse`, `parse_preserving_comments`, `build_form`, `build_expr`, `extract_module_declarations` + `ExtractedDeclarations` (both qualified + root forms), the quasiquote trio, the defmacro-helper family + `DefmacroInfo`/`MacroClause` re-exports.

Net: a large reduction (one whole module + an enum with two duplicated blocks + two consts + two fns + one re-export removed) against a small addition (two fn lines). Consistent with "frontend's surface narrows to purely syntactic."

---

## 5. Seams flagged for `/arch`

These are surfaced for `/arch` visibility; none is a blocker — all are within the cascaded BC §1 + the W-Macro design, but each touches a shared concern:

1. **`ResolutionGap` re-export removal (§1.3.3).** Dropping `pub use cranelisp_types::ResolutionGap` is a baseline-visible reduction justified by `ExpansionError`'s deletion. BC §1 + `macro-expansion-ownership.md` §5 name the `ExpansionError` retirement but do not explicitly enumerate the `ResolutionGap` re-export as collateral. **Confirm:** `/arch` is content that the re-export goes (Principle 15 — no surviving frontend-signature consumer). If any consumer is found mid-migration to still `use cranelisp_frontend::ResolutionGap`, it re-points to `cranelisp_types::ResolutionGap` (a `/dev (int)` cascade item, likely already in W-Absorb).

2. **`parse_type_expr` signature drops `source_id` (§3.2).** FIXME 0230's sketch carries a `source_id` parameter; this plan drops it to match `parse`'s `(&str)` shape. Within frontend's signature latitude, but noted so `/arch` (and the int consumer 0233) sees the final shape is `(&str) -> Result<TypeExpr, CranelispError>` before int wires against it.

3. **Test ownership of recognition/execution (§1.1 last row).** The 12 deleted `expand.rs` tests are NOT migrated to frontend (no frontend behaviour remains). Recognition coverage lands in typecheck/types (`resolve_macro_head`) and execution coverage in int (`MacroExpander`), per the W-Macro /dev wave breakdown. No FIXME `target: /qa` is filed from frontend — the coverage owners are already named in SPRINT.md. Flagged only so `/arch`/`/sprint` confirm no frontend-side regression-guard is being silently dropped (the quasiquote-before-dispatch intent is already guarded by `quasiquote.rs` tests).

---

## 6. Master-doc reconciliation

`design/frontend/frontend.md` (the master) carries the obsolete `expand`-in-frontend / FIXME-0175 / MacroResolver / Gap-protocol narrative across §2 (surface table rows for `expand`), §4 (form-classification chain naming `expand`), §5 (entire "Macro expander architecture" section), §7.3/§7.4/§7.6 (`ExpansionError` + `expand` testability), §8 (Decision register), §9 (staleness register). This subordinate doc is authored as the **current S76 target**; the master is updated in this same `/design` pass to:

- §2 surface table — strike the `expand` row; add a `parse_type_expr` row; point the macro rows at this doc + `macro-expansion-ownership.md`.
- §5 "Macro expander architecture" — replace with a short "Macro expansion moved out (S76 W-Macro)" pointer to this doc + the arch docs; retain only the quasiquote-desugar description (which is syntactic and stays).
- §9 staleness register — add a row for this doc (Current); mark `macro-plan.md` + `macro-resolver-trait.md` as superseded by the W-Macro move (they describe a frontend-owned expander that no longer exists — candidates for archive in a follow-up `/design` pass).

The master edits are folded into the `/design` Phase-3 change-set alongside this doc.

---

## 7. Cross-references

- `design/arch/macro-availability-model.md` §0 — LOCKED decision (the foundation).
- `design/arch/macro-expansion-ownership.md` §2.1 (frontend after the split), §5 (cascade map).
- `design/arch/bounded-contexts.md` §1 — Frontend BC (cascaded target; this doc's HOW serves that WHAT).
- `design/arch/fixmes/0230-frontend-parse-type-expr-named-api.md` — the named-API request.
- `crates/cranelisp-frontend/src/lib.rs` `//!` — the canonical surface (rewritten per §2 by `/dev (frontend)`).
- `crates/cranelisp-frontend/src/ast_builder.rs` — home of `build_type_expr` (0230 reuses it).
- `crates/cranelisp-frontend/public-api.txt` — baseline (regenerated per §4).
