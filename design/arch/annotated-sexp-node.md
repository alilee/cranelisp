# The `Sexp::Annotated` node — read-time annotation fold contract

**WORKING (S115 `/arch`, design-only; implements the 2026-07-21 USER RULING on
FIXME 0708 — Reading A-structural). Binding cross-crate contract for the S116
implementation waves.** Archive trigger: the S116 flip wave lands + this
contract folds into `crates/cranelisp-types/src/sexp.rs` rustdoc +
`interfaces.md` §"Sexp" + BC §1/§7 + the frontend/int crate CLAUDE.md files.

Ruling (recorded `sprints/SPRINT.md` §Notes, 2026-07-21): `:Type <form>` parses
to a NEW structural annotated node at READ time — one fold rule in the reader,
visible in the `Sexp` tree, so macros receive the folded node in argument
position (`(def x :Int 5)` = two macro arguments). The metadata side-channel
was rejected (silent annotation loss; annotations ASSERT). The AST-builder's
scan-and-pair fold retires.

---

## 1. The node shape

Added to `cranelisp_types::Sexp` (`crates/cranelisp-types/src/sexp.rs:7`):

```rust
/// `:Type <form>` — the read-time annotation fold (spec §1.4.5/§2.3.8;
/// user-ruled 2026-07-21, FIXME 0708 Reading A-structural).
Annotated {
    /// The annotation half: the raw form following `:`, colon STRIPPED —
    /// `Symbol("Int", …)` for `:Int`, `Symbol("primitives/Int", …)` for a
    /// qualified name, the compound `List` for `:(Fn [a] a)`. A raw `Sexp`,
    /// never a `TypeExpr` (see rationale).
    annotation: Box<Sexp>,
    /// The subject: the immediately-following form the annotation binds.
    subject: Box<Sexp>,
    /// Introducer-start .. subject-end.
    span: Span,
},
```

**Named fields, deliberately** (the only variant with two same-typed slots —
naming makes annotation/subject transposition unwritable at construction
sites; Principle 20 by representation).

**The annotation half is a raw `Sexp`, NOT a distinguished type-expr slot.**
Four grounds:

1. **Layering** — the reader is purely syntactic (frontend BC invariant; it
   names no type vocabulary). `TypeExpr` is an AST-builder product
   (`build_type_expr`, `ast_builder.rs:2274`); parsing types in the reader
   would smuggle the type grammar down a layer.
2. **The macro contract** — macros quote, unquote, and destructure the half.
   It must be representable in the `macros/Sexp` ADT (§3), which is
   Sexp-shaped; a `TypeExpr` slot would be opaque to quasiquote and to
   `SexpAnnotated` destructuring.
3. **Quasiquote** — `` `(f : ~t x) `` requires the half to hold an arbitrary
   pre-desugar form (`(unquote t)`), which only `Sexp` can.
4. **Validation stays where it is** — `build_type_expr` remains the sole
   type-grammar gate; the RA-N5 located reject ("the form bound by `:` must be
   a type expression") is preserved at the same seam, now consuming the node's
   annotation half instead of a sibling scan (`try_consume_annotation`,
   `ast_builder.rs:1952`). The reader folds STRUCTURALLY regardless of the
   half's kind (`:5 x` folds; the AST builder rejects it located) — exactly
   today's division of labour, one position earlier.

**Colon stripped from the half.** The node itself IS the colon. This makes the
simple and compound cases uniform (`:Int` and `:(Fn [a] a)` both yield a plain
half), and it retires the string-prefix dispatch (`starts_with(':')`) that
today encodes annotation-ness in symbol TEXT — position moves into the tree
(Principle 18: the invariant "never a standalone atom" becomes structurally
unrepresentable; there is no `:X` symbol to stand alone).

## 2. Fold semantics

**One rule, one site**: `reader.rs::read_colon_prefix`
(`crates/cranelisp-frontend/src/reader.rs:388`) becomes the fold. On a colon
introducer it reads the annotation half — the adjacent symbol run including
the qualified tail (`read_qualified_tail`, `reader.rs:673`, unchanged;
`:foo/` stays the S114 located reject), or, for a bare `:`, the NEXT form —
then reads the subject as the next form, and returns `Annotated`. Because
`read_form` is recursive, the fold applies in **every Sexp-producing
context** with no per-position code: top level, list interiors, bracket
interiors (`[:Int x :Int y]` → two `Annotated` elements), quote/quasiquote
bodies, and — the 0708 fix, by construction — macro-argument position, which
no longer exists as a distinct case at read time.

- **Nesting.** Subject recursion gives `:A :B x` =
  `Annotated(A, Annotated(B, x))`. The stacked-bounds rule (spec §3.9.3;
  `annotation_run_carrier`, `ast_builder.rs:2195`) reshapes from
  flat-run-scan to nested-chain walk: chain length >1 → `TypeExpr::Bounds`,
  length 1 → the try-type-then-trait carrier. Same semantics, new shape.
- **Spaced bare colon stays legal** (parity): `: Int x` and `: (Fn [a] a) x`
  fold identically to the adjacent spellings (today the bare-`:` AST pairing
  is adjacency-blind; preserve).
- **Error forms.** An introducer with nothing to bind — at EOF, before `)` /
  `]`, or as the sole remainder of an input line — is a **located reader
  error** with the EXISTING message text `annotation missing expression`
  (the §1.4.5-pinned wording; moving the site must not change the words —
  the [Tested] rows at §1.4.5 re-point to the reader tests, /qa sweep). The
  RA-N5 non-type-half reject stays AST-builder-side, text unchanged.
- **Quote/quasiquote: the fold applies.** Read-time precedes quote handling
  (Clojure `^` precedent — attaches at read, before any macro or quote sees
  the form). `'(:Int 5)` reads as `(quote Annotated(Int, 5))` and evaluates
  to a `(macros/SexpAnnotated …)` value. Int's quote shield
  (`expander.rs:848–880`) is unaffected — it holds list HEADS; the fold is
  below it.
- **Unquote in either half is supported**: `` `(f : ~t x) `` gives
  `Annotated((unquote t), x)`; the quasiquote template arm (§5) recurses
  both halves through ordinary template expansion, so a live `~` substitutes.
- **Unquote-splicing AS a half is a located error** — `~@` splices multiple
  forms into a list context; both node slots are single-form. The template
  arm routes each half through the existing template walk, whose non-list
  splice arm already rejects; the message is specialized to name the
  annotation slot.
- **Comments (preserving reader mode only).** Comments encountered between
  the introducer and its halves are HOISTED to precede the `Annotated` node
  in the output stream. Tree-render regen reorders them; the regen authority
  is source-text-first (`verbatim_source_slice`), so fidelity is unaffected.
  (The compile pipeline's non-preserving reader never sees this case —
  `src/marshal.rs:63` precedent.)

## 3. The macro-facing contract

Macro arguments are raw `Sexp`s counted by int BEFORE AST build
(`try_expand_sexp`, `src/process_form/macro_resolution.rs:371`). With the
read-time fold the count is right by construction: `(def x :Int 5)` presents
`x` and `Annotated(Int, 5)` — two arguments.

Macros execute as native code over the **`macros/Sexp` language-level ADT**.
That ADT gains its 8th constructor:

```
(SexpAnnotated [:Sexp stype :Sexp sform])     ; tag 7, APPENDED
```

- **Tag**: `TAG_SEXP_ANNOTATED: i64 = 7` in
  `crates/cranelisp-types/src/marshal.rs` (append-only; tags 0–6 stable;
  order truth remains the registration sites below, per the tags-file
  rustdoc).
- **Registration — BOTH seeds, same change-set** (a pre-existing P7 mirror
  pair, order-lockstep already documented): production seed
  `src/bootstrap.rs::register_macros_module` (`src/bootstrap.rs:425`, ctor
  rows `:513–519`); test-fixture seed
  `crates/cranelisp-typecheck/src/builtins.rs::register_sexp_type`
  (`builtins.rs:498`).
- **Two-field cell**: `SCons` is the two-field precedent
  (`alloc_adt_3`, `crates/cranelisp-primitives/src/marshal.rs:74`;
  `alloc_scons`, `src/marshal.rs:209`).
- **Marshal arms**: compiler-side `sexp_to_runtime` (`src/marshal.rs:48` —
  note `Comment` there is `unreachable!`; `Annotated` gets a REAL arm) and
  `runtime_to_sexp` (`src/marshal.rs:79`); runtime-side `quote_sexp_build`
  (`crates/cranelisp-primitives/src/marshal.rs:253`) and the deep-RC walk
  (`deep_rc_inc_slist` sibling arm — the cell holds two heap children).

**What a macro observes and owes:**

- **Splice-transparent macros are annotation-correct for free.** A clause
  that binds an argument and only splices it (`~value`) transports the
  `Annotated` node unexamined — `stdlib/defs.cl::def` works with NO stdlib
  change (its ctor-match is on the NAME argument only, `defs.cl:26`).
- **Ctor-matching macros own their arms.** A clause that structurally
  matches an argument's constructors (`stdlib/derive.cl` style) and receives
  an annotated form hits its ordinary match-miss — a located macro-match
  failure at the macro, not a compiler artifact. The author adds a
  `(SexpAnnotated t f)` arm or unwraps. This is the bounded author-side tax
  the ruling accepted.
- **Destructure/rebuild**: `(match arg [(macros/SexpAnnotated t f) …])`;
  rebuild via the ctor or via `:`-syntax inside a quasiquote template.
- **Standard unwrap helpers** — recommended, stdlib-owned: a predicate +
  the two projections (working names `annotated?` / `annotation` /
  `unannotate`; /stdlib finalizes per Clojure conventions). Filed as
  **FIXME 0780** (`target: /stdlib`, S116). Not load-bearing for the
  mechanism.

**Expansion/qualification walks — the annotation-half parity rule.** Both
scope-aware walks over expansion I/O gain an `Annotated` arm with identical
treatment (they share the binder enumeration; `expander.rs:963–973`):

- **subject**: walked normally (it is expression position — may itself be a
  macro call, gets qualified).
- **annotation half**: a bare `Symbol` half is held VERBATIM (parity with
  today's `:`-prefix guards — `is_annotation_symbol`, `expander.rs:977`;
  `qualify_free_symbol`'s annotation skip, `macro_resolution.rs:437–440`);
  a compound half is RECURSED (parity with today, where `(SList Sexp)` after
  a bare `:` is an ordinary child — this is what qualifies cross-module type
  names inside compound annotations, which S66 current-module-only
  resolution depends on).

  The asymmetry is as-built behaviour relocated onto the node — deliberately
  parity-preserving for the flip. A future namespace-aware qualification of
  simple annotation names is a separate /spec+/design question; do not fold
  it into S116 (recorded here as the open refinement, no FIXME — the parity
  rule is complete and sound on its own).

## 4. Printer / round-trip

- `Sexp::format_flat`/`format_indented` (`sexp.rs:42/:81`): render
  `:{annotation} {subject}` — colon reintroduced ADJACENT to the half
  (`:Int x`, `:(Fn [a] a) x`).
- `src/pretty.rs::pp` (`:289`, exhaustive — compile-forced): annotation half
  in the type role, subject per its own kind; `is_type_annotation_list` /
  `pp_type_annotation_list` (`:548/:555`) reshape onto the node;
  `subtree_contains_pair_form` (`:385`) gains a descent arm.
- Verbatim styling `emit_source_spans` (`pretty.rs:216`): spans over original
  bytes — byte-identical by construction.
- `src/save.rs` regen: the colon-binding suppression hack — `is_bare_colon`
  + `render_children_flat`/`render_decl_sexp_indented` (`save.rs:250–322`) —
  **deletes** (it exists solely to re-attach a bare-`:` token to its
  following form; the node renders adjacently by nature). `render_decl_sexp`
  (`:203`) gains the arm; docstring reconciliation unaffected.
- **S20/S21 byte-identity pins: UNTOUCHED — verified.** Those pin the
  display-gate `:Type value` ECHO envelope (`display::envelope` /
  `render_type` over resolved `Type`s;
  `prelude-import-convergence.md` §3.5), not the Sexp printer. The Sexp-level
  outputs that DO change: a compound annotation that today re-renders with a
  separating space (`: (Fn …)` — the bare-`:` token + list through generic
  `format_flat`) now renders written-form `:(Fn …)`. Simple `:Int x` output
  is byte-identical. /qa golden sweep at the flip covers `/sexp`, `/expand`,
  regen goldens, repl demos.
- Round-trip law (pin as unit tests): `read(print(t)) == t` modulo spans for
  every tree containing `Annotated`; and `verbatim_source_slice`'s
  re-parse-consistency gate holds unchanged (structural `PartialEq` covers
  the new variant by derivation).

## 5. Consumer census (file:line; disposition per site)

Compile-forced (exhaustive matches — the P18 lever; each gains an arm):

| Site | Disposition |
|---|---|
| `cranelisp-types/src/sexp.rs:29/:42/:81` (`span`/`format_flat`/`format_indented`) | arms (§1, §4) |
| `cranelisp-frontend/src/quasiquote.rs:194/:223/:148` (`expand_quote_template`/`expand_qq_template`/`expand_quasiquotes`) | template arms → `SexpAnnotated` composite; `~@`-as-half located error |
| `src/expander.rs:678` (`rewrite_spans_unique`) | recurse both halves, fresh span |
| `src/pretty.rs:289` (`pp`) | §4 arm |

Wildcard/shape-guarded (compiler-silent — the census IS the guard; sweep
verified in `/review` at each wave):

| Site | Disposition |
|---|---|
| `cranelisp-frontend/src/reader.rs:388` (`read_colon_prefix`) | becomes the fold (flip wave) |
| `cranelisp-frontend/src/ast_builder.rs:1952/:2040/:2094/:2117/:2195/:387` | consume the node → `Expr::Annotate`; scan-and-pair retires (§6) |
| `cranelisp-frontend/src/ast_builder.rs:2274` (`build_type_expr`) | reject `Annotated`-as-annotation-half located (RA-N5 class; covers `: :Int x`) |
| `cranelisp-frontend/src/defmacro.rs:94/:142` (`parse_param_items`/`parse_bracket_pattern`) | `Annotated` in a macro-param binder slot = located reject (macro params are untyped) |
| `cranelisp-frontend/src/synth.rs` | ctor helper for the composite (the ONE synthetic-Sexp kit) |
| `src/expander.rs:831` (`expand_scoped`, `_ =>` at `:955`) + `:751` (`shield_qq`) | explicit arm, §3 parity rule |
| `src/process_form/macro_resolution.rs:466` (`qualify_scoped`) | explicit arm, §3 parity rule |
| `src/marshal.rs:48/:79` + `cranelisp-primitives/src/marshal.rs:253` + RC walks | §3 marshal arms |
| `src/bootstrap.rs:425/:513` + `cranelisp-typecheck/src/builtins.rs:498` | 8th ctor row, both seeds |
| `src/worker.rs:103` (`leading_annotation_len`) | RETIRES (§6) |
| `src/save.rs:203–322` | hack deletes; render arm (§4) |
| `src/pretty.rs:216/:385/:548/:555` | §4 |
| `src/repl/format.rs:336` (`format_sexp`) | arm (delegates to printers) |
| `src/eval.rs:603` (`check_bare_symbol_introspection`) | unaffected (Symbol-guarded; an `Annotated` input correctly falls to eval) |
| `src/process_form/dependency.rs:1307/:1445`, `module_extract.rs`, `src/platform.rs`, `session_v4/lifecycle.rs` | shape-guarded head-matching walks; no annotation can occupy the matched positions; sweep-verify only |

**Typecheck: UNTOUCHED — verified.** `cranelisp-typecheck/src/{checker,infer,
traits,program,…}` contain ZERO Rust `Sexp` consumption (workspace census);
typecheck consumes `Expr::Annotate` from the AST exactly as today — the
pairing merely happens earlier. The sole typecheck-crate edit is the
test-fixture ctor row above (bootstrap seeding, not inference). **Backend:
zero `Sexp` references — untouched.**

## 6. Persistence verdict

`Sexp` serializes into the cache on three carriers:
`DefKind::Macro.macro_sexp` (`cranelisp-types/src/module.rs:2083`),
`ImplSexp.sexp` (`:2424`), `ModDecl.inline_body` (`:2478`). A variant
addition is a serde-visible shape change on cache-carried data →
**`CACHE_SCHEMA_VERSION` bump required** (`crates/cranelisp-backend/src/
cache/mod.rs:371`, currently 22).

- **The bump window: ONE, in the S116 CS-1 types change-set** (22→23 if the
  S115 §17.6 chained-face contingency did not fire; else current+1 at S116
  open). Per the types-CLAUDE.md same-change-set rule the bump rides the
  types edit, not the flip; all S116 waves share this single window.
- **Marshal tags** are runtime-only (never serialized); tag 7 appends, 0–6
  stable.
- **`public-api.txt` impact: `cranelisp-types` only** (the variant + the tag
  const; regenerate per the baseline discipline). Frontend/int/typecheck
  public surfaces unchanged (`parse` signatures carry `Vec<Sexp>` opaquely).

## 7. Retirement list (the mirrors this deletes)

1. `ast_builder.rs` scan-and-pair: `try_consume_annotation` (`:1952`)
   sibling-scan reshaped to node consumption; `build_one_expr_at` (`:2040`)
   consumed-count bookkeeping; `build_args_with_annotations` (`:2094`) and
   `build_annotated_params` (`:2117`) pairing loops; `build_forms` (`:387`)
   top-level annotation grouping; the `:1631` sole-element special-case
   commentary (a one-child list is now ordinary).
2. `src/worker.rs::leading_annotation_len` (`:103`) — recognition-for-
   grouping mirror; grouping is automatic when an annotation is ONE sexp.
3. `src/save.rs` colon-suppression renderer (`is_bare_colon` +
   flat/indented suppression, `:250–322`).
4. `src/expander.rs::is_annotation_symbol` (`:977`) and its held-verbatim
   sites; `qualify_free_symbol`'s `:`-prefix guard — string-prefix
   annotation dispatch replaced by the variant.
5. `src/pretty.rs::is_type_annotation_list`/`pp_type_annotation_list`
   (`:548/:555`) reshape onto the node (list-head string test retires).
6. **Diagnostics**: the opaque ``macro `defs/def` returned malformed sexp …
   3 argument(s); clauses accept 2`` becomes UNREACHABLE for the annotated-
   argument shape (the count is 2 by construction);
   `no_matching_clause_error` (`src/expander.rs:172`) is retained for
   genuine arity misses. `annotation missing expression` relocates to the
   reader with text preserved; /qa re-points the §1.4.5 traceability rows.

## 8. S116 implementation plan sketch

Staging follows the S114 dormant-enums→flip template. All source-touching
waves serial; ONE schema window (§6).

- **W0 `/arch` (types)**: the §1 variant + exhaustive-match arms in
  `cranelisp-types` + `TAG_SEXP_ANNOTATED` + schema bump + `public-api.txt`
  + rustdoc/`interfaces.md`/BC §1/§7 cascade. Dormant (no producer).
- **W1 `/dev(frontend)`**: dormant consumers — ast_builder node-consumption
  path (scan-and-pair KEPT until flip), quasiquote/defmacro/synth arms; unit
  tests construct `Annotated` directly (Principle 5 — all pure functions).
- **W2 `/dev` by surface** (sprint splits per triad convention): int arms
  (expander/qualify/marshal/pretty/save/format + bootstrap ctor row) +
  `cranelisp-primitives` marshal arms + the typecheck fixture ctor row. All
  dormant.
- **W3 FLIP (`/dev(frontend)` + `/dev(int)` coordinated)**: `read_colon_
  prefix` folds; §7 retirements delete in the same wave; the S115 W1-rider
  RED pin (`(def x :Int 5)` succeeds) flips GREEN; golden sweep (compound-
  annotation spacing, `/sexp`/`/expand`/regen).
- **W4 `/qa` + `/testing`**: the variant×{pos,neg} matrix (the standing
  coverage-by-definition-variants category): fold × {expression, macro-arg,
  bracket interior, quote, quasiquote+`~`, `~@`-as-half, nesting/bounds,
  trailing-introducer error, `:foo/` reject, spaced-`:`} — one codepath, the
  matrix enforces it; round-trip pins (§4); `/stdlib` helpers (FIXME 0780);
  traceability re-point.

**/spec cascade rows (for /spec's next dispatch; not edited here):**

- **§1.4.5** — the colon fold is READ-time and produces the structural
  annotated node; "never a standalone atom" now holds unconditionally,
  macro-argument position included; trailing introducer is a read error
  (message unchanged); grammar production for the node; `: Int` spaced form
  legality stated.
- **§2.3.8** — `annotate_expr` is built FROM the read-time node; the
  "every expression position" enumeration is no longer load-bearing for the
  fold (position-independence is structural); the sole-element
  parenthesized-annotation note re-grounds on the one-child list.
- **§9 / §9.1** — the macro contract: macros receive folded nodes;
  `macros/Sexp` gains `(SexpAnnotated [:Sexp stype :Sexp sform])` (tag 7);
  quote/quasiquote of annotations; unquote-in-half; `~@`-as-half error;
  splice-transparency vs ctor-matching obligations; a normative
  `(def x :Int 5)` example.
- **§2.2 grammar** — sexp/atom production rows referencing `colon_prefix`
  re-anchor on the node.
- Rider: `repl/spec.md`/plan §12 item 1 diagnostic pin flips polarity
  (the form now succeeds) — /repl + /qa.
