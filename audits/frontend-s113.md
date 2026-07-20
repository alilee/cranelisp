# cranelisp-frontend — Whole-Context Assessment (Sprint 113)

> **Rotation**: cranelisp-frontend, last assessed S87 (`audits/cranelisp-frontend-s87.md`;
> deep baseline `audits/frontend-20260423.md`). Twice-declined rotation, discharged S113.
> **Read scope**: all six source modules + their test siblings, `lib.rs`, `public-api.txt`,
> crate `CLAUDE.md`, all 15 `design/frontend/` docs, `plan-frontend.md`, spec §§2.3.8/5/7,
> `tests/plan/s113-test-plan.md` §1.2–1.3, open FIXMEs (0589/0613/0650/0651), S87
> disposition trail (`audits/s87-findings.md`).
> **Concurrent work**: W3 (`design/frontend/binder-head-reject.md`) is landing in this
> crate as this audit runs. This assessment covers the **pre-W3 state**; W3-adjacent items
> the wave should catch are flagged in §2.8, and the W3 diff itself is `/review`'s.
> **Method note**: read-only pass; no test-suite run (a source agent owns the suite this
> sprint). Defect candidates below are code-reading findings needing `/testing` repro pins.

---

## 1. Verdict

> Acid test: *if we lost this context's code and docs but retained the insight, would the
> lean second-time solution look like this?*

| Attribute | Grade | One-line basis |
|---|---|---|
| Design quality (fitness) | **strong** | six-module decomposition by concern, pure `&str`/`&Sexp` → value functions, narrow 4-function boundary — the rewrite keeps all of it |
| Design realisation | **adequate** | code matches the *current* design intent, but the master doc contradicts the code in both directions (§2.5), and the in-flight W3 design makes two false claims about current code (§2.8) |
| Simplicity & volume — code | **adequate–strong** | no god function, no unsafe, no gratuitous abstraction; residue = 5 dead retained sub-parsers + retired-"Ring N" user diagnostics |
| Simplicity & volume — docs | **weak** | ~5,350 doc lines for ~5,400 prod lines, of which ≥4 files are fully/partially superseded, one flagged "archive candidate" for ~37 sprints, and the master doc's own data (LOC, test counts, API table) is wrong |
| Simplicity & volume — tests | **strong** | 358 unit tests (49% of crate LOC), sibling-file convention held, message-seam and span assertions present |
| Duplication (the P7 lens) | **weak** | the crate's dominant debt: 4 standing families, 3 of them carried unactioned since the 2026-04-23 baseline through S87 to now (§2.4) |
| Risk-weighted coverage | **adequate** | production entry points are what the tests drive; the named gap is the operand-position × {ascription, trailing-junk} matrix (§2.2) — exactly the variant-matrix class /qa audits |
| Maintainability | **strong** | honest comments, documented caller contracts, invariant-justified `unreachable!`s, no hidden state beyond the one atomic counter |
| Memory freshness | **split** | crate `CLAUDE.md` is current and load-bearing (minor `~L` drift); `design/frontend/CLAUDE.md` still tells an agent the reader is a "PEG grammar" and the crate contains a "macro expander" — both false, the PEG half flagged in **three** successive audits |

**Overall.** The second-time solution would look **substantially like this code** — the
module partition, the purity discipline, the single-seam primitives
(`build_one_expr_at`, `reject_reserved_binder_name`, `parse_trait_head_shape`, one
synthetic-span counter) are exactly what a rewrite would produce, and the S87→S113 delta
shows real convergence (dual pipeline gone, tests siblinged, trait-head shape
single-sourced). It would **not** look like this in three respects. First, the rewrite
would apply its own single-seam discipline *uniformly*: today the `:Type`-binds-following-
form invariant is enforced at some operand positions and wrong-rejects at others, and the
"no trailing forms after body" check exists in `parse_defn` but not its two sibling
parsers — an enforcement matrix with holes, which is this crate's live defect surface
(§2.2). Second, it would carry **one** implementation each of {qualified-name split,
top-level-head classification, synthetic-Sexp construction, dotted-path lexing} instead
of 2–3 — the identical findings the 04-23 and S87 audits made, never actioned and never
formally declined (§2.4, §3 meta). Third, it would carry perhaps a third of the design-doc
volume: the corpus's accumulation of superseded narratives with supersession banners is
decay-in-waiting that already produces contradictions between files (§2.5).

---

## 2. Current state

### 2.1 Shape and volume

Prod ≈ 5,382 LOC across `reader.rs` (1,004), `ast_builder.rs` (2,029),
`module_extract.rs` (548), `defmacro.rs` (695), `quasiquote.rs` (445), `preamble.rs`
(269), `lib.rs` (392, of which ~340 rustdoc). Tests ≈ 5,238 LOC / 358 `#[test]`s in
sibling files (S87 F8's inline-bulk concern resolved by the sibling-file move; only
`preamble.rs` keeps inline tests, documented as the asymmetry in crate `CLAUDE.md`).
Public surface: 69 `public-api.txt` lines — 4 form-boundary functions + parse pair +
preamble capture + defmacro/quasiquote helper family + one `#[non_exhaustive]` DTO.
No `unsafe`, no I/O, no logging; the only shared state is `SYNTHETIC_SPAN_COUNTER`
(`quasiquote.rs:27`). Largest function ≈ 75 lines (`build_method_sig`). This is a lean,
well-bounded crate at the code level.

S87 baseline reconciliation: **resolved since S87** — F8 test bulk (sibling files);
trait-head two-parser drift window (S112's `parse_trait_head_shape`,
`ast_builder.rs:855`, is a model P7 consolidation). **Still open** — F1 (file split; the
2,029-line `ast_builder.rs` remains the single accretion point, though function-budget
clean), F2 (synth-Sexp DSLs), F3 (PEG docs), F4 (test/prod mirror), F5 (dotted-path
loops), F7 (head-set skew). No regressions found.

### 2.2 Live defect candidates — the enforcement-matrix holes (route to /qa + /testing now)

The crate's own invariant (crate `CLAUDE.md` §"`:Type` binds the FOLLOWING form": *"When
you add a new operand position, route it through `build_one_expr_at` — a raw `build_expr`
there silently drops annotation support"*) and spec §2.3.8 (*"an annotation MAY appear in
**every** expression position … an `if` / `fn` / **`let` body**"*) are enforced at N of M
positions. Read against every expression-position parser:

**Routed correctly** (via `build_one_expr_at`): defn single body (`ast_builder.rs:466`),
defn variant body (`:518`), `fn` body (`:1533`), `if` operands (`:1476-1487`), `match`
scrutinee (`:1572`) + arm bodies (`:1607`), `let` binding *values* (`:1451`), apply
head/args (`:1405-1406`), vec elements (`:1675`), top-level sequence (`:325`).

**Not routed — wrong-reject faces** (each `:Type body` form is spec-legal per §2.3.8 and
today errors):

| Position | Site | Face |
|---|---|---|
| `let` **body** | `build_let` `ast_builder.rs:1425-1430` — hard `children.len() != 3` + raw `build_expr` | `(let [x 1] :Int x)` → "let requires bindings and body" |
| impl-method body | `build_impl_method` `:1204` — raw `build_expr(&children[3])` | `(impl … (defn show [x] :Str …))` → "annotation missing expression" |
| trait default-method body | `build_method_sig` `:1007` — raw `build_expr(&children[ret_pos + 1])` | `(show [x] Str :Str "s")` → same error |
| `trace` operand | `build_trace` `:1377-1383` — hard arity 2 + raw `build_expr` | `(trace :Int x)` → arity error |

**Trailing-form silent-drop siblings** (the class already pinned RED for constructors —
`tests/spec_05_definitions.rs::deftype_ctor_trailing_form_after_field_bracket_rejected_neg`,
per crate `CLAUDE.md` §Known open defects — but never swept across the sibling parsers):

| Site | Face |
|---|---|
| `build_impl_method` `:1199-1204` — checks `< 4` only, ignores `children[4..]` | `(defn name [p] body junk)` inside `impl` silently drops `junk` (contrast `parse_defn:467-469`, which rejects) |
| `build_method_sig` `:1003-1010` — `default_body = children[ret_pos+1]`, ignores the rest | `(show [x] Str body junk)` silently drops `junk` |

**Case/qualification-check hole in `build_type_head`**: the bare-symbol arm requires
uppercase (`:599`); the `(Name params…)` list arm does **not** (`:606` — bare
`expect_symbol`), so `(deftype (point a) …)` passes the parser with a lowercase type
name, unlike `deftrait` where `parse_trait_head_shape` checks uppercase in *both* arms
(`:861/:884`). Type params also take any symbol, any case (`:607-613`). Downstream
behavior unverified (no suite run this pass) — needs a repro to classify silent-accept vs
late incidental error.

These are not recommendations; per the audit protocol they are defect candidates for
immediate `/qa` attribution + `/testing` pins. They are also one *family*: the
`variant × {positive, negative}` matrix (the standing /qa category) was never drawn for
"operand position × {bare, ascribed, trailing-junk}" and "head parser × case/arm", so
each parser grew its own subset of the checks — the exact mechanism the matrix exists to
prevent.

### 2.3 Resolution discipline (P24, the sprint's written-name identity class)

The frontend is the *write side* of name identity — it is licensed to split written names
— and it mostly behaves: reference-position type/trait names route through the §8.5
splitters at every impl site (`build_impl_target` `:1108/:1149/:1157/:1175`), value names
and pattern constructors are passed whole for `cranelisp_types::resolve` to split
(the arch-sanctioned asymmetry, FIXME 0328/0331). Two P24-adjacent wrinkles:

1. **The split rule is implemented three times in one file**: `type_ref_from_name`
   (`:1725-1732`), `trait_ref_from_name` (`:1741-1748`), and a third inline re-split
   inside `type_expr_to_trait_ref` (`:1905-1914`) — same `rsplit_once('/')` +
   both-halves-non-empty guard, mirroring a fourth in `cranelisp_types::resolve::split_qualified`.
   A drift in one guard is a D-qual divergence.
2. **The `type_expr_to_trait_ref` re-split is downstream compensation** for the 0589
   mis-classification: it exists because a `TypeVar` can currently carry `"fmt/display"`
   (lowercase-after-slash annotations mint slash-bearing TypeVars,
   `parse_annotation_name:1750-1758`). Once W3's 0589 routing fix lands ("lowercase +
   `/` → `Named` via the splitter"), the TypeVar arm's re-split becomes dead
   compensation — the P24 shape of a downstream site re-deriving what the decision point
   should have settled. It should be retired with the fix, not left as a fossil.

No instance of the sprint's headline "identity from written-name comparison" defect class
(two feeds disagreeing about one identity) was found in this crate — the frontend
compares written names only to *classify lexical shape* (case, `/`, head vocabulary),
which is its legitimate jurisdiction.

### 2.4 Duplication — the dominant debt, three audits running

Judged in the four facets:

- **Mirror.** (a) Test/prod: `ast_builder/tests.rs:13` `parsed_entry_to_top_level` and
  `:66` `is_top_level_form` are verbatim re-derivations of `ast_builder.rs:374/:356` —
  a prod head-set or entry-disposition change will not be reflected in the tests' router
  (S87 F4, unactioned). (b) Reader: the dotted-module-path loop appears twice,
  structurally identical (`reader.rs:609-661` in `read_symbol_or_keyword`,
  `:709-750` in `read_qualified_tail`) — S87 F5, unactioned.
- **Divergent.** The "parse a defn-shaped tail" operation exists three ways:
  `parse_defn`/`build_defn_variant` (docstring + multi-arity + ascription-routed +
  trailing-check), `build_impl_method` (none of the four — §2.2), `build_method_sig`
  default-body arm (none). Spec §7.3:238 legitimately narrows impl methods to
  single-arity/no-docstring, but ascription routing and trailing-form rejection are not
  spec narrowings — they are drift. The §2.2 defect faces *are* this divergence's cost,
  observed.
- **Entry-point.** "What is a top-level form" is expressed in three prod sites —
  `is_top_level_form_sexp` (`:356`), `build_form_inner`'s dispatch (`:226-266`),
  `parse_def_visibility` (`:131-141`) — plus the test mirror. They agree today; a new
  head added to one and not another routes the form to `build_expr` as a silent
  mis-parse, not an error (S87 F7, unactioned). Also: two synthetic-Sexp construction
  DSLs, `quasiquote.rs:75-162` vs `defmacro.rs:537-607`, both hand-building trees whose
  correctness depends on matching `ast_builder`'s reading exactly (S87 F2 / 04-23 #4,
  unactioned — the oldest open finding in the crate).
- **Spec-surface.** No redundant *language* construct originates here. One accidental
  second spelling: space-separated `: Name` is accepted as an annotation (the reader
  emits bare `:`, and `try_consume_annotation:1701-1708` accepts any following form
  `build_type_expr` can parse, not only compound `:(...)`) — a leniency cell, not a
  designed surface (see §2.7).

### 2.5 Design-doc fidelity — drift in both directions, plus internal contradiction

`design/frontend/frontend.md` (the master):

- §3.1 table: LOC and counts are stale by ~2× (`ast_builder.rs` "2915" vs 2,029 prod;
  `reader.rs` "1646" vs 1,004; "234 unit tests" vs 358).
- §2 table: claims `parse_import_sexp`/`parse_export_sexp`/`parse_mod_sexp`/
  `parse_platform_sexp` are "re-exported from `module_extract.rs`" — they are
  `pub(crate)` `#[allow(dead_code)]` with zero callers (`module_extract.rs:454-522`).
- §3.2 items 5–6 say the shared top-level classifier is "not yet implemented" — the
  `build_form`/`build_forms` single path landed (S87 confirmed it); the *residual* skew
  is F7, a different (smaller) gap than the doc describes.
- §4 item 3 narrates `int::process_form` calling frontend `expand(sexp, &symbol_tables)`
  as the current model — retired at S76; the banner at §4's head says to read it as
  historical, but the §4 body then interleaves current (§4.1, §4.2) with obsolete prose,
  so a reader must diff banners against paragraphs.
- **Internal contradiction across files**: `defmacro.rs:16-18/:210-212/:354` promise the
  helper family "narrows back to `pub(crate)` at FIXME 0098 Phase 2 close", while
  `lib.rs:167-169` states "Post-S76 … there is no 'narrow back' framing — these helpers
  stand on their int consumers alone." One of these is the contract; both are shipped
  rustdoc.
- `design/frontend/CLAUDE.md:15-16` still instructs documenting "PEG grammar structure"
  and a frontend-owned "macro expansion … MacroExpander trait implementation" — both
  false (hand-written reader; macro ownership left at S76). The PEG half is S87 F3,
  flagged in the 04-23 baseline (HIGH-5), again at S87, still live. `plan-frontend.md`
  §1 (lines 11-28) still records "Decision: `peg` 0.8" with porting instructions.
- `macro-resolver-trait.md` — marked "Superseded — archive candidate" in the master's own
  §9 register since S76 (~37 sprints); still present, still unarchived.

The load-bearing docs are in good shape: `binder-head-reject.md`, `trait-impl-head-parse.md`,
`quasiquote-fold.md`, `module-preamble.md`, `comment-preservation.md`, `reader.md`, and
the crate `CLAUDE.md` all match the code closely (two W3 exceptions, §2.8).

### 2.6 Risk-weighted coverage

Derived top risks and their pins:

1. **Silent-accept / silent-drop mis-parse** (the crate's actual defect history: D-qual
   S91, ctor trailing-form S107, binder heads S112) — partially pinned: the S113 BD
   matrix (`tests/plan/s113-test-plan.md` §1.2) pressures the binder-head seam
   well; the sibling cells in §2.2 are the unpinned remainder. **This is the gap.**
2. **Tokenization drift** (dispatch-order-is-load-bearing, crate `CLAUDE.md` §Reader) —
   pinned: 93 reader unit tests on the production `parse()` entry, covering the
   disambiguation table (float/int/operator/bool/colon/interior-operator).
3. **Synthetic-Sexp shape lock** (defmacro/quasiquote output must match `ast_builder`'s
   reading) — indirectly pinned via 40 defmacro/quasiquote unit tests + macro e2e
   (`spec_09_macros.rs`, `s76_macro_availability.rs`); no direct contract test, accepted
   since the baseline.
4. **Span integrity** (unique synthetic spans; located rejects) — pinned by the single
   allocator + the S112/S113 span-assertion discipline (`assert_err_span_at` rows).

Unit tests drive production entries (`build_form`/`build_forms`/`build_expr`/`parse`),
not a bespoke harness — with the one exception of the §2.4 test-adapter mirror, which is
both a duplication and a coverage-integrity issue (the adapter, not production routing,
decides what the assertions see). Spec-side: §5.8's "module name MUST be a simple symbol"
(`spec/05-definitions.md:566`) has **no negative test and no enforcement found** —
`parse_mod_decl` (`module_extract.rs:164-186`) accepts any symbol, including
`a.b` / `a/b` shapes the reader will happily produce (see §2.8, W3 flag ii).

### 2.7 Diagnostics posture (self-documenting REPL)

Generally strong — messages name the fix (`build_fn:1514-1520`'s single-arity message,
`build_constructor_def:650-656`'s write-`[:Type name]` message), `format_flat` not `{:?}`
(`module_extract.rs:537`), located spans throughout. Three leniency/degradation cells:

- `try_consume_annotation:1702-1707` **swallows** the `build_type_expr` error for a bare
  `:` + malformed compound form → falls through to `Expr::Var { name: ":" }` → opaque
  downstream "unresolved symbol". Same arm accepts space-separated `: Name` (§2.4).
- `read_qualified_tail` (`reader.rs:700-706, 737-742`) swallows `read_local_name` errors:
  `:foo/` with nothing valid after silently degrades to annotation `:foo`, `/` consumed.
- `reject_non_ring0_symbol` (`:411-433`) and `build_list_expr` (`:1321-1338`) emit user
  diagnostics naming "Ring 3"/"Ring 4" — a scheduling axis retired at S64; opaque to any
  user and stale against the project's own vocabulary.

### 2.8 W3 flags — pre-W3 facts the in-flight wave should catch (for /sprint → W3 dev/review)

1. **`binder-head-reject.md` §3 S2 mis-describes the insertion point**: "the reject
   applies to … `children[0]` **after it is confirmed to be an uppercase** `Sexp::Symbol`"
   — `build_type_head`'s list arm has **no uppercase confirmation** (`ast_builder.rs:606`;
   only the bare arm checks, `:599`). W3's one-line insert is fine either way, but the
   design's premise is false and the missing check is itself a hole (§2.2).
2. **`binder-head-reject.md` §8's `mod` exclusion rests on a false claim**: "`mod`
   already requires 'a simple symbol (not qualified, not dotted)' (§5.8) — **enforced at
   `module_extract.rs`**". No such enforcement exists in that file, and the BD matrix has
   no `mod` row — so the §5.8 MUST survives W3 unenforced and untested unless caught.
3. **Adjacent cells in the very functions W3 touches**: W3 threads the reject through
   `get_defn_name` (S1) and `build_method_sig` (S5) — the same functions carrying the
   §2.2 unrouted-body and trailing-drop faces. A wave that edits these lines is the
   cheapest moment to fix (or at least pin) the siblings.

### 2.9 Memory freshness

Crate `CLAUDE.md`: current, honest, load-bearing (the reader-dispatch table, the
annotation invariant, the D-qual section, the RED-guard record all check out against
code). Minor decay: `~L` line references drifted (`build_constructor_def` "~L604" → 623;
"annotation missing expression … ~L1131" → 1271); the routed-positions list omits none
falsely (it accurately reflects the holes — it never claims impl-method bodies are
routed). `design/frontend/CLAUDE.md`: stale on both counts named in §2.5 — it is the
worse offender because it is the *orientation* doc for a narrow-deployed `/design` agent.

---

## 3. Recommendations

Live-defect candidates (§2.2, §2.8 items 1–2) are **not** listed as recommendations —
per protocol they route to `/qa`/`/testing` for attribution + failing pins immediately
(surfaced in the dispatch return). The recommendations:

### R1 — Complete the operand-position and defn-tail enforcement matrices (the §2.2 family fix)
**Evidence**: §2.2 table (six unrouted/unchecked cells across `build_let`,
`build_impl_method`, `build_method_sig`, `build_trace`, `build_type_head`).
**Cost**: small (each fix is the `build_one_expr_at` + consumed-to-end idiom already
used at nine sites; the /qa matrix is two rows).
**Owner**: `/qa` (draw the `operand-position × {bare, ascribed, trailing-junk}` and
`head-parser × {case, arm}` matrices as standing rows) → `/testing` (pins) →
`/dev`(frontend) (fixes; unit test per fix per METHOD §2.2).
**Done**: every expression-position parser routes its body through
`build_one_expr_at` and rejects trailing forms; both `build_type_head` arms enforce the
same case rule; the matrix rows are green with negative twins. Done must cure the
*class* — a fix to only the pinned cells leaves the mechanism (no matrix) standing.

### R2 — One qualified-name splitter; retire the compensating re-split with 0589
**Evidence**: §2.3 — three in-file `rsplit_once('/')` implementations
(`ast_builder.rs:1725/:1741/:1905`) mirroring `cranelisp_types::resolve::split_qualified`;
the third exists to compensate the 0589 mis-classification W3 is fixing.
**Cost**: small.
**Owner**: `/dev`(frontend), with `/arch` sign-off only if the consolidation target is
the types-crate splitter (cross-crate).
**Done**: one splitting primitive in the crate (or direct use of the types-crate one);
`type_expr_to_trait_ref` no longer re-splits; a unit test pins that a slash-bearing
`TypeVar` cannot reach it (the structural fence outliving the 0589 fix).

### R3 — Single head classifier + tests call production (S87 F4+F7, third carry)
**Evidence**: §2.4 entry-point facet — head vocabulary in three prod sites + verbatim
test mirror (`ast_builder/tests.rs:13/:66`). Carried from 04-23 baseline → S87 → now;
never actioned, never declined.
**Cost**: small–medium (one `classify_head(head) -> HeadKind` consumed by
`is_top_level_form_sexp`, `build_form_inner`, and `parse_def_visibility`; test adapter
calls the prod functions and handles the `None` arm explicitly).
**Owner**: `/dev`(frontend).
**Done**: adding a top-level head requires exactly one edit; the test router cannot
drift from the prod router. **If declined, record the decline in this file's disposition
trail so the fourth audit stops re-litigating it.**

### R4 — Shared synthetic-Sexp kit (S87 F2 / 04-23 #4, third carry)
**Evidence**: §2.4 — `quasiquote.rs:75-162` and `defmacro.rs:537-607`, two constructor
DSLs over one implicit shape-lock with `ast_builder`. Oldest open finding in the crate.
**Cost**: medium.
**Owner**: `/dev`(frontend).
**Done**: one crate-internal `synth` module owns the primitive constructors
(`sym`/`int`/`str`/`list`/`bracket`/`cons`/`nil`); module-specific composites layer on
top; same accept-or-decline-permanently condition as R3.

### R5 — Doc-corpus refresh and prune
**Evidence**: §2.5 — stale master-doc data, false §2-table claim, PEG in
`design/frontend/CLAUDE.md:15` + `plan-frontend.md` §1 (third audit flagging),
`macro-resolver-trait.md` unarchived ~37 sprints after its own supersession note, the
`defmacro.rs` ↔ `lib.rs` narrowing-contract contradiction.
**Cost**: small–medium (deletion-heavy: archive `macro-resolver-trait.md`,
`plan-frontend.md` (or rewrite its §1 to hand-written), `sprint-70-cascade-plan.md`,
`implementation-slice-s66.md` to git history; correct `frontend.md` §§2/3.1/3.2/4;
rewrite `design/frontend/CLAUDE.md`'s "What to Document"; pick one narrowing story for
the defmacro helpers and fix the losing rustdoc).
**Owner**: `/design`(frontend) for `design/frontend/*`; `/dev`(frontend) for the
`defmacro.rs`/`lib.rs` rustdoc and `plan-frontend.md` (crate-local file).
**Done**: every file in `design/frontend/` is either current or in an archive location;
the master doc's §9 register has no "archive candidate" older than one sprint; no two
shipped docs state contradictory contracts.

### R6 — Hygiene batch: dead retained sub-parsers + retired-Ring diagnostics
**Evidence**: five `#[allow(dead_code)]` speculatively-retained functions
(`module_extract.rs:454-522` ×4, `defmacro.rs:103` ×1) waiting on REPL wiring that has
not arrived in ~47 sprints; user-facing "(Ring 3)"/"(Ring 4)" messages
(`ast_builder.rs:411-433, 1321-1338`) naming an axis retired S64.
**Cost**: small.
**Owner**: `/dev`(frontend).
**Done**: dead functions deleted (git history is the archive; re-derive from
`parse_import` etc. if the REPL need materialises); NYI messages say what to write
instead ("not yet supported; use `(fn [x] …)`"), no ring numbers.

### R7 — Reader/annotation leniency cells (suggestion grade)
**Evidence**: §2.7 — swallowed errors at `try_consume_annotation:1702` and
`read_qualified_tail` (`reader.rs:700-706/:737-742`); space-separated `: Name` accepted;
plus the S87 F5 dotted-loop mirror (`reader.rs:609-661`/`:709-750`) whose consolidation
would remove the second swallow site for free.
**Cost**: small.
**Owner**: `/qa` (rule whether `: Name` and `:foo/`-degradation are conformance cells or
tolerated leniency; spec §1.4.5/§2.4 arbitration may need the user) → `/dev`(frontend).
**Done**: each cell has either a located diagnostic + pin, or a recorded
tolerated-leniency ruling; `consume_dotted_module_path` exists once.

### Meta — restore the disposition trail for this context
The 04-23 and S87 frontend findings were routed to a consolidation backlog
(`audits/s87-findings.md` B12) that was never funded, and no decline rationale was ever
recorded on the assessments; three audits have now re-derived the same four findings at
full cost. Whatever S114 Phase 1 decides on R3/R4/R5, **append the decision to this
file** — the trail is the mechanism that makes the fourth audit cheaper than the third.

---

## 4. Disposition trail

*(Appended at S114 Phase 1 by /sprint + the user; not by /audit.)*
