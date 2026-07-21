# Operand-position & annotation-lexing enforcement matrices (S114 Track D)

> Subordinate topic doc, cited from `design/frontend/frontend.md` §4.3. Owned by
> `/design` (frontend). Authored S114 Phase 3 for SPRINT.md §Scope-D against the
> frontend-s113 audit §2.2/§2.7 defect families and the 0682 user ruling
> (2026-07-20). Anchors the two **standing** matrices `/qa` draws in
> `tests/plan/s114-test-plan.md` §5.1 (M1) + §5.2 (RA rows). Pre-implementation;
> `/dev`(frontend) implements the one-seam + reader change, `/review` checks
> against it.

The sibling doc `binder-head-reject.md` covers **binder heads** (declaration
names — the reference-vs-binder axis). THIS doc covers the two families the
audit named that are NOT binder heads:

1. **Operand-position ascription/trailing** (BD-A, audit §2.2) — `:Type body`
   ascription (spec §2.3.8) and trailing-form rejection, enforced at N of M
   expression positions today. The fix is ONE shared body-seam.
2. **Annotation/reference qualified-name lexing** (RA, audit §2.7 + the 0682
   ruling) — the dangling-qualifier reject (`:foo/`, `foo/`, `/bar`) and the
   bound-form-must-be-a-type-expression reject, decided at the **reader** and at
   `try_consume_annotation`.

Both are the *coverage-by-definition-variants* class (`tests/CLAUDE.md`): each
expression-position parser grew its own subset of the checks because no
`variant × {bare, ascribed, trailing}` matrix ever forced ONE codepath. The
design's job is to name that ONE codepath so the matrix has a single fix
criterion.

---

## 1. BD-A — the operand-position one-seam (M1 anchor)

### 1.1 The problem — the enforcement matrix has holes

The crate invariant (crate `CLAUDE.md` §"`:Type` binds the FOLLOWING form":
*"route a new operand position through `build_one_expr_at` — a raw `build_expr`
there silently drops annotation support"*) and spec §2.3.8 (*"an annotation MAY
appear in every expression position … an `if` / `fn` / `let` body"*) are
enforced at nine positions and **wrong** at four. The four unrouted sites
(audit §2.2, verified in source), each producing a spec-legal-but-rejected face:

| # | Site | `ast_builder.rs` | Wrong-reject face (BD-A1) | Trailing-drop face (BD-A2) |
|---|---|---|---|---|
| 1 | `build_let` **body** | `:1566-1571` — hard `children.len() != 3` + raw `build_expr(&children[2])` | `(let [x 1] :Int x)` → "let requires bindings and body" | — (arity-locked, so no silent drop; a trailing form hits the `!= 3` arm) |
| 2 | `build_impl_method` body | `:1340-1345` — `< 4` check + raw `build_expr(&children[3])`, `children[4..]` ignored | `(impl … (defn show [x] :Str …))` → "annotation missing expression" | `(defn name [p] body junk)` inside `impl` silently drops `junk` |
| 3 | `build_method_sig` default body | `:1126-1133` — raw `build_expr(&children[ret_pos+1])`, rest ignored | `(show [x] Str :Str "s")` → same error | `(show [x] Str body junk)` silently drops `junk` |
| 4 | `build_trace` operand | `:1518-1524` — hard arity 2 + raw `build_expr(&children[1])` | `(trace :Int x)` → arity error | `(trace x y)` → arity error (no silent drop) |

The **six RED cells** the /qa plan pins (`s114-test-plan.md` §5.1 M1): BD-A1 at
sites 1–4 (four ascription faces) + BD-A2 at sites 2–3 (two trailing-drop
faces). Sites 1 and 4 are arity-locked so their trailing face is an arity error,
not a silent drop — but they still adopt the seam so the drop face is
*structurally* impossible, not incidentally caught.

### 1.2 The seam — ONE `build_body_to_end` (Principle 7, Principle 18)

The nine correct positions already share `build_one_expr_at` (the
annotation-pairing primitive, `:1922`). The four wrong positions each want the
SAME two guarantees `build_one_expr_at` gives plus a **consumed-to-end** trailing
check. Single-source both into ONE helper every single-body operand position
calls:

```
/// Build the single trailing body-expression at `children[pos..]`, routing it
/// through the annotation-pairing primitive (so `:Type body` ascription works —
/// spec §2.3.8) and rejecting any form left after it (so `(form … body junk)`
/// is a LOCATED error, not a silent drop). The ONE seam for every single-body
/// operand position: let-body, impl-method body, trait-default body, trace
/// operand. Mirrors the tail-consumption discipline `parse_defn` already has.
fn build_body_to_end(children: &[Sexp], pos: usize, ctx: &str)
    -> Result<Expr, CranelispError>
{
    let (expr, consumed) = build_one_expr_at(children, pos)?;
    if pos + consumed != children.len() {
        return Err(parse_err(
            &format!("{ctx}: unexpected trailing form after body"),
            children[pos + consumed].span(),
        ));
    }
    Ok(expr)
}
```

Per-site rewiring (each is a one-to-three-line edit):

- **`build_let`**: relax the `!= 3` gate to `< 3` (a genuinely missing body),
  then `let body = build_body_to_end(children, 2, "let body")?;`. `[bindings]`
  stays at `children[1]`; the body starts at `children[2]` and consumes to end,
  so `(let [x 1] :Int x)` parses and `(let [x 1] a b)` rejects `b` located.
- **`build_impl_method`**: replace `build_expr(&children[3])` with
  `build_body_to_end(children, 3, "impl method body")?`. Closes BD-A1 **and**
  the BD-A2 `children[4..]` drop in one edit.
- **`build_method_sig`** default body: replace the `has_default_body` arm's
  `build_expr(&children[ret_pos + 1])` with
  `build_body_to_end(children, ret_pos + 1, "trait default method body")?`.
- **`build_trace`**: drop the `children.len() != 2` gate; call
  `build_body_to_end(children, 1, "trace")?`. `(trace :Int x)` now parses;
  `(trace x y)` rejects `y` as a trailing form (a clearer message than the old
  arity error).

**Structural acceptance (the M1 grep, /review):** no expression-position parser
calls raw `build_expr` for its *body* or hand-rolls a tail check — every
single-body position routes through `build_one_expr_at` (multi-operand
positions: `build_args_with_annotations`) or `build_body_to_end`. A fix that
greens the six pinned cells but leaves any M1 row un-routed does NOT close the
class. `parse_defn`/`build_defn_variant` already satisfy the criterion via their
own routed tail; they may adopt `build_body_to_end` for uniformity but need not
(not a defect there). This closes the audit §2.4 **divergent** facet ("parse a
defn-shaped tail exists three ways") for the ascription+trailing axes — the two
that were drift, not spec-narrowing (impl methods legitimately narrow to
single-arity/no-docstring per spec §7.3, and that narrowing stays).

## 2. deftype-ctor trailing-form completion (the pre-existing RED)

`build_constructor_def` (`:685`) rejects a trailing *non-bracket* non-docstring
form (the `other =>` arm, S107) but only inspects `children[next]` — a form
AFTER a valid field bracket is silently dropped:
`(deftype Box (Box [:Int n] extra))` drops `extra` and yields a one-field
`Box`. Guard: `tests/spec_05_definitions.rs::
deftype_ctor_trailing_form_after_field_bracket_rejected_neg` (RED,
crate `CLAUDE.md` §Known open defects). Fix shape: in the `Sexp::Bracket(..)`
arm that consumes the field list, after `build_field_list(&children[next])`,
require `next + 1 == children.len()`; else reject `children[next + 1]` located,
naming the fix (mirror the `other =>` arm's message shape and `parse_defn`'s
trailing reject). This is the constructor-position sibling of BD-A2 (the same
"a valid body/bracket followed by junk is silently dropped" class); it does not
use `build_body_to_end` (a ctor tail is a bracket, not an expression) but shares
the discipline. `/qa`'s M2 deftype rows already carry the case-arm cells (which
LANDED S113 W3, §3); this is the trailing axis of the same parser.

## 3. RA — annotation/reference qualified-name lexing (the 0682 ruling)

User ruling 2026-07-20 (SPRINT §Notes; scribed spec §1.4.5/§2.4/§8.5.1 `[S114]`):
`:` is a `^`-style reader macro — whitespace between `:` and its form ALLOWED
(`: Int` ≡ `:Int`); the bound form MUST be a type expression; **`:foo/` ERRORS;
bare `foo/` ERRORS anywhere; `/bar` (empty module half) ERRORS; bare `/`
(division) stands** (Principle 16, amended bullet — 0684).

### 3.1 Space tolerance is already the sanctioned mechanism (RA-P1/P2)

The reader emits a **bare `:` token** for the spaced/compound annotation
(`read_colon_prefix` `:409-419`: `:(...)` and bare `:`), and
`try_consume_annotation` (`:1842`) pairs it with the following form via
`build_type_expr` (`:1854-1861`). `: Int` therefore reads as `:` then `Int`, and
the bare-`:` arm builds `Int` as the annotation — space tolerance works TODAY
through the sanctioned bare-colon pairing path. RA-P1/P2 confirm it; no
mechanism change, only pins. The `build_one_expr_at` + `try_consume_annotation`
single-seam (crate `CLAUDE.md` §`:Type`) is the sanctioned space-tolerant path
per this ruling — recorded so no future change re-routes space handling through
a second spelling.

### 3.2 Where the dangling-qualifier reject lives — the READER, single-sourced

The both-halves-non-empty rule is a **lexical** property (whether a `/` has a
non-empty name on each side), decided where the token is formed. Today it is
enforced asymmetrically and swallowed in the annotation path:

| Written | Path | Today |
|---|---|---|
| `foo/bar` | `read_symbol_or_keyword` → `read_qualified_symbol` → `read_local_name` | OK (both halves) |
| `foo/` (value) | same → `read_local_name` peeks nothing valid → `Err("expected local name after '/'")` (`:788`, propagated by `?`) | **already errors** |
| `:foo/` (annotation) | `read_colon_prefix` → `read_qualified_tail` → sees `/`, `read_local_name` fails → **returns `first_part`, `/` consumed** (`:700-706`) | **SWALLOWS** → degrades to `:foo` |
| `:a.b/` (annotation) | `read_qualified_tail` dotted branch → found_slash, `read_local_name` fails → **returns `module`** (`:737-742`) | **SWALLOWS** → degrades to `:a.b` |
| `/bar` (any) | `read_operator` reads lone `/`, next byte `b` (symbol-start) → returns operator symbol `/`, then `bar` as a separate token | **not detected** (reads as `/` `bar`) |
| `/` (division) | `read_operator` → operator symbol `/`, boundary after | LEGAL (RA-N4 fence) |

**Design — three edits at the reader, no ast_builder reject for the qualifier
axis:**

1. **Consolidate the dotted-module loop into ONE fallible helper (S87 F5).** The
   dotted-module-path lexer appears twice, structurally identical:
   `read_symbol_or_keyword:609-661` and `read_qualified_tail:709-750`. Extract
   `consume_dotted_module_path(r, first_part) -> Result<Option<String>, CranelispError>`
   (returns `Ok(Some(path))` when a `/`-terminated dotted module was consumed,
   `Ok(None)` when no `/` terminated the run — the caller keeps the bare name,
   `Err` on a dangling qualifier). Both callers use it; the **second swallow
   site vanishes for free** (audit R7 "`consume_dotted_module_path` exists
   once"). Change `read_qualified_tail` to return
   `Result<String, CranelispError>` so its `/`-with-no-valid-local branch
   propagates a **located** error instead of returning `first_part` with `/`
   consumed. Its caller `read_colon_prefix` (`:404`) threads the `?`. This makes
   `:foo/` and `:a.b/` reject with the SAME diagnostic the value path already
   gives (RA-N1, RA-N2) — parity between annotation and value positions through
   one helper.

2. **`/bar` empty-module-half guard at `read_operator` (`:546`).** A lone `/`
   immediately followed (no whitespace boundary) by a name is a dangling
   qualifier with an EMPTY module half — the symmetric case the user confirmed
   (0686/0687). After `consume_operator_chars`, if the operator text is **exactly
   `"/"`** AND the next byte is `is_symbol_start`, reject located
   ("`/` here has no module name before it — a qualified name needs a non-empty
   module (`mod/name`); a bare `/` division must be separated (`(/ a b)`)").
   Keyed on `"/"` exactly (Principle 16 — only `/` is the qualifier char; `*foo`,
   `<foo`, `->` are untouched: `->` reads as operator text `->` ≠ `"/"`), and on
   symbol-adjacency (so `(/ 6 2)`, `(map / xs)`, `/` at EOF stay the division
   operator — RA-N4 fence). This is the ONE genuinely-new lexical reject; the
   others un-swallow existing paths.

3. **`read_local_name`'s existing `Err` (`:788`, `"expected local name after
   '/'"`) is retained** as the value-path dangling-local reject (RA-N3 value
   position). Edit 1 brings the annotation path to parity with it (same message,
   both positions).

   **S115 message-parity rider (0710, /dev(frontend), Minor).** The empty-LOCAL
   half message (`read_local_name`, `reader.rs:824` at HEAD — the `:788` reference
   above is pre-drift; verify at fix time) is terse and remedy-less
   (`"expected local name after '/'"`) compared to its **rich empty-MODULE-half
   sibling** at `read_operator` (`reader.rs:564` — "`/` here has no module name
   before it — a qualified name needs a non-empty module (`mod/name`); a bare `/`
   division must be separated (`(/ a b)`)"). Both are correctly located + rejected
   (spec §8.5.1); the finding (`/docs`, FIXME 0710) is purely that a newcomer who
   typed `map/` gets less help than one who typed `/bar`. **Fix: raise the
   `read_local_name` message to the empty-module sibling's shape** — name the
   dangling-qualifier shape and the remedy ("a qualified name needs a non-empty
   local (`mod/name`); drop the trailing `/`"). **Message text only, no semantic
   change**, no path change — the same `Err` at the same seam, richer wording.
   Coordinate the two phrasings with /spec §8.5.1 if they should share one
   template (0710 suggests it). This is the value/annotation-position dangling-
   local twin of the `/bar` empty-module reject; it is NOT the §5 binder-reject
   message (that is `binder-head-reject.md` §2.1/0711 — a different seam). Both
   ride the same S115 /dev(frontend) frontend-message wave (with the 0702 dotted
   widening) but are independent one-line edits.

**Why the reader, not ast_builder:** `/bar` and `foo/` never form a single
`module/name` string that reaches the ast_builder splitters (`type_ref_from_name`
et al.) — `/bar` tokenizes as two forms, `foo/` errors before composing — so the
downstream both-halves-non-empty guards *cannot* see them. The only site where
adjacency and emptiness are both known is tokenization. The splitters' guards
STAY as defense-in-depth for the one degenerate name that still legally reaches
them — bare `/` (the division operator as a value/name) — but their comment
"a degenerate `foo/` is legitimately passed through" is **superseded** (0684):
after this reject, `foo/`/`/bar` are rejected at the reader, so only `/` itself
reaches the splitters. Retiring that comment (crate `CLAUDE.md`:114 +
`ast_builder.rs:2082-2086`) is `/dev`(frontend)'s at RA-row time (carried in the
Phase-5 wave brief per SPRINT §Notes; the mirror-sentence half of 0684).

### 3.3 Bound-form-must-be-a-type-expression (RA-N5) — ast_builder

A bare `:` token is **only ever** an annotation introducer (crate `CLAUDE.md`
§`:Type`: never a `Var`; `build_expr` errors "annotation missing expression" on
a bare `:Type`). So its following form MUST parse as a type expression. Today
`try_consume_annotation`'s bare-`:` arm (`:1854-1861`) **swallows** a
`build_type_expr` failure and returns `None`, so the `:` falls through to
`Expr::Var { name: ":" }` → opaque downstream "unresolved symbol `:`" (audit §2.7
leniency cell). Design: make the bare-`:` arm's failure a **located error**
naming the fix — "the form bound by `:` must be a type expression; found
`{Sexp::format_flat}`" — rather than swallowing to a `Var`. This closes RA-N5
(`:3 x`, `: "s" x`) and the `try_consume_annotation:1702` swallow cell.

Scope fence: RA-N5 asserts only the **non-type-form** reject. The
0589-family cell (a lowercase name after `:` mints a `TypeVar` — `parse_annotation_name`
`:1903`) is a SEPARATE pinned family (already routed: qualified-lowercase →
`Named`; bare-lowercase → `TypeVar`), not touched here. A plain lowercase
`:foo x` stays a legal type-var annotation.

**RA-N4 non-negotiable:** `(/ 6 2)` → 3 must stay GREEN through every edit
above. The division fence is the acid test that the qualifier reject does not
over-reach (Principle 16).

## 4. Sequencing (Phase 4 input)

All of §1–§3 are **independent** of the S114 carrier work and of 0670:

- **BD-A one-seam (§1)** + **deftype-ctor trailing (§2)** + **RA reader/ast_builder
  (§3)** land in the /dev(frontend) Track-D wave — one change-set (they share
  `ast_builder.rs`/`reader.rs`; serialise, no cross-gate ordering). Flips: BD-A
  ×6, deftype-ctor-trailing ×1, RA-N1..N5, RA-P1/P2, plus the M1/M2 spot cells.
  `/spec`'s §1.4.5/§2.4/§8.5.1 scribe **precedes** the fix so `// spec:` anchors
  resolve (already DELIVERED, SPRINT §/spec).
- The **value-level binder reject re-landing** is the ONLY 0670-gated item and
  lives in `binder-head-reject.md` §3.4 (a different family — binders, not
  annotations) — F8 strict order: int fix → re-landing → cells.

## 5. Principles cited

- **Principle 7 (single source of truth)** — ONE `build_body_to_end` seam (§1);
  ONE `consume_dotted_module_path` (§3.2) collapsing the S87 F5 mirror.
- **Principle 18 (enforce invariants structurally)** — the trailing reject +
  ascription routing fire where the body is built; the dangling-qualifier reject
  fires where the token is formed (the only site adjacency is known).
- **Principle 16 (punctuation symbols are not special)** — the `/bar` guard keys
  on `"/"` exactly + symbol-adjacency; bare `/` division stays legal (RA-N4).
- **Principle 6 (complexity has a budget)** — the reject un-swallows existing
  paths (one genuinely-new lexical check); no speculative widening to other
  operator chars.

## 6. Cross-references

- `design/frontend/frontend.md` §4.3 — this doc named in the master.
- `design/frontend/binder-head-reject.md` §3.4 — the value-level binder reject
  re-landing (0670-gated), the sibling family.
- `tests/plan/s114-test-plan.md` §5.1 (M1) / §5.2 (RA) — the standing matrices
  this design anchors; §5.3 (0660 reserved rows).
- `crates/cranelisp-frontend/src/ast_builder.rs` :685 (`build_constructor_def`),
  :1067 (`build_method_sig`), :1328 (`build_impl_method`), :1495 (`build_trace`),
  :1561 (`build_let`), :1842 (`try_consume_annotation`), :1922 (`build_one_expr_at`).
- `crates/cranelisp-frontend/src/reader.rs` :388 (`read_colon_prefix`), :546
  (`read_operator`), :585 (`read_symbol_or_keyword`), :696 (`read_qualified_tail`),
  :756 (`read_local_name`) — the reader sites.
- `audits/frontend-s113.md` §2.2 (BD-A evidence), §2.7 (RA leniency cells), R7.
