# Trait/impl head parsing — the echo-the-head slot-1 shape (S112 b0)

**Status: current (authored S112 Phase 3, leg b0).** Design intent for the
narrow frontend change-set that admits the S111-settled echo-the-head `impl`
form. `/dev`(frontend) implements against this; `/review` checks against it.

Spec anchors: `spec/07-traits.md` §7.2 (deftrait head grammar), §7.3 / §7.3.4
(the `impl` form — slot 1 echoes the declared head, slot 2 names the target),
§7.3.5 (kind-matching — a **typecheck** seam, not frontend). Consumer contract:
`design/typecheck/hkt.md` §5.1/§5.4 (the Case-3 seam that reads what we parse).
Arch: SPRINT.md §Architecture-review adjustment **A1** (frontend is the missing
fourth surface) + the pinned types diff `TraitImpl.head_con_var: Option<Symbol>`
(`#[serde(default)]`, /arch-authored, we consume it).

Implementation site: `crates/cranelisp-frontend/src/ast_builder.rs` — `parse_impl`
(:941), `build_impl_target` (:997), `build_trait_head` (:834).

---

## 1. The problem the settled form creates for the parser

Today `parse_impl` reads slot 1 with `expect_symbol(&children[1])` (:954): slot 1
MUST be a bare symbol. The settled higher-kinded (HK) impl form echoes the
parenthesized `deftrait` head at slot 1:

```clojure
(impl (Functor f) (Functor Option)        ; slot 1 = (Functor f), slot 2 = (Functor Option)
  (defn fmap [g x] …))
```

so `children[1]` is a `Sexp::List`, and `expect_symbol` hard-errors. That hard
error is exactly what /arch's A1 identifies as the missing fourth surface: the
settled form does not parse at all today. b0 is the additive parse change plus
the pinned types carrier.

Two head shapes, one meaning bit (spec §7.1/§7.3, "Slot 1 is fixed, not
inferable"):

| Slot-1 shape | Trait kind | `head_con_var` |
|---|---|---|
| bare `Display` | conventional (kind `*`) | `None` |
| `(Functor f)` | higher-kinded (echoed head) | `Some("f")` |

## 2. What the parser does — and the hard line at what it does NOT

**Does (b0):**

1. Accept BOTH slot-1 shapes. Bare symbol → `head_con_var: None` (byte-identical
   to today's path). Parenthesized `(TraitName con_var)` → `head_con_var:
   Some(con_var)`.
2. Route the head trait-name through `trait_ref_from_name` in BOTH shapes — the
   §8.5 D-qual discipline (`crates/cranelisp-frontend/CLAUDE.md` §Qualified-name
   splitting; a whole slash-name stuffed into the bare-name slot re-roots under
   the current module). For the parenthesized shape the name is `head[0]`.
3. Leave slot 2 (`children[2]`) on the **existing** `build_impl_target` path,
   unchanged. For the HK case `(Functor Option)` parses to
   `TypeExpr::Applied(type_ref_from_name("Functor"), [Named("Option")])` — the
   pairing rides the existing `Applied` machinery. The parser assigns it no
   special meaning; it is a `TypeExpr` like any other.

**Does NOT (the hard line — Principle 24, "Resolve once"; one classifier):**

- **No kind classification.** The parser does not decide whether the trait is
  conventional or HK, does not read any trait declaration, does not look at slot
  2 to infer a kind. It records the *written shape bit* (`Some`/`None`) and stops.
- **No echo validation.** Whether slot 1's shape matches the trait's *declared*
  kind — an HK trait requiring `Some(_)`, a conventional trait requiring `None`
  — is checked at typecheck's §7.3.5 **Case-3 seam** (`register_trait_impl`,
  `hkt.md` §5.4 step 3), the single site that holds the trait declaration. A
  parser-side echo check would be a second classifier that could only ever agree
  with the kind-driven one (spec §7.3.5, "no separate classifier is needed or
  wanted").
- **No slot-2 interpretation.** `(Functor Option)`-as-pairing vs `(Option a)`-as-
  type-application is resolved by the trait's declared kind at the Case-3 seam,
  *before* slot 2 is inspected. The parser emits the same `Applied` shape for
  both and never disambiguates.

The parser's whole contribution is: parse the two slot-1 shapes into a
well-formed `(TraitRef, Option<Symbol>)`, and surface a located diagnostic for a
structurally malformed slot 1. Everything semantic is downstream.

## 3. One grammar for the head shape (Principle 7 — single source of truth)

Spec §7.3 states the slot-1 shape **is** the `deftrait` head shape ("echoes the
`deftrait` head as declared"). The frontend already parses the `deftrait` head in
`build_trait_head` (:834), which accepts exactly `Symbol` or a 2-element
`(TraitName var)` list with the same uppercase-head rule. If `parse_impl` grows
its own copy of that shape logic, the two can drift: a head shape `deftrait`
accepts but `impl` rejects (or vice versa) would make a legal echo unparseable —
the precise failure spec §7.3 forbids.

**Design intent:** extract the head *shape* parse into one shared helper that
both `build_trait_head` and `parse_impl` call. Suggested shape:

```
fn parse_trait_head_shape(sexp: &Sexp)
    -> Result<(&str /* head name, unsplit */, Option<(Symbol, Span)> /* con_var */), CranelispError>
```

- structural only: enforces `Symbol` OR 2-element `(UppercaseSymbol symbol)`;
  returns the raw head-name `&str` (unsplit) plus the con_var (if any);
- each **caller keeps its own name-resolution policy** — the divergence is
  intentional and must stay caller-side:
  - `build_trait_head` (deftrait): `TraitName::from(name)` (home-module name, no
    split) and folds the con_var into `type_params: vec![var]` + `hkt_param_name`;
  - `parse_impl` (impl): `trait_ref_from_name(name)` (§8.5 split for a qualified
    echoed head) and stores the con_var symbol into `head_con_var`.

So the **shape** grammar is single-sourced (they cannot drift on what a legal head
looks like) while the **name policy** stays where it belongs (deftrait resolves in
its home module; impl applies the D-qual splitter). This is the minimal cut that
honours both Principle 7 and the frontend's existing splitter discipline.

> If `/dev` finds the extraction disproportionate for a 2-shape grammar, the
> fallback is: `parse_impl` reuses `build_trait_head`'s exact structural checks
> verbatim, with a code comment pinning the two to spec §7.3's "same grammar"
> requirement. The shared helper is preferred (drift-proof); the verbatim mirror
> is acceptable only with the pin comment. A silent independent copy is not.

## 4. Malformed slot-1 diagnostics (self-documenting REPL principle)

Every rejection is a `parse_err` with the **span of the offending head**
(`children[1].span()` or the inner element's span), rendered via
`Sexp::format_flat()` never `{:?}` (the 0500 rendered-diagnostic class,
`crates/cranelisp-frontend/CLAUDE.md` §Debugging). Each names the fix.

| Written slot 1 | Reject reason (located) | Fix named |
|---|---|---|
| `(impl (Functor) …)` | HK impl head is missing its constructor variable | write `(Functor f)` |
| `(impl (Functor f g) …)` | too many elements in the impl head | a higher-kinded head is `(Trait con_var)` |
| `(impl () …)` | empty impl head | write the bare trait name, or `(Trait con_var)` |
| `(impl ((Functor f)) …)` | head element is not a symbol | trait name must be a bare symbol |
| `(impl (functor f) …)` | trait name must start with uppercase | reuse existing check (`build_trait_head`:848) |
| `(impl (Functor 3) …)` | constructor variable must be a symbol | write a name, e.g. `(Functor f)` |

Notes:

- The 1-element and 3+-element cases are the `children.len() != 2` arm of the
  shared shape parser (`build_trait_head`:840 today emits `"HKT trait head must
  be (TraitName var)"`). The impl-side message should read in impl terms
  ("impl head"), which is a caller-side wrapping of the shared shape error, OR a
  message the shared helper phrases neutrally ("trait head must be `(Trait
  con_var)`") that reads correctly for both callers. `/dev` picks; the neutral
  phrasing keeps it single-sourced.
- **con_var lowercase is NOT enforced at parse**, matching `build_trait_head`
  today (it `expect_symbol`s the var without a case check). Spec §7.2 grammar
  says `con_var = lowercase_symbol`, so an uppercase con_var is technically
  malformed — but that is a *pre-existing, shared* deftrait gap, not opened by
  this sprint. Keeping the two in lockstep (both non-enforcing) is correct for
  b0; tightening it (in the shared helper, for both forms at once) is a separate,
  spec-clear completeness item, not a language question. Flagged in §8.

## 5. Additive-green at b0 (the /arch staging requirement)

b0 must leave the old form and all existing typecheck behaviour byte-identical.
It does:

1. **Field is additive.** `TraitImpl.head_con_var: Option<Symbol>` with
   `#[serde(default)]` (/arch-pinned) — a fresh parse of a bare-head impl sets it
   to `None`, which equals the serde default, so no `CACHE_SCHEMA_VERSION` bump is
   needed *for b0* (the 20→21 bump is pinned to b2, for the `TraitDeclInfo.
   type_params` **meaning** change — /arch A4; unrelated to this field).
2. **Old path unchanged.** A bare-symbol slot 1 flows through the identical
   `trait_ref_from_name` + `build_impl_target` calls it does today, now with
   `head_con_var: None` attached. Same `TraitRef`, same `target`, same
   `type_constraints`, same methods.
3. **No new corpus, no consumer at b0.** No test or corpus file uses the
   parenthesized slot-1 form (verified: every existing HK impl is written
   `(impl Functor Option …)`, bare slot 1). typecheck ignores `head_con_var`
   until its Case-3 seam lands at b2. So b0 adds *acceptance* of a shape nothing
   yet writes, plus an unread field — pure additive surface, zero behaviour delta
   on the green suite.

**One caveat for `/dev` + `/testing` to confirm, not assume:** grep the suite for
any test that asserts the *old hard error* on a parenthesized slot-1 head (i.e.
feeds `(impl (Trait v) …)` and expects a parse failure). None was found in this
survey — but if one exists it inverts at b0 (the shape now parses) and must
migrate. This is the additive-green boundary to verify.

## 6. Sibling parse / round-trip sites — per-site verdict

The dispatch asks whether any other consumer parses or *re-emits* impl forms, and
whether the pretty-printer / `/source` / session-persistence round-trip the new
form faithfully. Enumeration (`parse_impl` / `TraitImpl` / `"impl"` consumers):

| Site | Crate | Role | Change needed? |
|---|---|---|---|
| `ast_builder.rs::parse_impl` | frontend | **the sole parse site** | **YES — b0, this doc** |
| `ast_builder.rs::build_impl_target` | frontend | slot-2 parse | **No** — slot 2 unchanged; `(Functor Option)` rides existing `Applied` |
| `lib.rs` re-exports | frontend | surface only | No |
| `src/pretty.rs::pp` | int | Sexp→styled-source (`/sexp`, `/source`, agent blocks) | **No — form-agnostic** (see below) |
| `src/save.rs::render_decl_sexp` | int | `user.cl` regeneration | **No — form-agnostic** (see below) |
| `src/repl/format_type.rs` (`format_trait_display`, `impls_for_type_in_view`, `; impl:` sections) | int | introspection **display** of *resolved* impls | Flag to /sprint (non-frontend; already in hkt.md §5.4 migration list) |
| typecheck `traits/*`, `program/*`, `checker.rs`, `builtins.rs` | typecheck | consume the parsed AST (leg b) | Owned by /design typecheck — not here |
| `src/{eval,worker,process_form,bootstrap,session_setup}.rs` | int | drive AST through pipeline | No parse/re-emit of impl syntax |

**Why pretty.rs and save.rs need no change — the load-bearing finding.** Both the
pretty-printer (`src/pretty.rs::pp`) and the session-persistence regenerator
(`src/save.rs::render_decl_sexp`) walk the **`Sexp` tree structurally** — they
render nested lists generically and are entirely **form-agnostic**. `"impl"`
appears in `pretty.rs`'s `SPECIAL_FORM_INDENT` list only to pick 2-space body
indentation; neither renderer pattern-matches the *internals* of an impl form.
The new `(impl (Functor f) (Functor Option) …)` is ordinary nested s-expressions,
so:

- `/sexp` and single-line `/source` (`pp`) render it as nested lists with the
  impl 2-space indent — faithful by construction;
- `user.cl` regeneration (`save.rs`) round-trips it: the **verbatim source-slice**
  path (`process_form::verbatim_source_slice`, the preferred path) re-emits the
  authored bytes exactly, and the structural `render_decl_sexp` fallback re-emits
  the nested lists faithfully. Either way the regenerated form re-parses through
  the same b0 `parse_impl`.

So round-trip fidelity is **inherited from the structural design**, not something
b0 must add. It is a *behaviour to verify with an e2e*, not a code change — see
§7. This is a genuine design strength worth stating: because these int-side
serializers never learned the impl grammar, they cannot fall out of sync with it.

**Flagged non-frontend site (to /sprint):** `src/repl/format_type.rs` renders the
*resolved* impl summary (`impl Trait for Type`, the `; impl:` sections) from the
resolved `ModuleEntry::TraitImpl`/view data, not the raw AST. Its output shifts
under the b2 kind-model change — `hkt.md` §5.4 already names the two affected e2e
(`repl_introspection::bare_user_trait_lookup_impl_section_lists_type_not_others`,
`impl_form_display_result_is_exactly_impl_trait_for_type`, message drift). This is
an int-display concern downstream of typecheck's model change, **not a frontend
parse concern**; I flag it so /sprint routes the display reconciliation to the int
surface at b2, but I do not design it here.

## 7. Testability notes (for /dev unit tests + /qa/​/testing e2e)

Unit tests (`ast_builder/tests.rs`), asserting on the parsed `TraitImpl` — all
pure, no session (Principle 5):

- bare slot 1 → `head_con_var == None`, `trait_name` unchanged (regression pin on
  the additive-green path);
- `(Functor f)` slot 1 → `head_con_var == Some("f")`, `trait_name.name == "Functor"`,
  `target` still the parsed slot-2 `Applied`;
- qualified echoed head `(fmt/Functor f)` → head name splits to
  `TraitRef{ module: Some("fmt"), name: "Functor" }` (D-qual discipline holds for
  the parenthesized shape too);
- each §4 malformed row → located `parse_err` (assert the span points at the
  head, and the message names the fix);
- **grammar-parity pin**: a head shape `build_trait_head` accepts, `parse_impl`
  accepts identically, and vice versa — the structural guard that the two do not
  drift (directly exercises the Principle-7 single-source intent).

E2e (design-only recommendation; /qa's plan, /testing authors): a **round-trip
guard** — enter/define an HK impl in the new form, `/source` (or restart from the
regenerated `user.cl`) it, and assert the re-emitted text re-parses to the same
`TraitImpl`. This is the durable proof of the §6 "form-agnostic serializers"
claim; it belongs to the b1/b2 corpus wave, not b0 (no new-form corpus exists at
b0).

## 8. Open questions (routed to /sprint; frontend does not rule)

None are language-normative *for the frontend parse* — the parser only records
the written shape — but two touch the seam and should be routed:

1. **Slot-1 con_var spelling match (→ /design typecheck / possibly user).** Spec
   §7.3 says slot 1 reproduces the head "verbatim as declared… the same
   constructor-variable spelling `(Functor f)`." The typecheck Case-3 design
   (`hkt.md` §5.4 step 3) validates only the *shape bit* (`Some` vs `None`), NOT
   the spelling — so `(impl (Functor g) …)` against `(deftrait (Functor f) …)`
   would pass echo-validation under the current design. The frontend is
   unaffected either way (it records whatever spelling is written into
   `head_con_var`, so the datum for a spelling check is *available*). Route to
   /sprint: is spelling-match enforcement intended? If yes, it lands at the
   typecheck seam reading `head_con_var`, not in the parser.

2. **con_var lowercase enforcement (→ /qa completeness, not user).** §4 keeps the
   parser non-enforcing, in lockstep with `build_trait_head`. Spec §7.2 is clear
   (`con_var = lowercase_symbol`), so this is a spec-settled completeness gap
   shared by both head parsers, not a normative question. If tightened, it lands
   once in the shared shape helper (covering deftrait and impl together). Noted
   for /qa's coverage matrix; out of scope for b0 unless /qa pulls it in.

## 9. Principles cited

- **Principle 7 (single source of truth)** — one head-shape grammar for
  `deftrait` and `impl` slot 1 (§3); the form-agnostic serializers that cannot
  drift from the grammar (§6).
- **Principle 24 (resolve once) / "one classifier"** — the parser records the
  shape bit and does no kind classification, echo validation, or slot-2
  interpretation; all of that is the single typecheck §7.3.5 Case-3 seam (§2).
- **Principle 5 (testability is structural)** — `parse_impl` stays a pure
  `&[Sexp]` → `TraitImpl` function, unit-testable with no session (§7).
- **Principle 6 (complexity has a budget)** — b0 adds one shape branch + one
  additive field; it does not add a parser-side kind model (§2).
