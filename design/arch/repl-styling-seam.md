# REPL Styling Seam — one formatter, one styling spec (E4)

**Status: DESIGN (S108 Increment 3, Phase 2) — IMPLEMENTED Wave D** (the seam is
live: `src/styled.rs` + `styled::render`; §5's `pretty_print_str` row amended at Inc3
close to the as-landed selector shape). The user-ratified
north star (2026-07-12): **ONE formatter conforming to ONE styling spec for all
token-styled REPL output** — values, introspection (`/sig`/`/info`/bare symbol), code
(`/sexp`/`/source`/`/expand`), `/search` rows, errors/warnings. `/repl` scribes the
normative styling spec from §3's role vocabulary; **the USER reviews that spec before
Wave-D implementation starts** (hard gate, `sprints/SPRINT.md` §Increment 3). `/design`
(int) elaborates interiors; `/dev` (src/, int) implements. Subsumes FIXME 0561's
mechanism side (the dim-vs-italic ratification itself is `/repl`+user).

**Explicit scope boundary (user, 2026-07-12):** the pure symbol lists — `/list`,
`/imports`, `/exports` name bodies — are a separate uniform-layout + line-break concern
(`append_name_category`, §3.3 L0–L4) and are NOT restructured here. Their **category
headers** do carry the `header` role (§3), applied through the same core; the name
bodies stay default-styled layout. `/search` rows DO carry token roles and are in scope.

---

## 1. The problem — as-built inventory

Two distinct defects, one seam:

**(a) Fragmented styling application.** Style roles today are applied at four unrelated
sites: `src/pretty.rs` (TWO code highlighters — the `pp`/`style_atom` Sexp-tree printer
and the `style_tokens` byte-scanner fallback inside `pretty_print_str`), `src/main.rs`
L408-415 (the `/search` lifecycle note, hand-styled Italic), `src/agent/render.rs`
(agent markdown → `pretty_print_str` + `agent_prose`), and `src/style.rs` (the agent
gutter). Each restates role knowledge (`;`-comment ⇒ italic, `:…` ⇒ cyan, head ⇒ bold)
independently — the FIXME 0561 divergence (spec §10.3 dim vs impl italic) is exactly
this class.

**(b) The semantic formatters discard role knowledge, and most spec'd styling is
consequently unimplemented.** The formatters that KNOW element roles at construction —
`format_result_value`/`format_adt_value`/`format_scheme_display`/`format_ctor_display`
(`src/display.rs`), `format_def_entry`/`format_overloaded_variants`/
`format_related_section(s)`/`format_type_display`/`format_trait_display`/
`format_eval_result`/`render_search_row`/`handle_doc` (`src/repl.rs`) — emit flat
`String`s with zero SGR. The result: **§10.3's roles for result lines, introspection
lines, search rows, prompts, banners, errors, and warnings are spec'd but NOT
implemented** (verified: `styled(`/`Style::` appear only in `style.rs`, `pretty.rs`,
`main.rs` L413, `agent/render.rs`). The only styled surfaces today are `/sexp`,
`/source`, agent-rendered code, and one lifecycle note. `/expand` renders through a
THIRD unstyled code renderer (`format_sexp`, repl.rs).

**(c) The string-reparse anti-pattern.** Where styling IS applied to formatter output
(`pretty_print_str`), the pipeline is: semantic formatter renders a `String` → the
styler **re-parses that string** (`try_parse_and_format`) → a round-trip check fails on
legitimate output (`:primitives/Int` does not survive the reader) → fall back to the
`style_tokens` byte-scanner. Two highlighters exist *because* the reparse is lossy.
Re-discovering by parsing what the producer knew at construction is the architectural
defect (Principle 7 — the role fact has two homes; Principle 21 — the function between
formatter and styler was never named, so it grew a parser in the crack).

**Spec fragmentation** mirrors the code: §1/§1.5 (values), §4.1 (introspection), §3.11
(code layout; colour hand-waved), §10.3 (REPL-output roles), §10.4 (styled universal
output) — and the code-highlighter token roles are unspec'd entirely (impl-only, in two
copies). `class=presentation-drift`.

## 2. Actors and the functions between them (Principle 21)

Laying the actors bare before choosing the mechanism:

| # | Actor (producer) | Emits (function → display elements) | Today |
|---|---|---|---|
| P1 | Result-value renderer — `format_eval_result` → `format_result_value`/`format_adt_value` (display.rs) | `:Type value` lines: type-annotation, int/float/bool literal, string literal, ctor dot-name, `<closure>`, vec brackets | plain String |
| P2 | Introspection renderer — `format_def_entry` + `format_scheme_display`/`format_ctor_display`/`format_overloaded_variants`/`format_macro_display`/`format_special_form_display`/`format_type_display`/`format_trait_display`/`format_builtin_type_display`/`format_related_section(s)` | `:Type name ; class - doc` primary lines + `; match:`/`; defn:`/`; impl:` section lines: type-annotation, FQ name (module-prefix + symbol), metadata comments | plain String |
| P3 | `/doc` renderer — `handle_doc` | `name: "doc"` lines | plain String |
| P4 | Code printer — `pp` (pretty.rs) for `/sexp`, `/source`-fallback, agent code blocks; `format_sexp` for `/expand` | code: head-of-apply, literals, strings, type-annotations, source comments, brackets, symbols | `pp` styles inline (one of the two highlighters); `format_sexp` plain |
| P5 | Verbatim-source styler — `pretty_print_str` (+ `style_tokens`) for `/source` stored text, agent ```lisp blocks | same element set as P4 but over caller-supplied text | string-reparse + byte-scanner (the second highlighter) |
| P6 | `/search` row renderer — `render_search_row` | type-annotation, name, module path, `(import …)` code snippet, `; doc:` excerpt, in-scope marker | plain String |
| P7 | Error/warning presenter — `main.rs` `Error: {e}`, `format_eval_result` `; warning:` lines, `runtime error:` lines | error keyword+detail, warning keyword+detail | plain String |
| P8 | REPL-frame emitters — prompt (`prompt_string`), banner (`print_banner`), watcher/lifecycle notes, cascade/broken-status lines | prompt, banner, metadata notes | plain (except main.rs L413) |
| P9 | Agent prose frame — `agent_prose` (style.rs) | `▌` gutter | already single-sourced; UNCHANGED |

**Consumers**: the terminal (stdout; colour-gated by `style::is_color_enabled`), and
the **agent membrane** (`agent/pull.rs` via `strip_ansi` — must keep receiving clean
plain text). The e2e harness is a non-TTY consumer: **colour-off output must stay
byte-identical through this migration** (the standing golden corpus is the guard).

The named function between producers and the terminal — today missing, hence the
fragmentation — is: *"here is a line as (element-role, text) spans; render it."* That
function is the seam.

## 3. The element → style role vocabulary

The normative contract `/repl` scribes (and the user reviews). One role per element,
defined once. SGR assignments marked ⚑ are the user-ratified table
(`sprints/SPRINT.md` §E4); the dim/italic split resolves FIXME 0561 at scribe time.

| Role | Elements it covers | Style |
|---|---|---|
| `TypeAnnotation` | `:Type`, `:module/Type`, `:(Fn [..] ..)` — in result lines, introspection lines, search rows, and code | cyan ⚑ (see §7 for the parked prefix-dim enhancement) |
| `Head` | first symbol of an apply form (code only; includes bolded delimiters when a form is in head position) | bold ⚑ |
| `LitNumBool` | int / float / bool literals — code AND value display | yellow ⚑ |
| `LitStr` | string literals — code AND value display (§10.2: SGR never inside the string *content*; the span wraps the quoted text as one unit) | green ⚑ |
| `SourceComment` | `;` comments in SOURCE code (`/source`, `/sexp`, agent code blocks) | italic ⚑ |
| `ReplMetadata` | REPL structured-metadata `;` lines/suffixes: `; defn`/`; deftype`/…, `; match:`/`; defn:`/`; impl:` sections, `; doc:`, `; warning:` prefix-comment, lifecycle notes (`; search index complete.`), broken-status/provenance lines | dim vs italic = the FIXME 0561 ratification (recommended per 0561: this role dim OR italic as the user rules; distinct from `SourceComment` either way) |
| `ModulePrefix` | the `module/` prefix inside an FQ **name** (`primitives/` in `primitives/vec-len`, the `in collections.vec` module column of search rows) | dim ⚑ — NEW role |
| `Name` | the symbol part of names; ctor dot-names; default body text | default (unstyled) |
| `ErrorKeyword` / `ErrorDetail` | `Error:` / message body; `runtime error:` lines | bold-red / red (§10.3) |
| `WarnKeyword` / `WarnDetail` | `Warning:`-class keyword / body | bold-yellow / yellow (§10.3) |
| `Header` | category headers (`Fns:`, `Types:`, `Special forms:`) — the one styling role the layout-family lists carry | bold (§10.3) |
| `Prompt` / `Banner` | prompt line, startup banner | dim (§10.3) |
| `AgentGutter` | `▌` prose gutter | bright magenta — existing, unchanged |
| `Plain` | whitespace, punctuation, layout padding, anything unlisted | none |

Completeness rule for the spec scribe: **every byte of token-styled output is covered
by exactly one role above**; a surface needing a role not in this table is a spec
change, not an impl choice. (`agent>` echo prompt keeps its existing §10.3 composite —
dim + bright-magenta token — expressed as `Prompt` + `AgentGutter`-family spans.)

## 4. The mechanism — role-span lines, one renderer

**The carrier is a role-span sequence, not a re-parsed string.** New int-side module
(Layer 1.5, between `style.rs` and all producers; suggested `src/styled.rs`):

```rust
pub(crate) enum Role { TypeAnnotation, Head, LitNumBool, LitStr, SourceComment,
                       ReplMetadata, ModulePrefix, Name, ErrorKeyword, ErrorDetail,
                       WarnKeyword, WarnDetail, Header, Prompt, Banner, Plain, … }

pub(crate) struct StyledDoc(Vec<(Role, String)>);   // newlines are Plain spans

fn role_style(role: Role) -> Option<Style>;          // THE styling spec in code — one table
pub(crate) fn render(doc: &StyledDoc) -> String;     // the ONLY site calling style::styled()
```

- `role_style` is the single code manifestation of `/repl`'s styling spec — the table
  in §3 maps 1:1 onto it. A role is defined once, applied once; drift is structurally
  impossible (Principle 18: the wrong thing — a second `styled()` call site in a
  formatter — is findable by a one-line grep gate, and `/review` watches for it).
- `render` degrades exactly as `styled` does today: colour-off ⇒ the concatenated
  plain text. **Invariant: `render(colour-off)` is byte-identical to the doc's text
  content** — this is what keeps the golden corpus and the agent membrane unchanged.

**Producers emit roles at construction — never by re-parsing their own output.**

- **Semantic producers** (P1–P3, P6–P8): `format_result_value`, `format_def_entry` and
  satellites, `render_search_row`, error/warning rendering, prompt/banner keep their
  semantic jobs but build `StyledDoc` instead of `String`. They already hold the
  structured parts (`Type`, `FQSymbol`, `ModuleFullPath` + `Symbol`, docstring), so
  `ModulePrefix`/`Name`/`TypeAnnotation`/`ReplMetadata` spans fall out directly — the
  FQ-prefix-dim role needs **no** parsing anywhere.
- **The code printer** (P4): `pp` keeps its layout algorithm (§3.11 alignment,
  FLAT_THRESHOLD, pair forms) but emits spans via a single **role-assignment walk**
  over the `Sexp` tree (head position, atom kind, `:`-symbol, comment node) instead of
  calling `styled()` inline. So yes — **the code core operates on the Sexp tree**; the
  tree is where code roles are structural.
- **The verbatim-source styler** (P5): replaces `style_tokens`. To
  style caller-supplied source WITHOUT re-laying it out: parse the text with the
  reader (which attaches byte `Span`s to every node), run the SAME role-assignment
  walk, and emit role spans **over the original byte ranges** — gaps between spans are
  `Plain`, so the user's own whitespace/layout is preserved exactly. On parse failure:
  emit the whole text as `Plain` (never a wrong-guess scan). This deletes the
  byte-scanner; the two highlighters collapse into **one role
  walk with two emitters** (computed layout vs original bytes). *(As landed:
  `pretty_print_str`'s round-trip check is RETAINED as the verbatim-vs-relayout
  selector between the two emitters — see the §5 disposition row; re-laying-out
  SOURCE is legitimate, unlike the deleted reparse-of-formatter-OUTPUT.)*

**Non-code surfaces do NOT map onto the Sexp tree.** A `:Type value` line or a search
row is session data, not a parseable form (`<closure>`, `; doc:` excerpts, and
`:primitives/Int` all fail the reader) — forcing them through Sexp would recreate the
round-trip problem this design deletes. The tree is *a producer* of roles (for code);
the role-span line is *the carrier* for everything.

**The shared envelope.** The Inc1-D2-class drift between `format_eval_result` (value
envelope) and `format_def_entry` (introspection envelope) — two renderers of
`:Type <subject> [; metadata]` — is closed one level up: one envelope constructor
(`envelope(type_ann, subject_spans, metadata) -> StyledDoc`) that both route through,
so the `:`-prefix/spacing/metadata grammar is single-sourced while the two producers
keep their distinct subject semantics (value vs definition — a legitimate difference,
not drift).

## 5. What collapses into what

| Current | Disposition |
|---|---|
| `pp`/`style_atom`/`pp_symbol` inline styling (pretty.rs) | `pp` retained for layout; styling moves to the shared role walk; `style_atom` deleted |
| `style_tokens` + `consume_type_annotation`/`consume_string_literal`/`consume_number`/`consume_symbol` (pretty.rs) | DELETED — replaced by the span-over-source emitter (§4 P5) |
| `pretty_print_str` round-trip/fallback machinery | **As landed (E4, Wave D — amends this row's original "no reparse-then-reformat" wording):** the round-trip check is RETAINED as the **verbatim-vs-relayout SELECTOR** for `/source`/agent code — a code line that round-trips flat through the reader is re-laid-out via `pp` (the locked golden `tests/display_exact.rs::source_rotate_aligned_matches_sexp_byte_exact` requires `/source` ≡ `/sexp` re-layout), otherwise the verbatim-source styler emits role spans over the original bytes. What was DELETED is only the `style_tokens` byte-scanner the round-trip used to fall back to. This is legitimate: re-laying-out actual SOURCE text is what `/sexp` already does; the condemned anti-pattern — re-parsing value/introspection **formatter OUTPUT** to re-discover roles — is fully gone (producers emit roles at construction) |
| `format_sexp` as `/expand`'s renderer (repl.rs) | `/expand` routes through the code printer (P4); `format_sexp` remains only if a plain-text (non-display) consumer needs it |
| `format_value`/`format_result_value`/`format_adt_value`/`format_scheme_display`/`format_ctor_display` (display.rs) | retained as semantic producers; return/emit `StyledDoc` spans; zero SGR knowledge |
| `format_def_entry`/`format_overloaded_variants`/`format_related_section(s)`/`format_type_display`/`format_trait_display`/`format_eval_result`/`render_search_row`/`handle_doc` (repl.rs) | same — producers over the shared envelope + section span builders |
| `main.rs` hand-styled lifecycle note (L408-415) | a `ReplMetadata` span through `render` |
| `main.rs` `Error: {e}` / `format_eval_result` `; warning:` lines | `ErrorKeyword`+`ErrorDetail` / `ReplMetadata`+`Warn*` spans through `render` |
| `agent/render.rs` code-block path | routes to the verbatim-source styler; `strip_ansi` membrane unchanged |
| `agent_prose`, `append_name_category` layout, `/list`-family name bodies | UNCHANGED (out of scope; headers gain the `Header` role via `render`) |

## 6. Migration shape (Wave D; sequenced last in the increment)

1. **Land the seam**: `Role`/`StyledDoc`/`render`/`role_style` + unit pins — per-role
   SGR bytes pinned ONCE (colour forced ON via the existing `style::test_support`
   seam), and `render(colour-off) == text content`.
2. **Convert the code printer**: `pp` → role walk; `/sexp`/`/source`/`/expand`/agent
   blocks through it; verbatim-source styler replaces `pretty_print_str` internals;
   DELETE `style_tokens` + helpers. Colour-off bytes unchanged (layout untouched).
3. **Convert semantic producers** (this is where §10.3 becomes TRUE for values,
   introspection, search, errors, prompt/banner): producers emit spans; callers
   (`CompilerSession::pretty_print`, `dispatch_command` boundary, main.rs write sites)
   render at the boundary. Colour-off bytes byte-identical to today (golden guard);
   colour-on per-surface byte-identity tests per output kind (the §3.11 discipline
   extended to styling — `/qa` plans, `/testing` authors).
4. Close FIXME 0561 in the same wave (`/repl` ratifies; `role_style` + spec §10.3 +
   `main.rs` comment reconcile to the ruling).

Nothing lands ahead of the user's sign-off on `/repl`'s scribed spec (the Increment-3
hard gate).

## 7. Boundary confirmations

- **No `cranelisp-types` change, no public-API change, no cache impact** for the base
  design. Everything above is int-side (`src/`); `render_type` (the FIXME-0420 single
  type→string walk in `cranelisp-types`) is consumed unchanged — a rendered type is
  one `TypeAnnotation` span.
- **One precisely-scoped contingency**: the user's PARKED enhancement — dim the
  `module/` prefix INSIDE `:module/Type` annotations — requires sub-spans within the
  rendered type. If ratified, the honest seam is a span-emitting variant in
  `cranelisp-types`: `render_type_spans(ty, …) -> Vec<(TypeToken, String)>` with
  `TypeToken ∈ {ModulePrefix, TypeName, Var, Punct}`, and `render_type` reimplemented
  as its concatenation (Principle 7 — still one walk). Additive `pub fn`, pure, no
  serde/cache impact; requires the types `public-api.txt` bump + `/arch` approval in
  that change-set. **Do NOT implement the alternative** (an int-side lexical pass over
  the rendered type string) — that re-introduces exactly the string-reparse defect
  this design deletes. Until ratified: whole-annotation cyan, no types edit.
- **Compatibility with `display-protocol.md`** (FIXME 0050, out of scope): the
  List/Seq surface-form renderer extends WHAT `display.rs` produces; this seam changes
  HOW producers carry roles. Orthogonal — when 0050 lands, its renderer is another
  span producer.
- **Non-TTY/agent invariants**: colour-off output byte-identical (goldens); the agent
  model feed stays plain via the unchanged `strip_ansi` membrane.

## Next skills

- `/repl` — scribe the ONE styling spec from §3 (consolidating §1/§1.5/§3.11/§4.1/
  §10.3/§10.4; resolve 0561); bring to the USER for the Wave-D gate.
- `/qa` — PLAN rows: per-role SGR pins, per-surface colour-on byte-identity, colour-off
  golden equivalence.
- `/design` (int) — interior elaboration (module placement, producer signatures) in
  `design/int/terminal-styling.md` (this doc supersedes its two-layer model with the
  three-layer producer/role/renderer model; update or successor).
- `/dev` (src/, int) — Wave D implementation after the user gate.
