# Terminal Styling and Pretty-Printer — int Design

Owner: `design` (int). This document states how the binary styles REPL
output and lays out code.

- **Required behaviour** is `repl/spec/10-terminal-styling.md`. The role table
  of its §10.3 is the one styling authority.
- **The styling seam** (actors, role vocabulary, mechanism) is `/arch`'s
  `design/arch/repl-styling-seam.md`. This document designs the interior
  below it.
- **Code layout**, including the aligned `let`/`match` pair layout, is
  normative in `repl/spec/03-slash-commands.md` §3.11.

## 1. Layers and the one styling authority

| Module | Responsibility |
|---|---|
| `src/style.rs` | The `Style` palette and the `styled` SGR primitive; the process-wide colour decision (§2); `strip_ansi`; the shared `error_line` and `repl_metadata_line` builders; the `agent_prose` gutter. |
| `src/styled.rs` | `Role`, `StyledDoc` (role-tagged spans), `role_style` (the §10.3 table in code) and `render`, the only caller of `style::styled` for REPL output. |
| `src/pretty.rs` | Code layout, emitting role spans (§3). It calls no styler. |

- **One table, applied once.** Every token-styled line is a `StyledDoc` built
  at construction and rendered through `styled::render`. With colour off,
  `render` yields the concatenated plain text byte-identically.
- **The one exception** is the agent's markdown formatter in
  `src/agent/render.rs`, which styles inline emphasis through `style::styled`
  under the same colour decision (`design/int/agent.md` §14.6).
- A second `style::styled` call in any formatter is a duplicate of the table
  and a defect. A grep for `style::styled` outside these sites is the review
  check.

### 1.1 Producer rules

- **Roles come from construction.** A producer emits role spans from the
  structured parts it already holds and never re-parses its own rendered
  output to rediscover them. Re-laying out genuine source text (`/source`,
  agent code fences) is legitimate; routing formatter output through the
  reader is not.
- **Code producers** (`/sexp`, `/source`, `/expand`, agent code blocks) assign
  roles in one walk over the `Sexp` tree by node kind and position. Two
  emitters share that walk: computed layout (`pp`) and spans over the original
  bytes (§3.1).
- **Semantic producers** (result values, introspection lines, `/search` rows,
  `/doc`, errors, warnings, prompt and banner) build spans directly from
  `Type`, `FQSymbol` and docstring parts. They do not map onto the `Sexp` tree:
  a `:Type value` line is session data, not a parseable form.
- **Shared line builders** are single-sourced: `style::error_line`,
  `style::repl_metadata_line`, `push_warning_line` (`src/repl/format.rs`) and
  the display envelope (`src/display.rs`).
- **Serialisation is not display.** Persisted `.cl` source and
  introspection source fallbacks use `pretty::pretty_print_plain`, never
  the colour-gated `pretty_print`. A colour-on session would otherwise write
  SGR into stored source and break the next parse.

### 1.2 The `:Type` typed line — three builders, one role

The typed-line grammar is built at three sites, deliberately:

| Site | Subject |
|---|---|
| `envelope` (`src/display.rs`) | a caller-supplied value span — the `:Type value` result line |
| `format_scheme_display_doc` (`src/display.rs`) | a module-prefix and name suffix — the introspection line |
| `push_type_annotation` (`src/repl/format.rs`) | none — the bare annotation primitive |

All three push `Role::TypeAnnotation`, and only `render` maps a role to SGR, so
the annotation cannot render differently at different sites. The sites differ
only in their subject, which `design/arch/repl-styling-seam.md` §4 rules a
legitimate difference.

**Forward condition.** The `:{type}` prefix text is repeated at the first two
sites (and in the ADT arm of `format_result_value`). If sub-span styling
inside `:module/Type` is ever ratified (the parked enhancement in
`design/arch/repl-styling-seam.md` §7), route every typed-line construction
through `push_type_annotation` first, then extend that one primitive.

## 2. Colour decision

`style::init_color(no_color)` runs once in `main` and stores the decision in a
`OnceLock`. `detect_color` applies the priority order of
`repl/spec/10-terminal-styling.md` §10.1: the `--no-color` flag, then a
non-empty `NO_COLOR`, then whether stdout is a terminal. It is a pure function
and tests at that seam; integration tests force colour off with `--no-color`.
Output bound for a non-terminal consumer, such as the agent's model feed, is
cleaned with `style::strip_ansi`.

## 3. Pretty-printer layout (`src/pretty.rs`)

### 3.1 Entry points and emitters

- `pretty_print` and `pretty_print_doc` lay out a `Sexp` tree through `pp`.
- `pretty_print_plain` returns the same layout as plain text (§1.1).
- `pretty_print_str` and `pretty_print_str_doc` render caller-supplied source
  line by line:
  - a pure `;` line becomes a source comment;
  - a trailing comment is split off and re-attached as a source comment;
  - code that round-trips through the reader is re-laid out by `pp`;
  - any other code line keeps its original bytes, with role spans laid over it
    (`style_source_verbatim`). If the span walk cannot reproduce the input
    exactly, the whole line falls back to plain text, so a misaligned span can
    never corrupt output.

### 3.2 Roles by node kind

- The first element of a list is in head position and renders in the head
  role. A list in head position carries head-role brackets. Bracket vectors
  never place children in head position.
- A `:`-prefixed symbol is a type annotation. A list whose first child is such
  a symbol is an annotation list and renders wholly in the annotation role,
  overriding head and literal roles.
- Numbers and booleans, and strings, take their literal roles.

### 3.3 Width and indentation

- A form whose unstyled flat text is at most `FLAT_THRESHOLD` (40) characters
  renders on one line. Widths are always measured on unstyled text, so escape
  sequences never affect layout.
- A multi-line form headed by an entry of `SPECIAL_FORM_INDENT` (`defn`,
  `deftype`, `deftrait`, `impl`, `let`, `match`, `fn`, `if`, `do`,
  `defmacro`) indents its body two spaces; any other form aligns later
  arguments with the first argument.

### 3.4 Aligned `let`/`match` pair layout

Binding vectors of `let` and arm vectors of `match` are pair-structured. The
§3.11 rules P0–P5 make their layout byte-reproducible.

- **Structural recognition only.** `try_pp_pair_form` recognises the head and
  the vector on the `Sexp` tree, never by post-processing strings. Only `let`
  (its first bracket argument) and `match` (the bracket after the scrutinee)
  are recognised. This is a display contract and changes no semantics.
- **Forced multi-line (P0).** A recognised vector with two or more pairs
  renders multi-line even when the form would fit flat. The check runs in
  `pp_list` before the width test. Every enclosing form also refuses the flat
  path when a descendant is such a form (`subtree_contains_pair_form`), because
  the flat path renders children at column 0 and would misalign the nested
  pairs. Fewer than two pairs, or an odd element count (P5), falls back to the
  ordinary layout — never a crash or a dropped element.
- **Columns.** The spec's column values are `pp`'s existing absolute `indent`,
  so no new coordinate system exists. For `let`, the vector opens after
  `(let ` and body forms follow at `indent + 2`. For `match`, the vector stays
  on the head line after a flat-rendered scrutinee.
- **`pair_vector_layout`.** The left column is the widest left term's unstyled
  width. Each pair occupies its own line, with its right term starting one
  space past that width. The right term is laid out by `pp` with
  `indent = right_col`, so a nested multi-line value, including a nested
  recognised form, indents relative to its own column (P4). The closing `]`
  attaches to the last right term's final line.

The same printer backs `/sexp`, `/source` and agent code fences, so each
inherits this layout without extra wiring.
