# REPL styling seam — one formatter, one styling authority

**Status: current contract, delivered.** All token-styled REPL output — values,
introspection, code, `/search` rows, errors, warnings, prompts and banners —
is built as role-tagged spans and styled at one render site. The normative role
table is `repl/spec/10-terminal-styling.md` §10.3; this document owns the
cross-surface mechanism. The interior (modules, producer signatures, colour
decision) is [terminal styling](../int/terminal-styling.md), and the working
rules for `src/` are the [source memory](../../src/CLAUDE.md#repl-display).

## 1. The defect class this seam removes

- **Styling applied at unrelated sites.** Each site restated role knowledge
  (comment ⇒ italic, `:…` ⇒ cyan, head ⇒ bold), so surfaces drifted apart.
- **Formatters discarded role knowledge.** Producers that knew each element's
  role at construction emitted plain strings, leaving most specified styling
  unimplemented.
- **Re-parsing formatter output to rediscover roles.** Styling a rendered
  string by parsing it back fails on legitimate output (`:primitives/Int` is not
  readable source) and forced a second, lexical highlighter. A role fact with
  two homes is a
  [Principle 7](principles/07-single-source-of-truth.md) violation; the missing
  named function between formatter and styler is the
  [Principle 21](principles/21-actors-and-functions-before-mechanism.md) gap.

## 2. Producers and consumers

| # | Producer | Elements |
|---|---|---|
| P1 | Result-value renderer | `:Type value` lines: annotation, literals, constructor names, `<closure>`, vectors |
| P2 | Introspection renderer | `:Type name ; class - doc` lines and their `; match:`/`; defn:`/`; impl:` sections |
| P3 | `/doc` renderer | documentation lines |
| P4 | Code printer, computed layout | `/sexp`, re-laid-out `/source`, agent code blocks |
| P5 | Code printer, original bytes | verbatim `/source` text and agent code that does not round-trip |
| P6 | `/search` row renderer | annotation, name, module path, import snippet, doc excerpt, in-scope marker |
| P7 | Error and warning presenter | `Error:`, `runtime error:`, `; warning:` lines |
| P8 | REPL-frame emitters | prompt, banner, lifecycle and watcher notes, redefinition status lines |
| P9 | Agent prose frame | the agent gutter and markdown prose |

Consumers are the terminal (colour-gated) and the agent membrane, which strips
SGR and must keep receiving plain text. The piped end-to-end harness is a
colour-off consumer.

## 3. Roles

The role vocabulary and each role's style are `repl/spec/10-terminal-styling.md`
§10.3; `styled::Role` and `role_style` (`src/styled.rs`) are its single code
manifestation.

- Every byte of token-styled output carries exactly one role. A surface that
  needs a role absent from §10.3 is a specification change, not an
  implementation choice.
- Pure symbol-list bodies (`/list`, `/imports`, `/exports`) are a layout
  concern and stay unstyled; their category headers carry the `Header` role.
- `/expand` output is not among §10.3's token-styled surfaces; it renders
  plain through `format_sexp`.

## 4. The mechanism — role-span lines, one renderer

- **The carrier is a role-span sequence, never a re-parsed string.** Producers
  build a `StyledDoc` of `(Role, text)` spans; `styled::render` is the only
  site that maps roles to SGR through `style::styled`.
- **Colour-off rendering is the text content, byte for byte.** This keeps the
  golden corpus and the agent membrane unchanged.
- **Producers emit roles at construction.** Semantic producers (P1–P3, P6–P8)
  already hold the structured parts — `Type`, `FQSymbol`, module path, symbol,
  docstring — so module-prefix, name, annotation and metadata spans need no
  parsing.
- **Code roles come from the `Sexp` tree.** P4 and P5 share one
  role-assignment walk (head position, atom kind, annotation, comment) with two
  emitters:
  - P4 lays out the tree (`pp`);
  - P5 parses caller-supplied source and lays spans over the original byte
    ranges, leaving gaps `Plain`; on a parse failure the whole text is `Plain`,
    never a lexical guess.

  Choosing P4 for source that round-trips through the reader is legitimate:
  re-laying-out source is what `/sexp` does. What is forbidden is re-parsing
  **formatter output** to rediscover roles.
- **Non-code surfaces do not pass through the reader.** Value lines and search
  rows are session data, not forms; forcing them through `Sexp` would recreate
  the round-trip failure.
- **Value and definition lines share their role primitives.** The `:Type`
  annotation is one role wherever it appears, so it cannot render differently
  at different sites; the value and definition producers differ only in their
  subject, which is a legitimate difference
  ([terminal styling](../int/terminal-styling.md) §1).

## 5. Deliberate exceptions

- **P9, the agent prose frame**, keeps its own single-sourced styling in
  `style::agent_prose` and the agent markdown renderer; it is the only other
  caller of `style::styled`.
- **Plain-text serialisation is not display.** Persisted source, failed-form
  text and introspection source fallbacks use the colour-free printer, so a
  colour-on session never writes SGR into stored source.

## 6. Invariants and their evidence

- Colour-off output is byte-identical to the unstyled text; the golden corpus
  guards it.
- Each role's SGR bytes are pinned once, with colour forced on.
- A second `style::styled` call in a formatter is a review reject.

## 7. Boundary

- The seam is int-internal: no `cranelisp-types` change, public API or cache
  impact. `render_type` is consumed unchanged; a rendered type is one
  `TypeAnnotation` span.
- **Parked enhancement:** dimming the `module/` prefix inside `:module/Type`
  needs sub-spans within a rendered type. If the user ratifies it, the seam is a
  span-emitting type walk in `cranelisp-types` with `render_type` reimplemented
  as its concatenation — still one walk, and a public-API change needing the
  user gate. **Never implement it as an int-side lexical pass over the rendered
  type string**, which reintroduces the re-parse defect. Until then the whole
  annotation is one span.
- [Display protocol](display-protocol.md) is orthogonal: it extends what the
  value renderer produces, and its collection renderer is one more span
  producer.
