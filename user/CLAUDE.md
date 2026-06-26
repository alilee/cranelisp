# user/

User-facing documentation for Cranelisp. Owned by the `/docs` skill.

## Authority

This directory holds the **approachable, practical, example-driven** documentation
a newcomer reads to learn and use Cranelisp. It is distinct from the normative
sources it re-presents:

- `spec/` — normative language specification (owned by `/spec`), precise and written
  for implementors.
- `repl/spec.md` — normative REPL experience specification (owned by `/repl`),
  including the CLI invocation contract (§0).
- `design/` — implementation design (owned by `/arch` and the developer skills).

User docs do **not** re-derive normative behaviour. They re-present it for a reader
who wants to get something working, and they **cross-link** the normative source so
the precise rules always have one home. Where the spec and a user doc disagree, the
spec wins and the user doc is the bug.

## Doc set

| File | Purpose | Status |
|---|---|---|
| `CLAUDE.md` | This file — ownership and writing conventions | live |
| `cli-reference.md` | The `cranelisp` command-line reference: modes, options, target resolution, lib search path / `Cranelisp.toml`, `/search` | live |
| `getting-started.md` | Install, REPL basics, first program (pure + IO), platforms/IO model, showcase pointer | live |
| `tutorial/` | Progressive introduction paralleling `examples/`; target surface for the forthcoming `/learn` tutorial | not yet authored (forward input for `/learn`, FIXME 0052) |
| `guide/` | Feature-by-feature user-facing reference paralleling `spec/` | started — `bitwise.md`, `field-accessors.md` live |
| `errors/` | Error-message catalogue, written as each error is confirmed | not yet authored |

## Writing conventions

- **Approachable and practical.** Lead with what the reader wants to do, then how.
  Show a command or a snippet before explaining the rule behind it.
- **Cross-link, do not restate normative rules.** When a precise contract lives in
  `spec/` or `repl/spec.md`, link to the exact section rather than paraphrasing it —
  paraphrase drifts. A user doc may summarise the *shape* of a rule and point at the
  normative text for the edges.
- **Use the language's own notation.** Types and values follow the REPL's
  `:Type value` convention (e.g. `:primitives/Int 3`). Never expose internal
  type-variable names (`a0`, `t42`) to users.
- **As-built, not aspirational.** Document what the binary does today. When a feature
  is specified-but-future (e.g. `--help`/`--version`, marked Future in
  `repl/spec.md §0.4`), say so plainly rather than implying it works.
- **Verify CLI/behavioural claims against the source or the binary** before writing —
  read `src/main.rs` for the CLI contract, run the prebuilt binary to confirm error
  text. Do not write CLI claims from memory.

## Cross-skill changes

If a user doc surfaces a defect (a documented example that does not compile, output
that contradicts the doc), `/docs` work on that item is not closed until `/qa` has a
narrow failing test reproducing it — see root `CLAUDE.md` §"Usability Findings and
Defects". For changes needed in another skill's owned document, file a FIXME under
`design/arch/fixmes/NNNN-name.md`; do not edit the other skill's files directly.
