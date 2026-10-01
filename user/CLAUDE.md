# user/

User-facing documentation for Cranelisp. Owned by `docs`
(`.agents/skills/docs/SKILL.md`).

## Authority

This directory holds the **approachable, practical, example-driven** documentation
a newcomer reads to learn and use Cranelisp. It is distinct from the normative
sources it re-presents:

- `spec/` — normative language specification (owned by `spec`), precise and written
  for implementors.
- `repl/spec.md` — normative REPL experience specification (owned by `spec`),
  including the CLI invocation contract (`repl/spec/00-cli-invocation.md`).
- `design/` — implementation design (`design/arch/` owned by `arch`,
  `design/{crate}/` by `design`).

User docs do **not** re-derive normative behaviour. They re-present it for a reader
who wants to get something working, and they **cross-link** the normative source so
the precise rules always have one home. Where the spec and a user doc disagree, the
spec wins and the user doc is the bug.

## Doc set

This file establishes the `user-documentation` collection:

> Current user instructions, feature guides and diagnostic explanations.

Its exact file patterns are declared in `standing-documents.toml`.

- `cli-reference.md` — the `cranelisp` command-line reference.
- `getting-started.md` — installation, REPL basics, first programs and pointers
  onward.
- `guide/` — feature-by-feature reference paralleling `spec/`.
- `errors/` — error-message explanations, written as each error is confirmed.

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
  `repl/spec/00-cli-invocation.md` §0.4), say so plainly rather than implying it works.
- **Verify CLI/behavioural claims against the source or the binary** before writing —
  read `src/main.rs` for the CLI contract, run the prebuilt binary to confirm error
  text. Do not write CLI claims from memory.

## Cross-role changes

- A user doc that surfaces a defect — a documented example that does not compile,
  output that contradicts the doc — follows root `CLAUDE.md` §"Usability Findings
  and Defects": hand off with a minimal repro; the item is not closed until `test`
  has committed a narrow failing test reproducing it.
- A change needed in another role's document follows root `CLAUDE.md`
  §"Cross-Role Changes": resolve it through `sprint` within the increment, or file
  an action under `sprints/actions/`. Do not edit the other role's files directly.
