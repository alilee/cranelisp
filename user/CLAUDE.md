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
| `cli-reference.md` | The `cranelisp` command-line reference: modes, options, target resolution, lib search path / `Cranelisp.toml`, `/search`; **linked-executable exit code = `--run`'s rule** (S118 parity fix) + the `CRANELISP_RC_DEC_CHECK` seam-check row | live |
| `getting-started.md` | Install, REPL basics, first program (pure + IO — the inline `hello.cl` two-step, since `examples/21-hello-io` is dark under FIXME 0907), platforms/IO model, showcase pointer | live |
| `tutorial/` | Progressive introduction paralleling `examples/`; target surface for the forthcoming `/learn` tutorial | not yet authored (forward input for `/learn`, FIXME 0052) |
| `guide/` | Feature-by-feature user-facing reference paralleling `spec/` | started — `bitwise.md`, `field-accessors.md`, `constructors.md` (`Type.Ctor` canonical name + bare alias + same-name disambiguation, value and pattern position), `functions.md` (`fn` single-arity vs multi-arity `defn`; clauses infer like separate mutually-recursive functions, sibling self-calls carry types across clauses), `parallel-collections.md`, `concurrency.md` (user side), `using-platforms.md` (platform-consumer side — the `(platform <name>)` + `(import [platform.<name> [*]])` two-step), `writing-platforms.md` (platform-author side), `live-development.md` (redefinition: late binding, cascade report, broken symbols, recovery — `repl/spec.md §18`; **impl redefinition** — wholesale replacement, rejected re-`impl` leaves the prior impl dispatching, `/info <Trait>` de-duplication — §18.9 + `spec/05-definitions.md` §5.4.5 [S115]), `traits.md` (`deftrait`/`self`/method sigs; **colon-free return type** and why `defn` differs; the **occurrence rule** at any arity + method-level type variables; **marker traits are not specified** — parked, movable boundary; **default methods** — inferred type, `:Type` on the body, per-impl template / override owes nothing, not a supertrait [S115]; concrete + HKT echo-head impl; return-type dispatch + `:Type` remedy; method-import dispatch D2; binder heads) live. **S118 known-limitation notes:** `concurrency.md` — `core.io` (`timeout`, `>>`) does not compile, cancellation example re-spelled over `primitives`-only `race`/`sleep` (FIXME 0907); `field-accessors.md` — accessor note re-axed onto **constructor-arm field lists** (the polymorphic framing was falsified; FIXME 0867) |
| `errors/` | Error-message catalogue, written as each error is confirmed | started — `trait-impl-diagnostics.md` (binder-position rejects incl. value-level binders and the **dotted** twin with the binder-vs-reference table [S115]; dangling-qualifier empty-module/local-half rejects; `:`-must-bind-a-type; type-parameter-must-be-lowercase; `deftrait`/`impl` declaration diagnostics; **no-occurrence-of-the-implementing-type** (both arities) and **zero-method trait** rejects; **impl-conformance mismatch** — quoted with a standing warning that the message reports its roles inverted and names no trait/method context (FIXME 0806) — and the **missing-required-method re-`impl`** reject [S115]; no-impl + return-poly `:Type` dispatch diagnostics) |

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
