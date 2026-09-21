# design/frontend/

Interior design for `crates/cranelisp-frontend/` — reading, syntactic
validation, AST construction, module-declaration extraction and quasiquote
desugaring. Owned by `design`, narrow-deployed to this surface.

These documents describe **how** the frontend solves its problems: algorithms,
seams, data shapes and the judgments behind them. They are distinct from
`design/arch/bounded-contexts.md` §1 (the boundary contract), the crate's
`lib.rs` rustdoc (the public surface), and `spec/` (what behaviour is correct).
Cite those rather than restating them.

## Document collection

| Collection | Purpose | Boundary |
|---|---|---|
| `frontend-designs` | Frontend interior designs. | The named Markdown products directly under `design/frontend/`, excluding this memory. |

An established collection with live reference checking. Every product is
current: a document whose subject is delivered states the delivered shape and
the judgments that hold it, not the migration that produced it.

- [frontend.md](frontend.md) — the master design: what the surface is, its
  public shape, its interior modules, and the form-classification chain.
- [reader.md](reader.md) — source bytes to `Sexp`: precedence, reader macros,
  name lexing, comment preservation.
- [ast-builder.md](ast-builder.md) — `Sexp` to AST: entry points, `build_form`,
  head classification, type expressions, `deftype`, patterns.
- [modules.md](modules.md) — structural-declaration extraction and `super`
  normalisation.
- [module-preamble.md](module-preamble.md) — leading comment-block capture and
  its round-trip contract.
- [defmacro-synthesis.md](defmacro-synthesis.md) — `defmacro` shape parse and
  per-clause definition synthesis.
- [quasiquote-fold.md](quasiquote-fold.md) — quote-family desugaring and its
  fold into the AST chokepoints.
- [s116-syntax-and-annotation.md](s116-syntax-and-annotation.md) — the read-time
  annotation fold and `deftype` declaration-shape enforcement.
- [binder-head-reject.md](binder-head-reject.md) — the one reject for a
  qualified or dotted spelling in any binder position.
- [enforcement-matrices.md](enforcement-matrices.md) — the operand-position body
  seam and the reader's dangling-qualifier rejects.
- [trait-impl-head-parse.md](trait-impl-head-parse.md) — the `deftrait` and
  `impl` head grammar.

## What belongs here

The frontend is **purely syntactic**: text → `Sexp` → AST. It does no macro
recognition and no macro execution — recognition is
`cranelisp_types::resolve_macro_head`, driven by typecheck and int; execution is
int's. Quasiquote desugaring is the whole of its macro-adjacent role. The reader
is a **hand-written recursive-descent** parser; there is no parser-generator
grammar.

Record a decision here when it shapes the crate's interior: a seam that
single-sources a rule, a placement judgment and why the alternative was wrong, a
representation that makes an invalid state unrepresentable, or a boundary the
frontend deliberately does not cross. Record the falsifier when a claim rests on
a neighbouring crate's behaviour.

Do not record: public signatures (the rustdoc and `public-api.txt` own them),
spec rules (cite the section), a neighbouring context's interior (name its
capability in its owner's language), or the sequence of sprints that produced the
current shape (git carries that).

## Conventions

- One file per subsystem or per cross-cutting judgment, named for the subject
  rather than for the increment that produced it.
- Prefer a diagram only where the data flow is not obvious from prose.
- Record a rejected alternative when a reader could reasonably re-propose it, and
  say what makes it wrong.
- A design that no longer matches the source is worse than none. When the
  implementation changes, the design changes with it in the same increment.
