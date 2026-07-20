# design/frontend/

Solution design documents for the Cranelisp frontend (reader, macro expander, AST builder). Owned by `/design`, narrow-deployed to this crate.

## Purpose

These documents describe *how* the frontend solves problems — algorithms, data structures, internal architecture, and trade-offs. They evolve alongside the implementation: sketched before coding, refined during, and updated when designs change.

This is distinct from:
- `design/arch/interfaces.md` — the *boundary contract* (what goes in and out)
- `spec/` — the *language definition* (what behaviour is correct)

## What to Document

The frontend is **purely syntactic** post-S76 W-Macro: text → `Sexp` → AST. It
does **no macro recognition or execution** (recognition → typecheck via
`cranelisp_types::resolve_macro_head`; execution → int via
`cranelisp_types::MacroExpander`) — only quasiquote desugaring. The reader is a
**hand-written recursive-descent** parser (there is no PEG grammar — the stale
`peg` references in `plan-frontend.md`/history are drift).

- **Reader internals**: hand-written recursive-descent dispatch (the
  load-bearing first-byte precedence + `/`/`.` structural significance), the
  dangling-qualifier reject placement, span threading, error recovery
- **AST builder**: Sexp-to-AST translation decisions, desugaring rules,
  validation passes, the annotation-pairing (`build_one_expr_at`) and
  binder-reject (`reject_qualified_binder_head`) single-seams, enforcement
  matrices (operand-position ascription/trailing; binder heads)
- **Quasiquote desugaring**: `` ` ``/`~`/`~@`/`quote` → synthetic `macros/`
  constructor Sexps; the fold into `build_forms`/`build_form`; synthetic-span
  allocation
- **Defmacro shape-parse**: `(defmacro name [params] body)` → `DefmacroInfo` +
  per-clause `Defn` synthesis (shape only — no execution)
- **Design evolution**: what changed and why across sprints, and what was
  considered but rejected (per-sprint history lives in the docs themselves and
  `sprints/archive/`)

## Conventions

- One file per major subsystem (e.g., `reader.md`, `macro-expansion.md`, `ast-builder.md`)
- Include diagrams (ASCII) for non-obvious data flow
- Record rejected alternatives briefly — "considered X, chose Y because Z"
- Update docs when the implementation changes; stale design docs are worse than none
