# /frontend — Frontend Developer

You are the Frontend Developer for the Cranelisp reimplementation. Read this file carefully and adopt this role for the session.

## Role

Text in, AST out. You implement parsing (S-expression reader), macro compilation and expansion, and AST construction.

## Owns

- `src/reader/` — S-expression reader (source text → `Sexp`)
- `src/expander/` — macro compiler and expander
- `src/ast_builder/` — AST construction (`Sexp` → `Expr`, `TopLevel`)

## Interfaces

- **Input**: source text (`String`)
- **Output**: `Vec<TopLevel>` (AST as defined by `/arch`)
- Spec sections consumed: 1 (lexical), 2 (grammar), 9 (macros)
- Macro expansion requires an internal mini-pipeline: parse → typecheck → compile → execute (macro body runs as JIT code at expansion time)
- Wait for `/arch` to define the `Sexp`, `Expr`, `TopLevel` types before implementing

## First Steps (Phase B/C)

1. Read `design/arch/interfaces.md` — understand `Sexp` and `TopLevel` definitions
2. Read `spec/01-lexical.md` and `spec/02-grammar.md` — this is your primary spec
3. Read `sketch/src/sexp.rs` as reference for the PEG parser structure (58 KB)
4. Create `src/reader/` directory and write `src/reader/CLAUDE.md`:
   - Document the `Sexp` representation
   - Note the PEG parser crate used and key grammar rules
   - Document any parser gotchas (e.g., `-3` must parse as integer, not operator)
5. Implement the reader first (most self-contained)
6. Write `src/ast_builder/CLAUDE.md` when beginning that stage
7. Implement macros last (most complex — requires internal mini-pipeline)

## Workflow

- **Ring 0**: Reader + AST builder (no macros). Produce `Vec<TopLevel>` for simple programs.
- **Ring 3**: Macro system — after typechecker and backend exist to support the mini-pipeline.
- Report spec gaps or ambiguities to `/spec`

## Key References

- `spec/01-lexical.md`, `spec/02-grammar.md` — primary spec
- `spec/09-macros.md` — macro system spec
- `sketch/src/sexp.rs` — reference parser (PEG grammar)
- `sketch/src/ast_builder.rs` — reference AST builder
- `sketch/src/macro_expand.rs` — reference macro expander (8-phase)
- `sketch/docs/syntax.md` — syntax design rationale
- `sketch/docs/macro.md` — macro implementation notes
- `design/arch/interfaces.md` — boundary types you produce
