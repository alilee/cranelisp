# sketch/

This directory contains the Cranelisp prototype — a complete, working compiler (~34K lines Rust, ~8K lines specification, ~978 tests) that proves the language design. It is **not the active compiler**. The active reimplementation lives at the project root.

## Purpose: Reference Oracle

When the specification is ambiguous, run the prototype and observe:

```bash
cd sketch
cargo build
cargo run -- --run examples/hello.cl
```

The REPL is available without arguments:
```bash
cargo run
```

Use `just <recipe>` for common tasks (build, test, run, check, fmt). See `justfile`.

## Directory Layout

- `src/` — Rust compiler source (~34K lines; the pipeline being replaced)
- `Cargo.toml` — Rust workspace (cranelisp, cranelisp-platform, cranelisp-runtime, exe-bundle, platforms)
- `lib/` — Standard library in Cranelisp (reference for `/stdlib` skill to rebuild)
- `examples/` — 25 feature-demonstration programs (reference for `/examples` skill to build learning sequence from)
- `docs/` — Legacy design documents and language specification
  - `docs/spec/` — 16 spec files (canonical source; copied to `../spec/` for the reimplementation)
  - `docs/reimplementation.md` — Full reimplementation strategy (copied to `../design/`)
  - Other design docs — architecture, type system, codegen rationale, etc.
- `tests/` — ~978 behavioral tests encoding prototype behavior (acceptance criteria for reimplementation)
- `audits/` — Code quality audits identifying structural debts to avoid in the rewrite
  - `typechecker.md`, `codegen.md`, `module.md`, `cache.md` — HIGH/MEDIUM/LOW severity findings

## Key Files for Each Role

| Role | Relevant sketch files |
|---|---|
| `/spec` | `docs/spec/*.md` — run examples to validate |
| `/arch` | `audits/*.md`, `src/module.rs`, `src/typechecker.rs` — structural lessons |
| `/frontend` | `src/sexp.rs`, `src/ast_builder.rs`, `src/macro_expand.rs` |
| `/typecheck` | `src/typechecker.rs`, `src/typechecker/` |
| `/backend` | `src/codegen.rs`, `src/jit.rs`, `src/codegen/` |
| `/qa` | `tests/integration.rs` (~470 tests), `tests/e2e/`, `tests/CLAUDE.md` |
| `/stdlib` | `lib/prelude.cl`, `lib/core/` |
| `/examples` | `examples/` — 25 programs for reference |
| `/platform` | `cranelisp-platform/`, `cranelisp-runtime/`, `platforms/` |
| `/review` | `audits/*.md` — read before every review session |

## What NOT to Copy

The prototype's structural debts (documented in `audits/`) must not be reintroduced:
- **`CompiledModule` god object** (133 references, 18 files) — decompose per `audits/module.md`
- **Monolithic functions** (codegen functions >500 lines) — split per `audits/codegen.md`
- **String-based dispatch** between pipeline stages — use typed enums
- **Dual batch/REPL pipelines** with divergent code paths — single pipeline
- **ISA constructed separately** from JIT path — one construction point

See `audits/CLAUDE.md` for the full audit process and conventions.
