# Continue: Sprint 49 — Macro Pipeline Gaps

## Context

Persistent worker threads and prelude loading landed in commit `8340a88`. The deadlock is resolved.
stdlib tests run: 38/54 pass. The 16 failures are all macro pipeline gaps in the v4 worker path.

Read `design/arch/pipeline-convergence-playbook.md` §"Remaining Work" for the categorized failure list.

## The 16 stdlib failures (3 categories)

### Category 1: Macros module symbols unavailable in expansion (10 failures)

Tests: `macro_str_*` (3), `macro_thread_first_*` (3), `macro_thread_last_*` (3), `macro_vec_access` (1)

Error examples:
- `"undefined variable: SexpStr"` — str macro expansion references SexpStr
- `"constructor SexpList has no type scheme"` — threading macro expansion references SexpList

The prelude's macros (str, ->, ->>) expand to code that references constructors from the `macros`
synthetic module (SexpStr, SexpList, etc.). When these macros expand in a user module context,
the expanded code can't find the macros module symbols.

Investigate: how does the v4 pipeline's macro expansion handle the `macros` module import?
The `inject_macros_import` call in `process_module_forms` injects `(import [macros [*]])` for
fresh modules. Check whether the expanded macro code runs in the user module's scope (which has
macros imported) or in some other context where macros symbols aren't available.

Key files: `src/worker.rs` (process_module_forms, inject_macros_import), `src/expander.rs`

### Category 2: Defmacro-in-expansion-results (4 failures)

Tests: `macro_const_*` (2), `macro_def_*` (2)

Error: `"defmacro should be handled before AST building (macro expansion phase)"`

The prelude's `const` and `def` macros expand to `defmacro` forms. The v4 pipeline's
`process_regular_form` passes expanded sexps to `build_program` which rejects defmacro.
The expansion result needs to be re-classified: if expansion produces a defmacro, it should
be handled by the macro registration path, not the regular AST builder.

Key files: `src/worker.rs` (process_regular_form, pass2_check_bodies_with_expansion)

### Category 3: Vec literal parse intercept (2 failures)

Tests: `macro_vec_empty`, `macro_vec_elements`

Error: `"vec literals not yet supported (Ring 1)"`

`(vec)` and `(vec 1 2 3)` are intercepted by the sexp parser or AST builder as vec literals
before macro expansion runs. The `vec` macro in the stdlib should expand these, but the parser
claims them first. Either the parser check needs to be removed/deferred, or the macro needs to
use a different name.

Key files: `crates/cranelisp-frontend/src/` (sexp parser or AST builder vec literal handling)

## Verification

Run: `cargo nt --test stdlib --no-fail-fast` — target is 54/54 pass.
Also check no regressions: `cargo nt --test ring0` (expect 106/108, 2 pre-existing checked_div).

## What NOT to change

- Worker threading (session_v4.rs, scheduler.rs) — done and working
- Prelude loading / null import — done and working
- Display formatting — done and working
- Test infrastructure (tests/helpers/mod.rs) — done
