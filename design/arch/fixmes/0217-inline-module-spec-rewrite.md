---
number: 0217
target: /int
filed_by: /arch
filed_at: 2026-05-24
sprint_filed: 69
refers_to: crates/cranelisp-types/src/module.rs §ModDecl, src/worker.rs §handle_mod, repl/spec.md §15.4, spec/08-modules.md §8.2.2
status: open
---

# Inline-module spec §8.2.2 step 2 — parent-file rewrite

## Issue

Spec §8.2.2 ("Inline Submodule Declaration") requires the implementation MUST:

1. Create the submodule backing file (`{parent_dir}/{stem}/{name}.cl`) containing the inline body
2. **Rewrite the parent file, replacing `(mod name form1 form2 ...)` with `(mod name)`**
3. Proceed with standard file-based module loading

Step 1 is implemented at `src/worker.rs:2199-2201` via `write_inline_mod_to_disk`. **Step 2 is not implemented** — the parent file is never rewritten. As a consequence:

- The persistent `ModDecl` in `SymbolTable.submodules` retains `inline_body: Some(forms)` forever
- Re-loading the file overwrites the backing submodule file on every run (idempotent if the inline body is unchanged, but spec calls the inline form "**one-time creation syntax**" — that semantic is violated)
- The spec's "indistinguishable from manually created" invariant after extraction is broken at the data-shape level (the inline_body persists in the symbol table)

## Proposed resolution

Int's source-rewriter (the `.cl` regeneration path documented at `repl/spec.md` §15.4) MUST serialize `ModDecl` as `(mod name)` form only, ignoring `inline_body`. The rewrite must happen at file-load time for any source file containing an inline `(mod name forms…)` form — write the backing file, rewrite the parent file, then proceed with normal file-based loading.

Suggested implementation path:

1. After `write_inline_mod_to_disk` succeeds, rewrite the parent source file to replace the `(mod name forms…)` form with `(mod name)` (preserving surrounding whitespace/comments where possible).
2. Reload the parent file's structural decls so the in-memory ModDecl no longer carries inline_body.
3. Add an integration test asserting that loading a file with an inline form causes the file to be rewritten (mtime change + content check) AND the backing file is created with the body content.

Reference current code: `src/worker.rs:handle_mod` (lines 2194-2210); `write_inline_mod_to_disk` (defined elsewhere in worker.rs); int's existing `.cl` regeneration path per `repl/spec.md` §15.4.

## Operational implication / Context

Until this lands:

- `ModDecl.inline_body` is the data-shape symptom of the unimplemented step 2 (documented in `crates/cranelisp-types/src/module.rs` ModDecl docstring + `design/arch/facades/types.md` §"Item-by-item disposition")
- Repeated file loads silently overwrite the backing file rather than being a true one-time extraction (idempotent in practice but spec-violating in semantics)
- The persistent symbol-table representation of inline-declared submodules differs from manually-created ones (violating spec §8.2.2's "indistinguishable" guarantee at the data level)

The narrowing of `ModDecl` to `{name, visibility, span}` (dropping inline_body) is NOT proposed by this FIXME — frontend correctly populates the field; int correctly consumes it. The field is real and load-bearing during the parse-write-load lifecycle. Only the post-load rewrite + the spec-level "one-time" semantic close together by implementing step 2.

Files this FIXME's resolution will touch:

- `src/worker.rs` (handle_mod + rewrite logic)
- `repl/spec.md` §15.4 (if regeneration path needs documentation update)
- New integration test in `tests/` (asserting rewrite behavior)
