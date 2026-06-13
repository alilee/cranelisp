---
number: 0343
target: /int
filed_by: /stdlib
filed_at: 2026-06-13
sprint_filed: 81
refers_to: src/save.rs (generate_module_source, generate_mod_decls), src/session_v4.rs (regenerate_backing_file), design/int/session-persistence.md
status: open
---

# Loading a module with a `(mod child …)` body triggers source regeneration that REWRITES the backing `.cl` WITHOUT the submodule body

## Issue (S81 W-I-5 /stdlib finding)

When a module whose source carries a non-empty `(mod test … defns … )` submodule
body is loaded, the int source-regeneration path (`generate_module_source` →
`atomic_write`) rewrites the on-disk backing `.cl`, emitting only a `(mod test)`
DECLARATION and DROPPING the submodule's entire body. Observed repeatedly while
landing `stdlib/testing/runner.cl`: appending a `(mod test …)` block (verified on
disk), then loading the module, silently truncated the file from ~235 lines to
~57–168 lines, collapsing `(mod test …)` to a bare `(mod test)`.

This is **destructive**: it corrupts committed stdlib source. It also explains
why no stdlib module has ever shipped a working `(mod test)` body — the
self-tests cannot survive a load.

`generate_mod_decls` reconstructs `(mod X)` from the parent's `submodules` list,
but the submodule's definitions live in the CHILD's symbol table, not the
parent's — so regenerating the parent's source from its table alone cannot
reproduce the child body, and the child body is lost on write-back.

Two sub-questions for the owner:
1. **Should regeneration run at all for a non-entry / stdlib dependency module?**
   `regenerate_backing_file` is documented as REPL-entry-module persistence
   (repl/spec.md §15); a `--run`/dependency load should not be rewriting stdlib
   files. If regeneration is firing for dependency modules, that is the primary
   bug.
2. **If it must run, it MUST round-trip the submodule body** — either by reading
   the child table(s) and re-emitting their forms under `(mod child … )`, or by
   preserving the original submodule source verbatim.

## Proposed resolution

`/qa` authors a minimal repro: a two-form file `(defn f [] 1)\n(mod test (defn g
[] 2))`, loaded such that regeneration fires; assert the on-disk file still
contains `(defn g [] 2)`. `// spec:` → design/int/session-persistence.md §1.3
(regeneration section ordering) + repl/spec.md §15. `/int` decides whether to
gate regeneration off for dependency modules or to round-trip submodule bodies.

## Operational implication

Forced the S81 runner to ship WITHOUT a `(mod test)` submodule (validated via the
REPL demo instead). Any future stdlib `(mod test)` body is at risk of silent
corruption until this is fixed. HIGH severity — it can destroy committed source.
