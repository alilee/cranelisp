---
number: 0330
target: /qa
filed_by: /dev (int)
filed_at: 2026-06-13
sprint_filed: 81
refers_to: spec/08-modules.md §8.2.2, src/worker.rs (handle_mod + rewrite_parent_inline_mod), design/arch/fixmes/0217 (resolved)
status: open
---

# Integration test for inline-module §8.2.2 step-2 parent-file rewrite

## Issue

FIXME 0217 (resolved S81 bite 1) implemented spec §8.2.2 step 2 — the parent
source file is now rewritten so an inline `(mod name form…)` form becomes a bare
`(mod name)` reference after the submodule backing file is created
(`src/worker.rs::rewrite_parent_inline_mod`). 0217's proposed resolution named
an integration test as step 3; test-authoring is /qa's, so it is handed off here
rather than written inline (the int `#[cfg(test)]` tier does not have the e2e
filesystem harness).

## Proposed resolution

Add an e2e test (`tests/spec_08_modules.rs`) asserting, for a `--run` project
whose entry file declares an inline `(mod child (defn …))`:

1. After the run, the **backing file** `{entry_dir}/{entry_stem}/child.cl`
   exists and contains the inline body.
2. The **parent file** has been rewritten — the `(mod child form…)` form is
   replaced by bare `(mod child)`, with surrounding forms/whitespace preserved.
3. (Optional) Re-running is idempotent (no spurious mtime bump when the form is
   already the bare reference) and the program output is unchanged.

Verified by hand during 0217 implementation:

```
# app.cl:  (mod child (import [primitives [Int]]) (defn helper [] 7))
#          (defn main [] (Pure (child/helper)))
$ cranelisp --run app.cl        # exit 7
# → app/child.cl created with the body; app.cl rewritten to `(mod child)`
```

## S81 bite-1 update — int-level UNIT test LANDED; e2e still owed (/qa)

The mandatory in-crate unit test for the parent-rewrite is **done** (S81 bite 1,
`/dev` int). The pure splice was extracted from `rewrite_parent_inline_mod` into
a free function `src/worker.rs::splice_inline_mod_to_bare(source, span, name) ->
Option<String>` (the FS I/O + symbol-table mutation stay in the wrapper; the
transformation is now unit-testable without an FS harness — mirrors the
`layout_hash_gate` extraction). Three unit tests pin it in `worker::tests`:

- `splice_inline_mod_rewrites_to_bare_reference` — inline `(mod child …)`
  spliced to bare `(mod child)`, surrounding forms/whitespace preserved;
- `splice_inline_mod_is_idempotent_on_bare_reference` — already-bare → `None`
  (no spurious mtime bump on reload);
- `splice_inline_mod_skips_out_of_range_span` — synthetic / out-of-range span is
  a no-op.

**This FIXME stays OPEN for the e2e half only.** The `tests/spec_08_modules.rs`
filesystem-level test (steps 1–3: backing file created, parent rewritten,
re-run idempotent + output unchanged) is `/qa`'s to author — the int `#[cfg(test)]`
tier has no e2e filesystem harness, and `/dev`-int may not write integration
tests (`tests/CLAUDE.md`). `// spec: spec/08-modules.md §8.2.2`.

## Operational implication / Context

Low priority — the behaviour is implemented and manually verified, and the
transformation is now unit-guarded. The e2e is the durable end-to-end
regression guard per the project test-traceability rule.
`// spec: spec/08-modules.md §8.2.2`.
