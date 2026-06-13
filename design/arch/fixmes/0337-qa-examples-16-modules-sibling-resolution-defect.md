---
number: 0337
target: /qa
filed_by: /sprint
filed_at: 2026-06-13
sprint_filed: 81
refers_to: examples/16-modules/main.cl, examples/16-modules/math.cl, tests/examples.rs (excludes 16-modules), spec/08-modules.md §8.11 (project layout / module resolution)
status: open
---

# `examples/16-modules` sibling-file module resolution broken for entry module `main` (no CI coverage)

## Issue (Phase-6a /examples finding, S81)

`examples/16-modules/main.cl` — the project's ONLY multi-file example — does not run:

```
module 'main' failed: submodule 'main.math' not found (declared by 'main')
```

The entry file `main.cl` declares `(mod math)` (a **bare** sibling-file module decl,
no inline body). The resolver looks for the **nested** submodule `main.math` instead of
the **sibling file** `math.cl`. Sibling-file `(mod …)` resolution appears broken when the
entry module is literally named `main`. Fails identically from repo root, from inside
`examples/16-modules/`, and with the platform path wired.

**NOT an S81 regression** (confirmed by /sprint): the S81 inline-`(mod)` self-locating-splice
fix (`18a0d07`, `src/process_form.rs::find_inline_mod_span`) requires `children.len() >= 3`,
so it **skips** bare 2-child `(mod math)` forms — it cannot be the cause. This is pre-existing,
surfaced now because Phase-6a exercised the example.

**Zero CI coverage.** Both `tests/examples.rs` and the legacy `examples_run.rs` explicitly
exclude `16-modules/` ("a directory, not a top-level .cl file"). That exclusion is why the
breakage sailed through every per-crate sweep undetected.

## Proposed resolution

1. **/qa authors a minimal failing repro** (per the user-proxy defect protocol): a two-file
   project — entry `main.cl` with `(mod sibling)` + a sibling `sibling.cl` defining a fn —
   `--run` it, assert the sibling fn resolves (and assert the negative: it must NOT look for
   nested `main.sibling`). First confirm whether the bug is **entry-named-`main`-specific**
   (try a non-`main` entry name) — that narrows the root cause for the resolver owner.
2. **Hand the narrowed repro to `/int`** (module resolution owner) for the fix.
3. **Add CI coverage for multi-file examples** — extend `tests/examples.rs` to run a
   directory-entry example (`16-modules/main.cl`) and assert its documented exit (303 per the
   file's own comment), so multi-file module regressions are caught going forward.

## Context

Phase-6a /examples assessment, S81. The 27 single-file examples all run green on the S81
binary; this is the lone example failure, and it currently teaches users that multi-file
projects are broken. Forward-flow to a sprint that owns the module-resolution fix.
