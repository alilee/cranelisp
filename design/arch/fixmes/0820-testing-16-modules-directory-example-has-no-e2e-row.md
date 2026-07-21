---
number: 0820
target: /testing
filed_by: /examples
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/examples.rs:109 + :130 (the exclusion comments) + :264-285 (the
  stale rationale block) + :347-365 (`37-method-import` — the row shape to copy);
  examples/16-modules/{main.cl,main/math.cl,main/shapes.cl};
  examples/plan-examples.md §2 row 16
status: open
---

# `examples/16-modules/` — the sequence's ORIGINAL multi-file example — still has no e2e row, on a rationale that is now false

## Severity

**Moderate.** A checked-in learning-sequence example is outside the CI umbrella,
so a regression in it is invisible until a `/examples` phase-6 sweep runs by
hand. This is the exact hole FIXME 0337 was filed for; it was closed for the
*general* multi-file case with a decoupled tmpdir fixture, but the checked-in
example it was named after is still uncovered. The younger sibling
`37-method-import/` (S113) got a proper row; 16 never did.

## Issue

`tests/examples.rs::every_example_runs_with_documented_exit` covers only
top-level `examples/*.cl` and explicitly excludes directory projects
(`:109`, `:130`). `37-method-import/main.cl` therefore has its own dedicated
test (`:347`). `16-modules/main.cl` has none.

The stated reason for not coupling to it (`:276`) is:

> that example is not yet relaid out to the nested shape (a Phase-6 /examples
> task), so coupling to it would make this guard depend on user-proxy churn

**That premise is false at HEAD.** `16-modules/` IS in the nested §8.2.5 shape:

```
examples/16-modules/main.cl        ;; (mod math) (mod shapes)
examples/16-modules/main/math.cl
examples/16-modules/main/shapes.cl
```

The relayout the comment waits on has already happened. The self-contained
tmpdir fixture at `:290` should STAY (it is the decoupled durable guard for the
mechanism); what is owed is the additional *example* row.

## Ask

Add a directory-project test alongside
`method_import_directory_example_runs_with_documented_exit`, modelled on it
exactly:

- entry: `examples_dir().join("16-modules").join("main.cl")` (read-only on
  project_root — same comment convention as the 37 row)
- expected exit: **47**
- `// spec:` — spec/08-modules.md §8.2.5 (nested multi-file directory project;
  `mod`/`import`/`export`/`defn-` per examples/plan-examples.md §2 row 16)

Verified by `/examples` at S115 Phase 6a (2026-07-21, HEAD `5ba28de8`):
`--run` = 47 and `--link` = 47, fresh cache, from `cwd=examples/`.

Also correct the stale rationale paragraph at `:264-285` so the next reader is
not told a relayout is still pending.

## Not asked

No change to the top-level umbrella table, and no change to
`examples/16-modules/` itself — the example is green in both modes and its
documented exit is unchanged.
