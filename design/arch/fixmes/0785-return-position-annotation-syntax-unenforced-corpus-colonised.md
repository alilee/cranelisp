---
number: 0785
target: /qa
filed_by: /sprint
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-frontend/src/reader.rs::read_colon_prefix;
  crates/cranelisp-frontend/src/reader/tests.rs::annotation_fold_rejects_dangling_delimiters_at_introducer;
  tests/spec_07_traits.rs::deftrait_method_annotated_named_param_accepted;
  spec/07-traits.md §7.1.1
status: open
---

# Retain one exact solution guard for the structurally rejected trait-return annotation

## Source-first disposition (S121 C2, 2026-09-01)

The original product defect and corpus repair are complete.
`reader::read_colon_prefix` now owns the syntax structurally: a `:` introducer
reads both its type and following subject into one `Sexp::Annotated`; before
`)` or `]`, the absent subject rejects at the introducer with `annotation
missing expression`. Consequently `(show [x] :String)` cannot reach the trait
builder or checker. The reader unit
`annotation_fold_rejects_dangling_delimiters_at_introducer` pins that generic
delimiter mechanism.

The originally cited positive fixtures in `tests/spec_07_traits.rs`,
`tests/spec_05_definitions.rs`, `tests/spec_qualified_name_sweep.rs`,
`tests/w2_close_fences.rs` and `tests/repl_persist.rs` now use bare return types.
The exact old spellings survive only in explanatory comments or historical
plans, not as positive inputs. The tracked demos are likewise clean. There is
no remaining corpus-repair tail.

FIXME 0801's correction is incorporated here: `git ls-files
repl/demos/runs/**` is empty and `.gitignore` excludes `repl/demos/runs/`.
Those paths are generated replay output, not committed fixtures; no `/repl`
action is owed.

The requested position/shape matrix is otherwise represented by existing
controls: `deftrait_method_annotated_named_param_accepted` covers an annotated
parameter with a bare required return; the standing trait declarations cover
bare parameters and bare returns; `trait_default_body_ascription_and_trailing`
and `trait_default_method_body_ascription_accepted` cover an annotated value
body; and C2's deftype head-mode units cover annotated and bare fields. A
tracked-source corpus lint is not a closure requirement: the grammar violation
is unconstructable after reading, while such a lint would miss the substantial
embedded Rust-string corpus that exposed the original issue.

## Remaining evidence and closure trigger

Root `CLAUDE.md` requires a defect-born solution-level regression test. The
suite still has no exact process input for the malformed required-method tail;
the nearby nameless-parameter test uses `[:a]`, a different source position.
At the first executable root-compiler gate, `/test` adds one narrow REPL guard:

```clojure
(deftrait Bad (show [x] :String))
```

It asserts the located `annotation missing expression` refusal at that colon
and a following lookup proves `Bad` was not registered. Existing
`(show [x] String)` acceptance and `(show [x] :String x)` annotated-default-body
acceptance are the discriminating controls. This source is not authored while
the workspace is intentionally unbuildable; frontend's generic unit is not a
substitute for the process-level defect guard.

Close and delete this filing when that one solution test is committed and
green. No product correction, corpus rewrite, standing lint or design return
remains.
