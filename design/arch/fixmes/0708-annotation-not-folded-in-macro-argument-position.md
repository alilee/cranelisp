---
number: 0708
target: /design (int)
filed_by: /repl
filed_at: 2026-07-20
sprint_filed: 114
refers_to: design/arch/annotated-sexp-node.md;
  design/int/int.md §16.0;
  crates/cranelisp-frontend/src/reader.rs;
  tests/annotation_fold_macro_arg_0708.rs;
  repl/spec/05-error-presentation.md;
  tests/plan/PLAN.md
status: open
---

# `:Type` in macro-argument position — residual tails after the read-time fold

## Current state (verified 2026-09-24)

- The user ruled Reading A-structural on 2026-07-21: `:Type <form>` folds at
  read time into one `Sexp::Annotated` node, so a macro receives the folded
  node as one argument and `(def x :Int 5)` has two macro arguments. The
  contract is [annotated S-expressions](../annotated-sexp-node.md); the spec
  rows (§1.4.5, §1.8, §2.3.8, §9.1.2/§9.2.2/§9.4.2, §7.1.1) are scribed.
- The reader constructs `Sexp::Annotated` for every position
  (`crates/cranelisp-frontend/src/reader.rs`). The positive witness
  `annotation_fold_macro_arg_0708::annotation_folds_in_macro_argument_position`
  and its unannotated control exist.

## Remaining obligation

1. **Annotation-mirror tail (Binary/int).** Four lexical `src/` mirrors of the
   retired pre-fold shape remain: `worker::leading_annotation_len` (a
   constant-zero stub), `save.rs::is_bare_colon`,
   `expander::is_annotation_symbol` and `pretty.rs::is_type_annotation_list`
   with its helpers. Their disposition and arming evidence are
   `design/int/int.md` §16.0.
2. **Spaced degenerate spelling.** `repl/spec/05-error-presentation.md`
   records that `: Int` alone reports `undefined variable: :` where `:Int`
   alone reports `annotation missing expression`. Not re-verified here.
3. **Evidence reconciliation (`qa`).** `tests/plan/PLAN.md` still describes
   this fork as awaiting a `spec` ruling and allocates a polarity-safe
   `returned malformed sexp` pin. The ruling is made; `qa` decides whether the
   positive witness supersedes that pin, and `test` retires the witness's
   open `// defect:` notation when it passes.

## Closure

All three items are resolved or carried by their owners' standing documents.
