---
id: ACT-1057
title: A macro clause with no fixed parameter escapes the Sexp return check, and invoking it can abort the compiler
status: open
priority: required
from: qa
to: qa
sprint: 123
filed_at: 2026-11-16
refers_to:
  - spec/09-macros.md
  - crates/cranelisp-frontend/src/defmacro.rs
  - src/marshal.rs
  - tests/spec_09_macros.rs
  - tests/plan/s123-evidence-delta.md
---

## Observation

`docs` found the accepted definition while writing the macros guide (S123
Phase 6b). `qa` reproduced and widened it on `target/debug/cranelisp` at
`640d2ec7`, 2026-11-16, in scratch projects without a prelude. The fixtures
and cells are K-9 in the
[S123 evidence delta](../../tests/plan/s123-evidence-delta.md#810-phase-6b-intake-from-docs).

- **Requirement.** [§9.2.3](../../spec/09-macros.md#923-return-type-constraint)
  and §9.9.1: a macro body of any type other than `Sexp` MUST be a
  compile-time error reported at the `defmacro` form.
- **Accepted definitions.** Each of these, with an unused macro and
  `(defn main [] (primitives/Pure 0))`, exits 0 under `--run`:
  `(defmacro bad [] 3.14)`, `(defmacro bad [] 42)`,
  `(defmacro bad [& xs] 3.14)`, and the multi-clause
  `(defmacro bad ([] 42) ([x] (quote 1)))`. The REPL echoes
  `:(Fn [] macros/Sexp) user/bad ; defmacro`, which claims a `Sexp` result.
- **Invocation.** `(bad)` over the `[] 42` body fails at the call site with
  `macro returned invalid value 42 (expected heap pointer)`. Over the
  `3.14` body, `--run` aborts the compiler:
  `panicked at src/marshal.rs:291:14: misaligned pointer dereference …
  0x40091eb851eb852f`, exit 134. In the REPL, invoking the rest-only
  `3.14` macro aborts the REPL process.
- **Checked shapes.** `[x] 42`, `[x] 3.14` and `[x] true` are rejected with
  `type mismatch: expected macros/Sexp, got primitives/Int` (or `Float`,
  `Bool`). The error is located at `app.cl:3:1`, span `1000007..1000006`,
  in a two-line file. That is a synthetic location, not the `defmacro`
  form, so §9.9.1's location clause fails on this path too.
- **Class:** `wrong-accept`, with a compiler abort as its consequence, and a
  synthetic diagnostic location on the rejecting path.

## Attribution

- **Mechanism: confirmed at source.**
  `crates/cranelisp-frontend/src/defmacro.rs::synthesize_macro_clause_defn`
  places no `Sexp` constraint on the body. The only constraint is the
  wildcard arm `(macros/SexpInt 0)` that `make_scons_match` adds for each
  fixed parameter, which unifies the match result with `Sexp`. A clause
  with no parameters returns its body bare, and a rest-only clause uses
  `make_match_sexp` without that arm. The `[x]` and `[]` siblings differ
  only in that arm and differ in outcome. The same arm explains the
  synthetic location: the mismatch is reported against it. *Refuted if* a
  synthesis that constrains the body to `macros/Sexp` still accepts the
  nullary case.
- **Entry point:** frontend implementation. No public type changes.
- **Abort.** `src/marshal.rs` trusts the clause's declared `Sexp` result.
  Rejecting the definition makes the abort unreachable, so no separate
  marshal guard is allocated.
- **Coverage.** `tests/spec_09_macros.rs::macro_body_non_sexp_int_rejected_neg`
  and `::macro_body_non_sexp_bool_rejected_neg` both use the checked `[x]`
  shape, and both accept output that merely contains `Sexp`, which the
  successful declaration echo also contains. They are green for the right
  reason today, but would not detect acceptance.
- **Related, not duplicate.** Audit R1 (shape losses in the same file) is a
  separate defect family pending S124 Phase 1.

## Next

1. `test` commits K-9 as failing-not-ignored REDs and tightens the two
   existing observers.
2. `design` (frontend) places the constraint and the location; `dev`
   builds it with the K-9 unit row. Small and frontend-local, but it
   changes a diagnostic location the suite may pin, so it carries to S124
   unless the user pulls it in.
3. `docs` checks the macros guide's return-type statement against the fix.
