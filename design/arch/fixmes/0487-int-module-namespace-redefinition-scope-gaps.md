---
number: 0487
target: /int
filed_by: /port
filed_at: 2026-07-03
sprint_filed: 101
refers_to: repl/spec.md §18, design/int/session-transaction.md §4/§10, src/ (REPL module-namespace turn env)
status: open
---

# `/mod M` redefinition turns don't see the environment the module's own file was compiled in — blocks the at-scale mid-stack edit loop

## Issue

S101's redefinition machinery is aimed at exactly the exemplar's use case:
load a multi-module program, edit a mid-stack function live, let the
transaction recompile/break dependents. Exercised against the Sudoku exemplar
(grid/solver/html/form loaded via import; `/mod grid` / `/mod solver` to edit),
the loop is blocked before the transaction machinery is even reached, because
a module-namespace turn compiles in a **different environment than the module's
file body did**:

1. **Prelude value names are absent.** In `/mod solver`, `(= 1 1)` and
   `(+ 1 2)` fail with `undefined variable: =` / `+`; `None`/`Some` are
   likewise unbound in `/mod grid`. Yet `solver.cl` uses `=`/`+` on nearly
   every line and compiled fine at load — the file body had the prelude, the
   `/mod` turn does not. Consequence: **pasting the very function you want to
   edit back into its own module namespace fails to compile** for essentially
   every real exemplar function (the S86 idiom pass routed all arithmetic
   through prelude trait operators). Only prelude-free bodies
   (`grid/cell-at`, `grid/pow2`, `grid/bit-count`) are editable at all.

2. **Prelude type aliases are absent.** `(defn cell-at [g idx :Int extra] …)`
   in `/mod grid` → ``unknown type `Int` (from module ``)``. Fully-qualified
   `:primitives/Int` works. This matters doubly because unannotated
   redefinitions generalize to polymorphic schemes, which take the §10 T1
   downgrade — so without usable annotations, a module-namespace redefinition
   can practically never be a *concrete* target, and the dependent-recompile
   transaction silently never fires (see §Operational implication).

3. **Introspection commands reject FQ names.** `/sig grid/cell-at`,
   `/info solver/eliminate`, `/refs grid/cell-at` → `unbound symbol` /
   `unknown symbol`, even when the bare name is imported into `user` (bare
   `/info eliminate` works). `/refs cell-at` from `user` reports "no
   references" although `solver.cl` has 12 call sites — it searches only the
   current module, so there is no way to preview a cascade ("who calls this
   across the project?") before redefining. Also minor: `/sig cell-at` on an
   imported name prints only `; imported from grid/cell-at` without the
   signature.

## Proposed resolution

- Make the `/mod M` turn environment match the environment `M`'s file body
  was compiled in (prelude values + type aliases in scope, alongside the
  module's own imports), or rule explicitly why not and document the FQ
  workaround in `repl/spec.md`.
- Accept FQ `module/name` arguments in `/sig`, `/info`, `/refs`,
  `/source`, `/doc` (the transaction's own reports already print FQ names —
  `; broken: solver/solve — …` — that the user then cannot paste into
  `/info`).
- `/refs` should search all loaded modules (or take a `--all` form): it is
  the natural "preview the affected set" companion to the §18.3 cascade
  report.

## Operational implication / Context

Found during S101 Phase 6a at-scale assessment (/port). With these gaps, the
observed exemplar dev-loop outcomes were:

- Unannotated module-fn redefinitions (`(defn is-solved [g] 42)`) generalize
  (`(Fn [a] Int)`) → T1 downgrade → **no cascade, no report, split world**:
  the REPL call returns 42 while `(solve g)` silently uses the frozen old
  `is-solved` and succeeds. Correct per the amended §10 stage-M design, but
  at scale this is the *common* case, not the edge — nearly every exemplar
  function is unannotated and inference-generalized.
- With the FQ-annotation workaround the transaction fires and the trap UX is
  good (`solver/solve is broken by the redefinition of grid/is-solved: …`),
  but dependent recompilation of file-backed symbols fails (cross-module:
  "definition source unavailable for dependent recompilation"; same-module:
  false type errors `undefined variable: None`/`Some` — the recompile env is
  missing the prelude too). Those are defects/gaps in their own right, routed
  to /qa with repros via the Phase 6a /port report — this FIXME covers the
  interactive-scope half.
