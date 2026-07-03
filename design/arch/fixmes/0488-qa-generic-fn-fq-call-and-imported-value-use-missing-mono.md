---
number: 0488
target: /qa
filed_by: /stdlib
filed_at: 2026-07-03
sprint_filed: 101
refers_to: stdlib/collections/vec.cl §vec-flatten, tests/spec_04_expressions.rs::polymorphic_accumulator_fold_does_not_over_unify (adjacent, distinct signature), design/backend/ownership-codegen.md §12.7 (adjacent class), tests/plan/s101-coverage-postmortem.md §cat-3
status: open
---

# Generic fn referenced by FQ call or imported-value-use never reaches codegen — "undefined function/variable"

## Issue

A **generic (polymorphic) function** referenced any way other than a *bare
call* typechecks but fails at codegen — its monomorphised instance never
reaches the consuming turn's codegen batch. Two error signatures, one
suspected class:

**Signature 1 — FQ call position** (`undefined function: <fq>`), 2-line repro,
no stdlib needed:

```
user> (defn iden [x] x)
user> (user/iden 5)
Error: codegen error at 1..10: codegen failed for /: codegen error at 1..10: undefined function: user/iden
```

Same failure FQ-calling any generic stdlib fn (`collections.vec/count`,
`/get`, `/conj`, `/vec-map`, `/vec-reverse` — with or without a prior
import). **Concrete** FQ calls work: `(num.int/abs -3)` ✓,
`(collections.vec/range 0 3)` ✓, concrete `(user/foo 1)` ✓.

**Signature 2 — imported generic fn in value position**
(`undefined variable: <name>`):

```
user> (import [collections.vec [vec-reduce vec-concat]])
user> (vec-reduce vec-concat [] [[1 2] [3]])
Error: codegen error at 12..22: ... undefined variable: vec-concat
```

Also: `(vec-map identity [1 2 3])` after `(import [fn.compose [identity]])`
→ `undefined variable: identity`. The neighbouring cells all WORK:
same-module generic as value (`(vec-map iden [1 2 3])` ✓), imported
*concrete* as value (`(vec-map abs [1 -2 3])` ✓), builtin as value
(`(vec-reduce vec-push [0] [1 2 3])` ✓ — the S101 fix), bare call of the
same imported generic (`(vec-concat [1 2] [3])` ✓, `(identity 5)` ✓).

## Matrix (probed 2026-07-03, HEAD binary, CRANELISP_LIB=stdlib)

| Reference shape | concrete | generic |
|---|---|---|
| bare call, same-module or imported | ✓ | ✓ |
| FQ call (any module, incl. `user/`) | ✓ | ✗ "undefined function" |
| value position, same-module | ✓ | ✓ |
| value position, imported | ✓ | ✗ "undefined variable" |
| value position, builtin (vec family) | ✓ (S101) | — |

## Stdlib collateral

`collections.vec/vec-flatten` is **unusable from user code** — any call
(`(vec-flatten [[1 2] [3]])`, fresh session, only that import) fails
`undefined variable: vec-concat` at the stdlib span (4508..4518): the
stdlib body passes same-module `vec-concat` as a value to `vec-reduce`,
and the monomorphisation at the user turn loses it. `vec-flatten` has no
self-test (`stdlib/collections/vec/test.cl` — /stdlib's gap, self-test
rides the fix in 6b+).

## Addendum (S101 6b probe, 2026-07-03): third signature — composition over a fold-bodied generic

The 6b attempt to simplify `vec-concat` to `(vec-reduce vec-push va vb)`
(builtin-as-value fold, the "viable" matrix cell) surfaced a THIRD
signature and was **reverted** (the loop body stays; see
`stdlib/collections/vec.cl` §vec-concat NOTE):

- **Standalone bare call works** with the fold body:
  `(vec-concat [1 2] [30 40 50])` ⇒ `[1 2 30 40 50]` ✓ (as 6a verified).
- **Composition breaks**: with the fold body, applying ANY imported
  generic over its result fails at the consuming turn's codegen with the
  error attributed to the OUTER fn —
  `(count (vec-concat [1 2] [3 4 5]))` → `undefined function: count`;
  `(get (vec-concat [1 2] [3 4 5]) 2)` → `undefined function: get`.
  Same failure from a stdlib test submodule (`collections.vec.test`).
  Control: `(count (vec-reverse [1 2 3]))` ✓ and `(count [1 2 3])` ✓ —
  composition over LOOP-bodied generics is fine; with the loop body
  restored both composed calls return correctly (5, 3).
- **Inference collateral**: under the fold body, `vec-concat`'s scheme
  degrades — `(vec-concat [1 2] :(Vec Int) [])` reports "ambiguous type"
  (second-arg empty-vec literal no longer pinned by unification; the same
  pin works under the loop body). Possible interplay with the 0344-family
  over-unification guard.
- **Severity sharpened (6b follow-up, 2026-07-03)**: this inference
  collateral is a TYPECHECK-time failure, so with the fold body in place a
  COLD-cache prelude compile (`CRANELISP_LIB=stdlib`, fresh dir) **aborts
  REPL startup entirely** — `module 'prelude' failed: … dependency
  'collections.vec.test' failed: … ambiguous type … bound in
  \`test-vec-concat-empty-right\`` — and the `:(Vec Int) []` annotation
  does NOT cure it (reproduced against a fold-body stdlib copy WITH the
  annotations present). Prelude-compile and direct-module-load paths fail
  identically (no strictness divergence). The LANDED loop-body tree is
  deterministically green on the same probe: 9/9 cold-cache startups +
  3/3 `--no-cache` startups reach the prompt, annotated AND un-annotated
  row variants both compile (the annotations are kept as S84-defensive).
  A parallel /docs cold-start abort report (S101 6b) reproduced only
  against the transient fold-body mid-edit state — snapshot race, not a
  live defect in the landed tree.

Net: the "value position, builtin ✓ (S101)" cell holds only for the
DEFINING module's own compile + bare calls of the containing fn; a
builtin-as-value in a generic's body poisons sibling mono-instance
emission when the containing fn is COMPOSED at a consuming turn. Guard
material: `stdlib/collections/vec/test.cl::test-vec-concat-*` (green on
the loop body, they fail codegen under the fold body).

Distinct from FIXME-0344's failing guard
(`polymorphic_accumulator_fold_does_not_over_unify`): that is a *type
error* from scheme over-unification; these are *codegen* failures after a
clean typecheck (`(vec-reduce + 0 (range 0 101))` ⇒ 5050 works).

## Proposed resolution

/qa authors narrow failing-not-ignored repros (both signatures; the 2-line
FQ repro is free-standing, no stdlib) and isolates per `tests/CLAUDE.md`
§"Isolating Cross-Crate Failures" to identify the resolver (suspect: the
consuming turn's codegen-batch derivation / mono-instance emission — the
same "resolves in typecheck, body never reaches the codegen batch" family
as the S86 DEF-1 re-export note in `stdlib/CLAUDE.md`).

## Operational implication / Context

Likely pre-existing (not S101-caused — the S101 cat-3 sweep covered
*builtin* families only), but **newly load-bearing**: now that vec builtins
work as first-class values, users will immediately pass stdlib HOFs/fns
around, and the imported-generic cell is the first one they hit.

## /qa isolation (S102 Wave 2, 2026-07-03): SEAM ATTRIBUTED — see `tests/plan/0488-isolation.md`

All three signatures attribute to **/dev(typecheck)** — the mono instance is
**never minted** (category (i) of the seam question; fresh-dir `/sig` probes
show no mangled entry under any name after each failing turn; REPL ≡ `--run`
on all three). None attributes to backend `fn_as_value.rs` → **0488 does NOT
ride Wave 11 B3.1**; /sprint schedules typecheck slot(s). Per-signature:

- **(a) FQ call** — pass-4 collection misses FQ-qualified callee heads.
  Same-module FQ: both collector gates exclude it
  (`resolve_terminal_entry_and_home` raw-key probe; the imported-collector's
  `home != current_module` gate). Cross-module FQ: collected, but
  `get_constrained_fn`'s home-probe uses the raw qualified string as a
  symbol-table key → no mint. New RED guard:
  `generic_value_use_mono::generic_fn_cross_module_fq_call_monomorphises`.
- **(b) imported value-use** — `collect_parametric_fn_value_args`'s explicit
  `home == current_module` gate (program.rs:3629) excludes imported generics;
  the fn-value mint call (program.rs:3415) also hard-codes `home: None`.
- **(c) fold-bodied composition** — DISTINCT mechanism: the defining module's
  generalization publishes an over-general template scheme
  (`vconcat : (Fn [a (Vec b)] c)`, result untied) → the inner call's result
  is a free var at the consuming turn → the OUTER site fails pass-4's
  all-args-concrete guard → no rewrite → `undefined function: <outer>`.
  Annotation cure verified (`(vcount :(Vec Int) (vconcat …))` works). This
  root-causes the §Addendum inference collateral. New RED guard (root-cause
  level): `generic_value_use_mono::fold_bodied_generic_template_scheme_ties_params_and_result`.
  Residue: WHERE the unification is lost (0344-guard interplay suspected) —
  unit-tier question for the fixing dev.

Unit-test shapes + owner recommendation: `tests/plan/0488-isolation.md`.
0488 guard count 3 → 5 (+2 green controls); ledger §"Sprint 102 Phase-5
Stage-1 QA-first RED set" Wave-2 addendum.

## /qa guard batch (S101 6b, 2026-07-03): guards LANDED — this file is now redundant as a record

New `tests/generic_value_use_mono.rs`: all THREE signatures reproduce
STDLIB-FREE — (a) `generic_fn_fq_call_monomorphises_like_bare_call` (RED,
`undefined function: user/iden`) + `concrete_fn_fq_call_control` (green);
(b) `imported_generic_in_value_position_monomorphises` (RED, `undefined
variable: iden2`, local fixture module) + same-module/imported-concrete
green controls; (c) `composition_over_fold_bodied_imported_generic_monomorphises`
(RED, `undefined function: vcount` attributed to the OUTER fn — local
`vreduce`/`vconcat`/`vcount` fixture mirroring the stdlib fold shape, with
in-test bare-call green controls). Partial-reduction note recorded in the
test header: (c) is micro-shape-sensitive — a sibling shape with reversed
`if` branch polarity + different helper naming PASSED at probe time; which
micro-detail flips it is unknown. Ledger: `tests/plan/ledger.md` §"Sprint
101 Phase 6a/6b defect set".
