---
number: 0279
target: /qa
filed_by: /sprint
filed_at: 2026-06-06
sprint_filed: 76
refers_to: stdlib/io/monad.cl, tests/CLAUDE.md §"Isolating Cross-Crate Failures", src/worker.rs (priority-worker compile path), design/arch/macro-availability-model.md §0
status: open
---

# Compiler stack overflow on `stdlib/io/monad.cl` — blocks the production prelude; needs minimal repro

## Issue

Unmasked by the S76 layered repairs (0265 trait sigs → 0263/0264 fixtures →
0277 vec entries): with those landed, the production prelude now reaches
`io.monad` and the COMPILER aborts — `thread 'priority-worker-0' has
overflowed its stack`.

Bisection so far (0277 agent, 2026-06-06): `collections.vec` + all trait/
string/option/result/threading/list/control/defs modules load clean;
**`stdlib/io/monad.cl` alone reproduces** (added by itself to a working
prelude, and even in isolation). `RUST_MIN_STACK` does not help; no
codegen-trace output before the abort → the unbounded recursion is at
typecheck or macro-expansion. The module imports `[primitives [Pure]]` +
`[macros […]]` and defines `pure`/`do`/`bind!` over `primitives/bind`.

This is the last known blocker on the full production prelude (gates the
stdlib-dependent e2e suites + the exemplar).

## Proposed resolution

Per the QA reproduction protocol: reduce `io.monad` to the minimal form that
overflows — candidate axes: the `do`/`bind!` defmacro clauses (S76 W-Macro
recognition path — a recognition/expansion cycle?), the `pure` name (also a
`DefKind` on `primitives/Pure`-adjacent?), the higher-order `bind` scheme
(recursive `(IO a)` unification?), quasiquote nesting. Small repro → small
surface; `CRANELISP_MACRO_TRACE=1` / `CRANELISP_INFER_TRACE=1` may show the
loop before the abort. The repro joins the suite failing-not-ignored
(`// spec:` the relevant §9/§10 row) and the triage names the owning compiler
skill (/typecheck, /frontend, or /int W-Macro) with the repro, not the
symptom.

## /qa reduction result + triage (S76 W3 — 2026-06-07)

REDUCED to a 2-file / 3-line repro (the fix-axes in Proposed resolution were
ALL ruled out as the cause):

```
util.cl:  (defn f [x] x)            ; polymorphic identity :: (Fn [a] a)
main.cl:  (import [util [f]])
          (defn main [] (f 9))      ; monomorphise f at Int
```

Reduction path (each step confirmed the overflow still reproduces, then the
next strip):

1. The `do`/`bind!` defmacro clauses are NOT the cause — a recursive `do` macro
   DEFINED-but-unused does not overflow; a non-recursive macro does not.
2. `pure` (the imported fn) is the trigger, but NOT via its name or the `Pure`
   ctor: imported `(defn lift [x] (Pure x))` overflows; imported
   `(defn pure [x] x)` overflows.
3. The razor: an imported one-arg fn returning a CONSTANT does NOT overflow; an
   imported one-arg fn returning its PARAMETER (POLYMORPHIC `(Fn [a] a)`) DOES.
   A same-module polymorphic identity does NOT overflow — the cross-module
   IMPORT is load-bearing.

**Root cause (lldb backtrace at the overflow):** unbounded recursion in
`cranelisp_types::types::apply` at `crates/cranelisp-types/src/types.rs:230` —
`apply(subst, Var(id))` chases `id -> mapped` where the substitution maps a type
var to a type containing itself (a cyclic / occurs-check-violating `Subst`, same
`ty` pointer across all frames). No INFER_TRACE/MACRO_TRACE/MODULE_TRACE output
precedes the abort (the recursion is in `apply`, not in unification stepping).

**Triage verdict — owning skill: /typecheck.** The defect is the CONSTRUCTION
of the cyclic substitution when instantiating/monomorphising a cross-module
polymorphic scheme (occurs-check / scheme instantiation / subst composition).
`apply` in cranelisp-types is merely where non-termination manifests; the fix is
in typecheck's cross-module scheme handling, NOT in `apply`.

Repro landed FAILING: `tests/regression.rs::regression_0279_cross_module_polymorphic_import_monomorphisation`
(`// spec: spec/08-modules.md §8.3`; `// FIXME(/typecheck)`; 20s-bounded so the
abort is a non-success exit, not a suite hang). PLAN.md row R1. Strong corollary:
the pre-existing `d6_exemplar_*` / `wave6_*` regression overflows are very likely
the SAME `apply` cyclic-subst bug (cross-module polymorphism in the exemplar) —
0279's fix should clear that cluster.

## Operational implication / Context

S76 Wave 3/4 (the repro; the fix follows triage — in-sprint if small, else
carried with the repro as the durable record). Until resolved, production-
stdlib suites stay red on prelude load — distinguish this class from the
cleared fixture classes in the Wave-4 ledger.
