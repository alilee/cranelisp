---
number: 0296
target: /qa
filed_by: /dev
filed_at: 2026-06-08
sprint_filed: 76
refers_to: tests/regression.rs (d6_exemplar_* + wave6_exemplar_solver_full_run), design/arch/fixmes (former 0279/0295, now deleted — resolved)
status: open
---

# Residual exemplar-solver RUNTIME stack overflow — distinct defect, NOT the 0279 cyclic-subst root

## Issue

FIXMEs 0279/0295 (the cross-module polymorphic-import cyclic-substitution
non-termination) are RESOLVED in S76 Wave 4c. Root cause: HM instantiation built
an identity self-map `{id -> Var(id)}` when the per-session `next_id` counter had
not been advanced past an imported scheme's bound TypeIds, making
`cranelisp_types::types::apply` chase `id -> Var(id) -> …` forever. Fixed at the
construction site in typecheck (`fresh_instantiation_subst` re-rolls fresh ids so
no self-map is ever built) plus a defensive occurs-guard in `apply`.

0279 predicted its fix would "clear the d6/wave6 overflow cluster." It cleared the
**compile-time** members (the `priority-worker-0` overflows): `d6_grid_wrapper_cow`,
`d6_solve_recursive_adt`, `d6_vec_cow_adt_loop`, `d6_vec_cow_int_loop`,
`d6_exemplar_make_grid_only`, `d6_exemplar_eliminate_from_peers`,
`wave6_run_tests_batched_html` all PASS now (regression suite 57/62, up from the
pre-fix count). The `regression_0279_*` repro itself is green.

**Five tests remain FAILING with a DIFFERENT root:**
`d6_exemplar_solve_all_dots`, `d6_exemplar_propagate_only`,
`d6_exemplar_propagate_single_pass`, `d6_exemplar_solve_minimal_puzzle_no_io`,
`wave6_exemplar_solver_full_run`. These overflow on the **`main` thread at
RUNTIME** (`thread 'main' has overflowed its stack`), NOT on `priority-worker-0`
at compile/typecheck time. This is runtime stack depth in the executing Sudoku
solver (deep recursion / RC drop-glue depth on nested ADTs), unrelated to the
typecheck-time cyclic-subst that was fixed. They were failing at base commit
f58765a and are unaffected by the instantiation fix (a typecheck-only change
cannot move a runtime-thread overflow).

## Proposed resolution

Re-triage these 5 as a distinct runtime-recursion defect (owner likely
/dev-backend or /dev-runtime once reduced). Per the QA reduction protocol, reduce
the exemplar solver to the minimal recursive shape that overflows the main thread
at runtime, and re-point the failing regression tests at that root. Do NOT
re-attach them to the (now-resolved) cyclic-subst FIXME — conflating the two is
what 0279's "strong corollary" framing risked.

## Operational implication / Context

The S76 Wave-4c gate blocker (compile-time prelude overflow + 5 `spec_10_io::bind_*`
regressions) is CLEARED. These 5 residual exemplar tests are a separate, pre-existing
runtime defect that should carry its own FIXME and reduction, not block the
cyclic-subst resolution.
