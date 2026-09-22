# Sprint 117 QA plan — failed-turn recovery rows retained for ACT-0958

> **Retained dated record (S122 consolidation).** Only §3.3 remains, under its
> original number, because [ACT-0958](../../sprints/actions/ACT-0958-rearm-failed-turn-recovery-coverage.md)
> cites it as the allocation whose requirements must not be weakened. The
> current allocation for the same condition is the Q2 row and the D1
> private-seam substitution in [S122 evidence](s122-evidence-delta.md#conditions-by-source-stream);
> this record retires when ACT-0958 closes or re-points its citation. The
> S117 exit verdict, §3.1/§3.2/§3.4 rows (all landed in `tests/spec_07_traits.rs`,
> `tests/spec_09_macros.rs`, `tests/spec_11_stdlib.rs` and
> `tests/repl_introspection.rs`), the §5 module-matrix allocation and the §6
> S115 band reconciliation are in Git: `git show 7b1220c7:tests/plan/s117-test-plan.md`.
> Nothing here is current status.

### 3.3 Failed-turn transaction and diagnostics

| ID | Required assertion |
|---|---|
| TX-1 | In one REPL session, after a genuine codegen failure, evaluating `42` returns `:primitives/Int 42` and does not repeat the prior error or span. |
| TX-2 | After the failure, an unrelated function is defined and called successfully: registration, typecheck, batch derivation, GOT publication and evaluation all recover. |
| TX-3 | The symbol whose compile failed is not callable as stale or partial code and does not contaminate `/info`; a clean redefinition of that symbol then compiles and runs. |
| TX-4 | The first diagnostic names the actual failing definition or module context, never an incidental expression head such as `/`. |

The S117 rows required these observations through the public binary with a
public failure trigger. The user's 2026-09-10 D1 approval substituted a
root-private failing compile operation at the prepare→compile→publish seam,
with public successful-turn controls, because no stable legitimate public
codegen-failure trigger exists. The assertions above are unchanged by that
substitution; their layer moved.
