# `core.io/timeout` concrete-instantiation intake

## Current disposition

User approved the fix on 2026-09-09. Arch and design attributed the missing
instance to private typecheck mono-recheck function-value harvesting; dev
corrected that producer without changing the stdlib, backend, specification,
public API or ABI. The actual-seam unit was RED before correction and is GREEN
afterward; the typecheck suite passes 899/899.

Final-source nextest `6c976cd1-5232-455c-b82c-d5ba2d53b142` passes the public
timeout subject/control in all three modes, the adjacent constructor-as-value
guard, and public-module maintenance (3/3). Review found no implementation
defect. The further QA-allocated cross-module unit also went RED→GREEN and
passes alongside the original unit (2/2); finding-scoped re-review has no
outstanding finding. Live completion status is in [SPRINT.md](SPRINT.md).

The observations below record the pre-fix intake, not a current failure.

## Confirmed pre-fix symptom

Docs' retained artifact `s121-docs-io-U7nDtm/timeout.cl` imports
`core.io/timeout`, evaluates `(timeout 10 (sleep 1000))`, and matches the
`Option` result.  Under the documented workspace-stdlib `--run` command it
exits 1 during code generation, rather than taking the timer/`None` path and
exiting 0.  The accepted-binary SHA matches the accepted Phase-5 binary, so no
binary-drift explanation is established.  Class: **wrong reject of a concrete
public stdlib operation**, trace `spec/10-io.md` timeout/race semantics plus
`spec/11-stdlib.md` public-module use.

The diagnostic establishes only that a generic value reference named `Some`
reached the existing slotless-template backstop.  It does not establish why its
concrete instance was absent, nor attribute the fault to backend, typecheck,
module compilation, or the prior 0907 defect.  Keep 0907 separate.

`test` established the exact public subject RED through REPL, `--run`, and
`--link` (nextest `051cf648-b56b-4982-b257-adae6ad4e33f`).  The local lambda
mirror is green in all three, but alone changes module home, imports, and
definition context.

`inline-race.cl` (exit 111) proves a small primitive `race`/`bind`/`Pure`
program can run.  It contains neither `core.io`, `sleep`, `Option`, nor a
constructor-as-value reference, so it is a baseline—not a mechanism control.

## Matched evidence and adequacy

`test` retained the unignored permanent e2e RED in the existing
workspace-stdlib-conformance exception.  The exact public-import subject must
expect exit 0 and absence of the codegen error across REPL, run, and link using
the existing workspace-stdlib helpers.

The one bounded matching counterfactual is complete: a test-private complete
stdlib copy changes exactly one `core/io.cl` expression, `map-io Some` to
`map-io (fn [x] (Some x))`, then runs the identical public-import subject.
It is green in REPL, run, and link; the unchanged workspace subject remains
red with the exact backstop in all three (nextest
`c876b99b-1d8f-4c89-be86-85a9936c26f8`).  This proves a form-specific boundary:
in the same `core.io` module context, the bare polymorphic constructor used as
a function value fails concrete `timeout` instantiation while the lambda form
does not.  It does **not** locate the absent-instance cause within typecheck or
backend, or prescribe a repair. This was the evidence supplied for the user's
subsequent fix approval.

This RED/control pair is adequate as a permanent wrong-reject safety fence and
as a detection proof: same subject, one asserted replacement, divergent
outcomes.  It is not a complete timeout acceptance matrix—the timer result is
observed, but loser cancellation is not independently observed here.  The
approved `core.io` self-test restoration remains the proper carrier for that
separate semantic condition.

## Coverage disposition

`stdlib_all_public_modules_compile_and_run` imports `[*]` then returns
`(Pure 0)`. It checks module loadability but never calls/instantiates a public
generic combinator, so it could pass while `timeout$Int` fails.  This is a
specific public-generic-API coverage gap, not a false result.  Its new plan
condition is bounded: a public derived generic combinator that passes a
polymorphic constructor as a value must instantiate and execute concretely in
every user execution face.  It does not claim a repository-wide generic-API
matrix. The approved fix consumes this permanent test and finding-scoped
review; attribution rests on the owning roles' source investigation and unit
RED, not the error text alone.
