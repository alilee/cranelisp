---
number: 0929
target: /design (int)
filed_by: /qa
filed_at: 2026-07-27
sprint_filed: 119
refers_to: design/arch/safety-invariants.md §4;
  design/backend/non-concrete-release-contract.md §7.4;
  crates/cranelisp-backend/src/drop_glue.rs;
  crates/cranelisp-backend/src/compiler/context.rs;
  src/pipeline.rs;
  src/repl/commands.rs;
  tests/plan/s119-test-plan.md §3.7
status: open
---

# R18 fabrication census: the remaining discard-and-substitute sites

Safety-register row R18 (no fabricated concreteness) carries the per-site
grades, owners and the two model refusal spellings
(`crates/cranelisp-typecheck/src/program/support.rs` `ViewBuildError::NotConcrete`
and `crates/cranelisp-types/src/heap.rs::ctor_field_concrete_types`). This
filing is the citation anchor for the NC-2 fabrication census allow-list
until each site is disposed.

`ConcreteType` variants stay public; enforcement is the NC-2 census (pinned
allow-list, every entry citing an open filing, a new site RED in its own
change-set), with R18's residual graded asserted-with-a-named-falsifier once
the census lands with its detection proof (arch ruling, S119).

## Site state (verified 2026-09-24; backend rows re-read by `qa` 2026-11-19)

| Site | Current source | Disposition and owner |
|---|---|---|
| `crates/cranelisp-typecheck/src/ownership/fixpoint.rs` parameter seed | residual parameter frames publish no summary; pinned by `a_residual_parameter_frame_publishes_nothing_and_stays_in_the_keyed_set` | **done** (S122) |
| `crates/cranelisp-backend/src/compiler/fn_compiler.rs` dead `variable_types` arm | absent | **done** |
| `crates/cranelisp-backend/src/drop_glue.rs` Vec arm, `unwrap_or(ConcreteType::Int)` | absent at `f8c55626`; a refusal since `1d965ed5` | **done** (S124) |
| `crates/cranelisp-backend/src/compiler/context.rs` constructor field read, `unwrap_or(Type::Int)` | absent at `f8c55626`; a refusal since `24c42430` (packet row D1) | **done** (S124) |
| Binary/int display-type defaults, `src/pipeline.rs` and `src/repl/commands.rs` `unwrap_or(Type::Int)` | live at `ed6f4d87` (`execute_compiled_expr`, `typecheck_only`) | **designed** 2026-11-20 by `design` (int): [result owner §4.3.1](../../int/result-owner.md#431-the-observed-type-has-no-default) removes both defaults. The executed site's chain ends in the arm's scheme result, which is total, and the `/type` site's absence is a located error. Source does not show that the arm is unreachable, so it had no grade. `dev` (`src/`) owes the change and its module rows |

## Remaining obligation

- Land the binary's display-type correction (`dev`(`src/`), designed in
  result owner §4.3.1). No backend production site remains: the only
  `unwrap_or(Type::Int)` in the crate is in `test_support.rs`.
- Land the NC-2 census with both detection legs; no census test cites this
  filing today.

## Closure

No listed site fabricates a type, and R18 records the census's detection
proof and residual grade.
