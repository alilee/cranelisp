---
number: 0929
target: /design (backend)
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

## Site state (verified 2026-09-24)

| Site | Current source | Disposition and owner |
|---|---|---|
| `crates/cranelisp-typecheck/src/ownership/fixpoint.rs` parameter seed | residual parameter frames publish no summary; pinned by `a_residual_parameter_frame_publishes_nothing_and_stays_in_the_keyed_set` | **done** (S122) |
| `crates/cranelisp-backend/src/compiler/fn_compiler.rs` dead `variable_types` arm | absent | **done** |
| `crates/cranelisp-backend/src/drop_glue.rs` Vec arm, `unwrap_or(ConcreteType::Int)` | live | located refusal — contract §7.4, `dev` (backend) |
| `crates/cranelisp-backend/src/compiler/context.rs` constructor field read, `unwrap_or(Type::Int)` | live | deleted by the ruled constructor-declaration channel (`CtorField` carries `ConcreteType`) — contract §7.4 |
| Binary/int display-type defaults, `src/pipeline.rs` and `src/repl/commands.rs` `unwrap_or(Type::Int)` | live | grading owed: can a heap-typed result reach these arms with no display type? `design` (int) |

## Remaining obligation

- Dispose the three live sites above.
- Land the NC-2 census with both detection legs; no census test cites this
  filing today.

## Closure

No listed site fabricates a type, and R18 records the census's detection
proof and residual grade.
