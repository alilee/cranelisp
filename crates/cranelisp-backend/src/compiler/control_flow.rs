// Control flow, binding, and closure codegen — module hub.
//
// The cohesive codegen clusters live in sibling sub-modules, each an
// `impl FnCompiler` block on the shared struct:
//   - `let_if`       — sequential + lenient `let` binding and `if` branch-merge
//   - `par_bind`     — IO ParBind node + continuation closure emission
//   - `lambda`       — closure compilation: site alloc, inner-fn body, drop glue
//   - `fn_as_value`  — named-fn / trait-method value wrappers + auto-curry
//   - `free_vars`    — pure free-variable analysis over `MonoExpr`
//   - `sparkability` — lenient-eval decision pass
//   - `capture_rc`   — the single-source capture-RC-inc helper
//
// This hub keeps only the cross-submodule bridge re-exports. (The former
// `emit_extern_call_1` IVar-plumbing helper was folded into the arity-generic
// `compiler::extern_call::emit_extern_call` — audit F5 dedup.)

// The sub-modules reach `FnCompiler` via `super::FnCompiler` (children resolve a
// parent's private `use` items); keep the hub as that single resolution point.
use super::FnCompiler;

mod capture_rc;
mod dependent_spark;
mod fn_as_value;
mod free_vars;
mod lambda;
mod let_if;
mod par_bind;
mod sparkability;

// Cross-submodule bridges: these names are referenced by the sub-modules via
// `super::…` (children can reach a parent's private `use` items). Re-exported
// `pub(crate)` so the hub is a single resolution point and the imports are not
// flagged unused.
pub(crate) use capture_rc::emit_capture_inc_into;
pub(crate) use free_vars::find_free_vars;
// `find_sparkable_args` + `LENIENT_DISABLED` are reached by `compiler::apply`
// (the apply-argument lenient pre-pass, lenient-eval.md §4.4) through this hub —
// the `sparkability` submodule itself is private to `control_flow`. The unit
// tests reach `find_sparkable_args` via `super::` on the same re-export.
pub(crate) use sparkability::{find_sparkable_args, LENIENT_DISABLED};
// Only the `sparkability_tests` sibling reaches this via `super::`.
#[cfg(test)]
pub(crate) use sparkability::find_sparkable_bindings;

#[cfg(test)]
mod sparkability_tests;

#[cfg(test)]
mod par_codegen_tests;

#[cfg(test)]
mod poll_codegen_tests;
