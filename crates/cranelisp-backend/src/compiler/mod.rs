//! Per-function CLIF emission — internal codegen primitives.
//!
//! `FnCompiler` owns a `FunctionBuilder` + `&mut M: Module` and holds all the
//! state needed to compile one function (NOT a 21-parameter function — this
//! addresses the prototype's primary structural debt). One dispatch method per
//! `Expr` variant (`compile_int_lit`, `compile_let`, …).
//!
//! These types (`FnCompiler`, `CompileContext`, `MatchContext`)
//! are `pub` codegen primitives reached only via the
//! `compile_to_module` free function in production; the `pub` exists for
//! test-side AST-fragment compilation. The GOT-target resolution helpers
//! `resolve_func_arity` / `resolve_got_target` / `got_data_symbol_name` are the
//! canonical per-symbol-table probing primitives (no equivalent at the
//! `cranelisp-types` boundary).
//!
//! **Forbidden pattern.** Every primitive — including `not`, `+`, `=`, and the
//! arithmetic/comparison operators — goes through the SAME GOT-indirect
//! dispatch path as any user function. Inline substitution (`primitives_inline`)
//! is a name-keyed shortcut over that path, never a parallel dispatch; backend
//! has no trait knowledge and MUST NOT key on `(trait, method, type)` triples.


// Codegen submodules — narrowed to `pub(crate)` in S75 W3 (they export no
// items externally; codegen lives in `impl FnCompiler` blocks inside them and
// no out-of-crate consumer exists).
pub(crate) mod apply;
pub(crate) mod control_flow;
pub(crate) mod literals;
pub(crate) mod match_codegen;
pub(crate) mod trace_codegen;
pub(crate) mod vec_codegen;

// Decomposition submodules (S87 Wave 5b). The module-internal codegen
// concerns are split into cohesive files; the hub re-exports their items so
// the in-crate import paths (`crate::compiler::X`, `super::X`) keep resolving.
mod context;
mod extern_call;
mod fn_compiler;
mod rc_emission;
mod resolution;

use cranelisp_types::Type;

// Re-exports preserving the in-crate `crate::compiler::*` / `super::*` paths
// that the sibling codegen modules, `lib.rs`, `jit.rs`, `cache::object`, and
// the test siblings already import. `CompileContext` is the ONLY pub-to-boundary
// item under `compiler::` (verified against `public-api.txt`); it MUST re-export
// `pub` so the public API path is preserved. Everything else is `pub(crate)`.
pub use context::CompileContext;
pub(crate) use context::CtorMeta;
pub(crate) use fn_compiler::{FnCompiler, MatchContext};
pub(crate) use rc_emission::{
    collect_var_ids_from_type, find_var_type_in_expr, signature_heap_category,
    substitute_type_inline,
};
pub(crate) use resolution::{
    got_data_symbol_name, inner_fn_discriminator_for, resolve_extern_target,
    resolve_func_arity, resolve_got_target, resolve_platform_effect_target,
    resolve_poll_effect_target, resolve_vec_query_primitive,
};

/// Information about a single function to be traced by `(trace ...)`.
///
/// **Backend-internal** (S76 FIXME 0255, `tracing.md` §5). Discovery moved into
/// backend trace-codegen — `trace_codegen::discover_traced_fns` builds these by
/// iterating `symbol_tables` directly. They no longer cross the int↔backend
/// boundary, so this type is `pub(crate)` and the `CompileContext::traced_fns`
/// field is gone. Per-param/result display descriptors are baked at
/// wrapper-compile time (`trace_codegen`), not carried on this struct.
#[derive(Debug, Clone)]
pub(crate) struct TracedFnInfo {
    /// Fully-qualified function name (e.g., "user/fact").
    pub name: String,
    /// Module that defines this function (e.g., "user", "primitives"). The
    /// grouping key for `compile_trace`, and used to reference the module's GOT
    /// **data symbol** (`got_data_symbol_name`) via relocation in both JIT and
    /// object mode — the GOT base is never baked as a compiling-process
    /// `iconst` (FIXME 0275).
    pub module_path: cranelisp_types::ModuleFullPath,
    /// GOT slot index for this function. At runtime the wrapper reaches the
    /// ORIGINAL implementation by loading `got_base[slot]` BEFORE the swap (into
    /// a per-group originals buffer); the address is never baked at codegen.
    pub got_slot: usize,
    /// Number of parameters.
    pub arity: usize,
    /// Static parameter types (from function's type scheme).
    pub param_types: Vec<Type>,
    /// Static return type (from function's type scheme).
    pub result_type: Type,
}

#[cfg(test)]
mod tests;
