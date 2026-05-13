// Pipeline: shared compilation functions used by the v4 pipeline.
//
// This module provides:
// - Module file resolution
// - Expression compilation and execution (REPL eval)

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use cranelisp_types::{ErrorLocation, 
    CranelispError, ModuleFullPath,
    Span, Type,
};

// ---------------------------------------------------------------------------
// Module file resolution
// ---------------------------------------------------------------------------

/// Resolve a module name to a `.cl` file path.
///
/// Search order per spec §8.11.2:
/// 1. Project root — `{project_root}/{name}.cl`
/// 2. Lib directories — `{lib_dir}/{name}.cl` for each lib dir, in order
///
/// Tier 1 (submodule of current module) is handled by the caller — submodules
/// are already registered in the TypeChecker via `(mod name)` and don't need
/// file search.
pub fn resolve_module_file(
    module: &ModuleFullPath,
    project_root: &Path,
    lib_dirs: &[PathBuf],
) -> Option<PathBuf> {
    let relative = format!("{}.cl", module.as_ref().replace('.', "/"));

    // Tier 2: project root.
    let root_candidate = project_root.join(&relative);
    if root_candidate.is_file() {
        return Some(root_candidate);
    }

    // Tier 3: lib directories.
    for dir in lib_dirs {
        let candidate = dir.join(&relative);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Expression compilation (REPL eval path)
// ---------------------------------------------------------------------------

/// Compile the current module's `__expr` entry, execute it, and return
/// `(value, type)`.
///
/// Sprint 57 Wave 2 G6: the `program: &Program` fallback parameter is gone.
/// Wave 0 registers `__expr` on the current module's symbol table as a
/// synthetic zero-arg `Defn` with `ast: Some(_)`; this is the single source
/// of truth for the expression body (and carries the post-pass resolution
/// annotations that the pre-annotation program lacked). Callers no longer
/// pass a `&Program`.
///
/// Sprint 57 Wave 6 (IO-path SIGBUS fix): when the `__expr`'s inferred type
/// is `IO a`, the raw IO pointer returned by the compiled wrapper is forced
/// through `run_io_trampoline` *inline* — i.e. before the per-eval `Jit`
/// drops. The IO tree may carry heap closures whose `code_ptr`s point into
/// this JIT's mmap'd pages (raw fn pointers, not GOT-indirect). Letting
/// `jit` drop with an outstanding, un-trampolined IO value would invalidate
/// those closure pointers via Decision 31's `impl Drop for Jit`
/// (`JITModule::free_memory()`); a caller-side `run_io_trampoline(value)`
/// then SIGBUSes dispatching into freed pages. Forcing the tree here
/// consumes every closure in the IO while its code is still live, then
/// returns the final unwrapped inner value with unwrapped type — mirroring
/// `CompilerSession::trampoline` for the batch path. See `tests/io_minimal.rs`
/// for the minimal reproducer cluster.
#[allow(clippy::too_many_arguments)]
pub fn compile_and_execute_expr(
    jit_symbols: &[(String, *const u8)],
    got_data_defs: &[(String, *const u8)],
    display: Option<&cranelisp_types::DisplayInfo>,
    traced_fns: &[cranelisp_backend::compiler::TracedFnInfo],
    trace_extra_symbols: &[(String, *const u8)],
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    current_module: ModuleFullPath,
) -> Result<(i64, Type), CranelispError> {
    // Pull the annotated expression body from the symbol-table entry for
    // `__expr`. Wave 0 registers it as a synthetic defn with
    // `ast: Some(...)`. The symbol-table body carries the post-pass
    // resolution annotations (SigDispatch for Overloaded-base calls,
    // auto-curry resolutions) that the pre-annotation program lacked.
    let expr_owned: cranelisp_types::Expr = symbol_tables
        .get(&current_module)
        .and_then(|t| match t.get("__expr") {
            Some(cranelisp_types::ModuleEntry::Def { ast: Some(defn), .. }) => {
                Some(defn.body().clone())
            }
            _ => None,
        })
        .ok_or_else(|| CranelispError::CodegenError {
            message: "no `__expr` entry found in current module".into(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
    let expr = &expr_owned;

    // Get the type from display info or from the AST node's inferred_type.
    let ty = display
        .map(|d| d.ty.clone())
        .or_else(|| expr.inferred_type().cloned())
        .unwrap_or(Type::Int);

    if traced_fns.is_empty() {
        use cranelisp_types::{ErrorLocation, Defn, DefnVariant, Symbol, Visibility};

        // Decision 23 (Wave 2 follow-on): per-module GOT slabs are registered
        // through the JIT's symbol-lookup table — the symbol address IS the
        // slab base, no extra pointer-cell indirection. Fold `got_data_defs`
        // into `extra_symbols` so `JITBuilder::symbol()` resolves
        // `__cranelisp_got_{M}` directly to `GotTable.base_ptr()`.
        let mut extra_syms: Vec<(&str, *const u8)> = jit_symbols
            .iter()
            .map(|(name, ptr)| (name.as_str(), *ptr))
            .collect();
        for (name, ptr) in got_data_defs {
            extra_syms.push((name.as_str(), *ptr));
        }
        // Sprint 66 Wave 3a-γ: register int-owned intrinsics unconditionally
        // at JIT setup (see FIXME 0178 + worker::inline_jit_codegen_for_names
        // for the rationale). These are intrinsics per
        // `design/arch/facades/intrinsics.md` — uniform dispatch through
        // `JITBuilder::symbol()`, no conditional gating.
        for (name, ptr) in crate::session_v4::int_intrinsics() {
            extra_syms.push((name, ptr));
        }

        let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_syms)?;
        jit.declare_intrinsics()?;

        let wrapper_name = Symbol::from("__repl_expr__");
        // Use a synthetic wrapper span that nests the expr span so the
        // typecheck's pre-eval resolution annotations (keyed by expr.span())
        // survive through codegen.
        let wrapper_span = expr.span();
        let wrapper_defn = Defn {
            name: wrapper_name.clone(),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: expr.clone(),
                span: wrapper_span,
            }],
            visibility: Visibility::Public,
            span: wrapper_span,
        };

        let func_ids = jit.declare_functions(&[&wrapper_defn])?;
        let empty_arities: HashMap<Symbol, usize> = HashMap::new();

        let compile_ctx = jit.build_compile_context(
            &func_ids,
            &empty_arities,
            symbol_tables,
            current_module.clone(),
        );

        jit.compile_defn(&wrapper_defn, compile_ctx)?;
        let code_ptr = jit.finalize_and_get_ptr(&wrapper_name, 0)?;

        // SAFETY: compiled code was just generated and finalized by our JIT.
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
        // Clear any stale error before the JIT call.
        let _ = cranelisp_runtime::panic::take_runtime_error();
        let raw_value = func();

        // Check thread-local error flag (set by runtime_panic in JIT code).
        if let Some(msg) = cranelisp_runtime::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime error: {msg}"),
                location: ErrorLocation::from_span(expr.span()),
            });
        }

        // Sprint 57 Wave 6: if the wrapper returned an IO value, trampoline
        // it *now* — while `jit` is still live — and return the unwrapped
        // inner value. See function docstring for the full rationale.
        let (value, ty) = unwrap_io_inline(raw_value, ty);

        // `jit` drops here. Safe: if IO, we trampolined; otherwise the
        // callee returned a non-code value. No fn pointer derived from
        // `jit` is reachable from `value`.
        drop(jit);
        Ok((value, ty))
    } else {
        let (value, ty) = compile_and_execute_expr_with_trace(
            jit_symbols, got_data_defs, expr, traced_fns, trace_extra_symbols,
            symbol_tables, current_module.clone(),
            ty,
        )?;
        Ok((value, ty))
    }
}

/// If `ty` is an `IO a` type, force the IO tree rooted at `raw_value` via
/// `run_io_trampoline` and return `(inner_value, a)`. Otherwise return
/// `(raw_value, ty)` unchanged.
///
/// This MUST be called before the per-eval `Jit` drops (see
/// `compile_and_execute_expr` docstring). Mirrors the IO-aware post-call
/// handling in `CompilerSession::trampoline` at `src/session_v4.rs`.
///
/// Decision 24 (consuming convention): `run_io_trampoline` is non-consuming
/// of its input tree — it walks the caller's Pure/Effect/Bind/Par nodes
/// read-only. The Rust-side boundary (this function) owns the tree and MUST
/// release it via `drop::consume_io_tree` after the trampoline returns.
/// Without this follow-up call, the outer caller-tree nodes (Bind/Pure +
/// continuation closures) leak — the O(N) Wave-1-review Condition-6
/// regression. This pairing mirrors the internal structure of the extern
/// `cranelisp_run_io` entry point (see
/// `crates/cranelisp-runtime/src/io.rs::cranelisp_run_io`).
fn unwrap_io_inline(raw_value: i64, ty: Type) -> (i64, Type) {
    if ty.is_io() {
        // SAFETY: `raw_value` is either a heap pointer to an IO node (when
        // the compiled expression built one) or 0 on early return. The
        // trampoline tolerates null-ish inputs by dereferencing the tag
        // field; a non-IO value here would indicate a typechecker bug, not
        // a safety bug in this function. Behaviour mirrors
        // `CompilerSession::trampoline`.
        let inner_value = cranelisp_runtime::run_io_trampoline(raw_value);
        // Decision 24: release the caller's tree. `consume_io_tree`
        // transitively walks Pure/Effect/Bind/Par and dec's every
        // heap-typed sub-ref (including continuation closures still owned
        // by Bind nodes). Intermediate nodes produced *inside* the
        // trampoline by continuations were already released there via
        // `dec_shallow_io` — so this final walk is not a double-free.
        cranelisp_runtime::drop::consume_io_tree(raw_value);
        let inner_type = ty.io_inner_type();
        (inner_value, inner_type)
    } else {
        (raw_value, ty)
    }
}

#[allow(clippy::too_many_arguments)]
fn compile_and_execute_expr_with_trace(
    jit_symbols: &[(String, *const u8)],
    got_data_defs: &[(String, *const u8)],
    expr: &cranelisp_types::Expr,
    traced_fns: &[cranelisp_backend::compiler::TracedFnInfo],
    trace_extra_symbols: &[(String, *const u8)],
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    current_module: ModuleFullPath,
    ty: Type,
) -> Result<(i64, Type), CranelispError> {
    use cranelisp_types::{ErrorLocation, Defn, DefnVariant, Symbol, Visibility};

    let mut extra_syms: Vec<(&str, *const u8)> = jit_symbols
        .iter()
        .map(|(name, ptr)| (name.as_str(), *ptr))
        .collect();
    for (name, ptr) in trace_extra_symbols {
        extra_syms.push((name.as_str(), *ptr));
    }
    // Decision 23 (Wave 2 follow-on): per-module GOT slabs are registered via
    // the JIT's symbol-lookup table — the symbol address IS the slab base.
    for (name, ptr) in got_data_defs {
        extra_syms.push((name.as_str(), *ptr));
    }
    // Sprint 66 Wave 3a-γ: int-owned intrinsics — unconditional registration
    // (see FIXME 0178). Mirror of `compile_and_execute_expr` above.
    for (name, ptr) in crate::session_v4::int_intrinsics() {
        extra_syms.push((name, ptr));
    }

    let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_syms)?;
    jit.declare_intrinsics()?;

    let wrapper_name = Symbol::from("__repl_expr__");
    let wrapper_defn = Defn {
        name: wrapper_name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            param_annotations: vec![],
            body: expr.clone(),
            span: expr.span(),
        }],
        visibility: Visibility::Public,
        span: expr.span(),
    };

    let func_ids = jit.declare_functions(&[&wrapper_defn])?;
    let empty_arities: HashMap<Symbol, usize> = HashMap::new();

    let mut compile_ctx = jit.build_compile_context(
        &func_ids,
        &empty_arities,
        symbol_tables,
        current_module.clone(),
    );

    compile_ctx.traced_fns = Some(traced_fns);

    jit.compile_defn(&wrapper_defn, compile_ctx)?;
    let code_ptr = jit.finalize_and_get_ptr(&wrapper_name, 0)?;

    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
    // Clear any stale error before the JIT call.
    let _ = cranelisp_runtime::panic::take_runtime_error();
    let raw_value = func();

    // Check thread-local error flag (set by runtime_panic in JIT code).
    if let Some(msg) = cranelisp_runtime::panic::take_runtime_error() {
        return Err(CranelispError::CodegenError {
            message: format!("runtime error: {msg}"),
            location: ErrorLocation::from_span(expr.span()),
        });
    }

    // Sprint 57 Wave 6: trampoline IO inline while `jit` is still live.
    // See `compile_and_execute_expr` docstring for the full rationale.
    let (value, ty) = unwrap_io_inline(raw_value, ty);
    drop(jit);
    Ok((value, ty))
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------
//
// Sprint 57 Wave 6: lock in the IO-unwrap invariant. The larger
// integration-level SIGBUS reproducer lives in `tests/io_minimal.rs`; these
// unit tests verify the pipeline-level invariant directly.

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{FQTypeName, TypeName};

    fn io_int_type() -> Type {
        Type::ADT(
            FQTypeName::new(
                ModuleFullPath::from("primitives"),
                TypeName::from("IO"),
            ),
            vec![Type::Int],
        )
    }

    /// Sprint 57 Wave 6 (IO-path SIGBUS fix): non-IO types flow through
    /// `unwrap_io_inline` unchanged. This is the baseline — only IO values
    /// incur the trampoline cost, so non-IO REPL eval results (the common
    /// case) pay nothing for the fix.
    #[test]
    fn unwrap_io_inline_leaves_non_io_unchanged() {
        let (value, ty) = unwrap_io_inline(42, Type::Int);
        assert_eq!(value, 42);
        assert_eq!(ty, Type::Int);

        let (value, ty) = unwrap_io_inline(1, Type::Bool);
        assert_eq!(value, 1);
        assert_eq!(ty, Type::Bool);
    }

    /// Sprint 57 Wave 6 (IO-path SIGBUS fix): when an IO-typed expression is
    /// passed in, the type is unwrapped to the inner `a`. Wrapping this in
    /// a unit test makes the fix's external contract visible: after
    /// `compile_and_execute_expr` returns for an IO expression, the caller
    /// sees a non-IO type and a fully-reduced inner value — the per-eval
    /// `Jit` is safe to drop. Regression guard for the
    /// `tests/io_minimal.rs::minimal_3_bind_pure_lambda_trampoline_after_eval_sigbus`
    /// cluster: if this test fails (returns IO type), the invariant has
    /// regressed and the minimal integration tests will SIGBUS again.
    #[test]
    fn unwrap_io_inline_strips_io_type_for_pure_node() {
        // Build a bare Pure(42) node at the runtime boundary. Pure has no
        // closure, so trampolining it is safe here (no JIT dependency) —
        // this exercises the IO-stripping logic in isolation from the JIT
        // lifecycle concern that motivates the fix.
        use cranelisp_runtime::alloc_with_rc;
        const TAG_OFFSET: isize = 16;
        const FIELD_0_OFFSET: isize = 24;
        const IO_TAG_PURE: i64 = 0;

        let base = alloc_with_rc(16) as i64; // tag(8) + field0(8)
        unsafe {
            *((base + TAG_OFFSET as i64) as *mut i64) = IO_TAG_PURE;
            *((base + FIELD_0_OFFSET as i64) as *mut i64) = 42;
        }

        let (value, ty) = unwrap_io_inline(base, io_int_type());

        // Type was unwrapped: caller sees `Int`, not `IO Int`.
        assert_eq!(ty, Type::Int, "expected unwrapped Int, got {ty:?}");
        // Value was the trampolined inner, not the IO node pointer.
        assert_eq!(value, 42, "expected trampolined inner 42, got {value}");
        assert_ne!(
            value, base,
            "unwrap_io_inline must NOT leak the heap-IO pointer to caller"
        );

        // Sprint 57 Wave 6 (Decision 24 fix): `unwrap_io_inline` is a
        // consuming Rust boundary — it MUST release the caller's tree via
        // `consume_io_tree` after the non-consuming trampoline walk. If a
        // future edit drops the `consume_io_tree` call, this allocation
        // would leak and the QA-balance tests (g8_io_trampoline_rc_balanced,
        // g8_rc_balance_bind_chain) would regress. Because `unwrap_io_inline`
        // already owns the consume, there is nothing left for the caller to
        // dec.
    }

    /// Sprint 57 Wave 6 (Decision 24 fix): `unwrap_io_inline` must balance
    /// alloc/dealloc on the IO path. `run_io_trampoline` is non-consuming,
    /// so `consume_io_tree` must release the outer caller-tree nodes
    /// (Pure/Effect/Bind/Par + continuation closures). Regression guard for
    /// the g8_io_trampoline_rc_balanced / g8_rc_balance_bind_chain failures.
    /// If someone drops the `consume_io_tree` call, this test flips red.
    #[test]
    fn unwrap_io_inline_rc_balanced_for_pure_node() {
        use cranelisp_runtime::alloc_with_rc;
        const TAG_OFFSET: isize = 16;
        const FIELD_0_OFFSET: isize = 24;
        const IO_TAG_PURE: i64 = 0;

        let allocs_before = cranelisp_runtime::alloc_count();
        let deallocs_before = cranelisp_runtime::dealloc_count();

        // Build a bare Pure(7) node and hand it to `unwrap_io_inline`.
        // The only heap alloc in-scope is this Pure node — `unwrap_io_inline`
        // must release it.
        let base = alloc_with_rc(16) as i64;
        unsafe {
            *((base + TAG_OFFSET as i64) as *mut i64) = IO_TAG_PURE;
            *((base + FIELD_0_OFFSET as i64) as *mut i64) = 7;
        }

        let (value, ty) = unwrap_io_inline(base, io_int_type());
        assert_eq!(value, 7);
        assert_eq!(ty, Type::Int);

        let new_allocs = cranelisp_runtime::alloc_count() - allocs_before;
        let new_deallocs = cranelisp_runtime::dealloc_count() - deallocs_before;
        assert_eq!(
            new_allocs, 1,
            "only 1 alloc expected (the Pure node); got {new_allocs}"
        );
        assert_eq!(
            new_deallocs, 1,
            "expected 1 dealloc from consume_io_tree; got {new_deallocs} \
             — Decision 24 consuming-contract regression"
        );
        assert_eq!(
            new_allocs, new_deallocs,
            "unwrap_io_inline RC imbalance: {new_allocs} allocs vs \
             {new_deallocs} deallocs"
        );
    }
}
