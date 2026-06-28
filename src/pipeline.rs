// Pipeline: shared compilation functions used by the v4 pipeline.
//
// This module provides:
// - Module file resolution
// - Expression compilation and execution (REPL eval)

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

/// Execute the current module's already-compiled `__expr` entry and return
/// `(value, type)`.
///
/// S76 W-Collapse: the REPL expression-eval path no longer hand-rolls a
/// second JIT. `worker::inline_jit_codegen_for_module` (called by the eval
/// driver before this fn) compiled the synthetic `__expr` defn through the
/// unified `compile_to_module` path, which populated its per-module GOT slot
/// and installed a `Code::Jit(Arc<Jit>)` lifecycle owner on the entry. This
/// function reads the GOT address, transmutes it to a zero-arg `extern "C"`
/// fn, calls it, and (for IO results) trampolines inline while the `Arc<Jit>`
/// on the `__expr` entry keeps the code mapped.
///
/// Sprint 57 Wave 6 (IO-path SIGBUS fix, preserved): when `__expr`'s inferred
/// type is `IO a`, the raw IO pointer is forced through `run_io_trampoline`
/// *before this fn returns* — the IO tree may carry heap closures whose
/// `code_ptr`s point into the JIT's mmap'd pages. The `Arc<Jit>` retained on
/// the `__expr` entry keeps those pages live for the duration of the call +
/// trampoline. (Eval-result lifetime / reclaim is driven by the `Code::Jit`
/// `Drop` when the entry is later replaced — `int.md` §5.3.)
pub fn execute_compiled_expr(
    display: Option<&cranelisp_types::DisplayInfo>,
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    current_module: &ModuleFullPath,
) -> Result<(i64, Type), CranelispError> {
    // Read the GOT address + inferred type for the compiled `__expr` entry.
    let (got_addr, expr_ty) = {
        let table = symbol_tables.get(current_module).ok_or_else(|| {
            CranelispError::CodegenError {
                message: "no symbol table for current module at expr eval".into(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }
        })?;
        let entry = table.get("__expr").ok_or_else(|| CranelispError::CodegenError {
            message: "no `__expr` entry found in current module".into(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
        // The callable slot now rides on the `DefKind` variant (S83 reshape,
        // FIXME 0356/0357) — read it via the `callable_got_slot()` chokepoint.
        let Some(slot) = entry.callable_got_slot() else {
            return Err(CranelispError::CodegenError {
                message: "`__expr` entry has no GOT slot (codegen did not run)".into(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        };
        let cranelisp_types::ModuleEntry::Def { ast, .. } = entry else {
            return Err(CranelispError::CodegenError {
                message: "`__expr` entry is not a Def".into(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        };
        // `ast` is now `DefnVariant` (S69 Submission 35); `body` is a field.
        let inferred = ast
            .as_ref()
            .and_then(|d| d.body.inferred_type().cloned());
        (table.got.load_slot(slot), inferred)
    };

    if got_addr.is_null() {
        return Err(CranelispError::CodegenError {
            message: "`__expr` GOT slot is null (codegen did not populate it)".into(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    // Type: display info first, then the AST node's inferred_type.
    let ty = display
        .map(|d| d.ty.clone())
        .or(expr_ty)
        .unwrap_or(Type::Int);

    // SAFETY: `got_addr` is the finalized code pointer for the zero-arg
    // `__expr` wrapper, written by `compile_to_module`. The `Arc<Jit>` on the
    // `__expr` entry keeps the pages mapped for the duration of this call.
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(got_addr) };
    let _ = cranelisp_intrinsics::panic::take_runtime_error();
    let raw_value = func();

    if let Some(msg) = cranelisp_intrinsics::panic::take_runtime_error() {
        return Err(CranelispError::CodegenError {
            message: format!("runtime error: {msg}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    // IO trampoline inline (the code is still mapped via the entry's Arc<Jit>).
    let result = unwrap_io_inline(raw_value, ty);

    // A platform Effect forced during the trampoline may have faulted under the
    // intrinsics fault guard (FIXME 0327, the dispatch funnel). The guard
    // captured `(fn_name, cause)` into the dispatch-fault slot; compose the
    // structured `PlatformError::DispatchError` here (the two-layer split:
    // intrinsics sets the slot, int composes — BC §4b invariant 14 / §5
    // invariant 9). This is checked AFTER the trampoline because the fault is
    // raised during the IO force, not during the bare `__expr` call.
    if let Some(fault) = cranelisp_intrinsics::panic::take_dispatch_fault() {
        return Err(compose_dispatch_error(fault));
    }

    Ok(result)
}

/// Compose a structured `PlatformError::DispatchError` from an intrinsics
/// dispatch-fault carrier (FIXME 0327 — the dispatch funnel, int's compose
/// half). The intrinsics guard captured `(fn_name, cause)` and is
/// diagnostics-free by charter; int maps it to the typed error surfaced via
/// `CranelispError::Platform`.
fn compose_dispatch_error(
    fault: cranelisp_intrinsics::panic::DispatchFault,
) -> CranelispError {
    CranelispError::Platform(cranelisp_types::PlatformError::DispatchError {
        fn_name: cranelisp_types::Symbol::from(fault.fn_name),
        cause: fault.cause,
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })
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
        // Drive the IO tree through `cranelisp_run_io` — the single entry that
        // cfg-splits to the host reactor under `concurrency-runtime` (so real
        // poll-shape effect nodes suspend/resume on the reactor, FIXME 0457) and
        // to the synchronous stepper otherwise (byte-identical). It ALSO releases
        // the caller's tree internally (Decision 24 consuming convention —
        // `drive_io` + `consume_io_tree`), so no separate consume is needed here.
        // Routing `--run`/REPL through this same entry as `--link` keeps the IO
        // forcing single-sited (the reactor is never re-driven by a parallel int
        // path; 0419 divergence-proofing).
        let inner_value = cranelisp_intrinsics::io::cranelisp_run_io(raw_value);
        let inner_type = ty.unwrap_io().clone();
        (inner_value, inner_type)
    } else {
        (raw_value, ty)
    }
}

// `compile_and_execute_expr_with_trace` — DELETED S76 (W-Collapse + trace
// ruling). The trace eval path no longer hand-rolls a JIT; trace codegen +
// discovery are backend-internal and `(trace ...)` flows through the unified
// `compile_to_module` path like any other form.

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

    // spec: design/arch/bounded-contexts.md §5 invariant 9 — int composes a
    // structured `PlatformError::DispatchError` from the intrinsics-captured
    // dispatch fault, mapping fn_name + cause and surfacing via
    // `CranelispError::Platform` (FIXME 0327, the dispatch funnel, int's
    // compose half).
    #[test]
    fn compose_dispatch_error_maps_fn_name_and_cause() {
        let fault = cranelisp_intrinsics::panic::DispatchFault {
            fn_name: "stdio/read-line".to_string(),
            cause: "device unavailable".to_string(),
        };
        let err = compose_dispatch_error(fault);
        match err {
            CranelispError::Platform(cranelisp_types::PlatformError::DispatchError {
                fn_name,
                cause,
                ..
            }) => {
                assert_eq!(fn_name.as_ref(), "stdio/read-line");
                assert_eq!(cause, "device unavailable");
            }
            other => panic!("expected Platform(DispatchError), got {other:?}"),
        }
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
        use cranelisp_intrinsics::alloc_with_rc;
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
        use cranelisp_intrinsics::alloc_with_rc;
        const TAG_OFFSET: isize = 16;
        const FIELD_0_OFFSET: isize = 24;
        const IO_TAG_PURE: i64 = 0;

        let allocs_before = cranelisp_intrinsics::alloc_count();
        let deallocs_before = cranelisp_intrinsics::dealloc_count();

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

        let new_allocs = cranelisp_intrinsics::alloc_count() - allocs_before;
        let new_deallocs = cranelisp_intrinsics::dealloc_count() - deallocs_before;
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
