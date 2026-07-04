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
) -> Result<ExprOutcome, CranelispError> {
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

    // Run through the SAME unified C-ABI driver `--run`/`--link` use
    // (`cranelisp_intrinsics::panic::cranelisp_run_program`, FIXME 0366) —
    // the single clear→call→pre-IO-peek→drive_io→post-IO-peek sequence
    // documented on that function as "REPL-safe (no `process::exit` inside
    // the driver)". FIXME 0499: the REPL eval path used to hand-roll a
    // partial mirror of this sequence (`take_runtime_error()` immediately
    // after `func()`, then `unwrap_io_inline` with no error-slot check
    // afterward) — that mirror checked the runtime-error slot only BEFORE
    // driving the IO tree, never AFTER. A fatal runtime error raised DURING
    // the drive (e.g. an empty `(select [])` hitting the count-zero guard in
    // `run_select_node`, `crates/cranelisp-intrinsics/src/io.rs`) therefore
    // synthesised its sentinel `0` straight through to display instead of
    // aborting the expression (spec/10-io.md §10.12.8 violation) — a
    // single-driver/dual-host-wrapper divergence, not a second IO driver.
    // Delegating to the shared driver here removes the second wrapper
    // entirely: REPL and `--run`/`--link` now reach the identical
    // clear→call→peek→drive→peek sequence, so every fatal-runtime-error-
    // raising IO op (not just `select`) is observed identically in both
    // modes.
    //
    // SAFETY: `got_addr` is the finalized code pointer for the zero-arg
    // `__expr` wrapper, written by `compile_to_module`. The `Arc<Jit>` on the
    // `__expr` entry keeps the pages mapped for the duration of this call +
    // the IO drive the program driver performs internally.
    let outcome =
        cranelisp_intrinsics::panic::cranelisp_run_program(got_addr, ty.is_io());

    program_outcome_to_result(outcome, ty)
}

/// The outcome of running a compiled `__expr`: a computed value or a
/// **runtime trap** (a `(runtime_panic …)`-raised error — a broken symbol's
/// trap stub, an exhaustiveness failure, an empty `(select [])`, …).
///
/// A trap is NOT a compiler error, so it is deliberately NOT a
/// `CranelispError`: `CranelispError`'s Display wraps every variant in a
/// category+span prefix (`codegen error at 0..0: …`), and the REPL/`--run`
/// printers then add `Error: …` — the wrapper chain repl/spec.md §18.5
/// forbids. The trap payload rides this dedicated int-side outcome instead;
/// the printer renders it as the bare `runtime error: {payload}` §18.5 line
/// (s102-defect-wave.md §7.2 — the recommended int-side cut, no
/// `cranelisp-types` change). Genuine compiler/platform faults (the dispatch
/// funnel) stay `Err(CranelispError)`.
#[derive(Debug, Clone, PartialEq)]
pub enum ExprOutcome {
    /// A computed value with its (IO-unwrapped) type.
    Value { value: i64, ty: Type },
    /// A runtime trap. `message` is the §18.5 payload — the trap body with the
    /// intrinsics-internal `runtime panic: ` slot prefix already normalized
    /// away — WITHOUT the `runtime error: ` category prefix (the printer adds
    /// that, matching §5.1's category+message model).
    Trap { message: String },
}

/// Translate a [`cranelisp_intrinsics::panic::ProgramOutcome`] into
/// `execute_compiled_expr`'s [`ExprOutcome`] / `Result` contract. Split out
/// so this translation is unit-testable without a live JIT/symbol table —
/// this is the exact seam where the pre-fix REPL path (FIXME 0499) silently
/// dropped a runtime error raised DURING the IO drive: the former code never
/// inspected an outcome/slot at this point at all.
fn program_outcome_to_result(
    outcome: cranelisp_intrinsics::panic::ProgramOutcome,
    ty: Type,
) -> Result<ExprOutcome, CranelispError> {
    match outcome.error_kind {
        // 1 = runtime error: the runtime-error slot is SET (drain for text).
        // Reached whether the panic occurred pre-IO (during the bare
        // `__expr` call) or post-IO (during the trampoline/reactor drive,
        // e.g. FIXME 0499's empty `(select [])`) — the driver collapses both
        // cases into one outcome kind. This is a runtime TRAP, not a compiler
        // error: return the dedicated `ExprOutcome::Trap` (repl/spec.md §18.5)
        // — NOT a `CranelispError::CodegenError`, which would wrap the payload
        // as `codegen error at 0..0: runtime error: runtime panic: …` and then
        // gain an `Error: ` prefix at the printer. Normalize the
        // intrinsics-internal `runtime panic: ` slot prefix away HERE (the
        // single chokepoint reading the slot); the printer supplies the §18.5
        // `runtime error: ` category prefix.
        1 => {
            let raw = cranelisp_intrinsics::panic::take_runtime_error()
                .unwrap_or_else(|| "runtime panic".to_string());
            let message = raw
                .strip_prefix("runtime panic: ")
                .map(str::to_string)
                .unwrap_or(raw);
            Ok(ExprOutcome::Trap { message })
        }
        // 2 = platform-dispatch fault (FIXME 0327, the dispatch funnel). This
        // IS a genuine compiler/platform fault (a structured `PlatformError`),
        // so it stays `Err(CranelispError)`.
        2 => {
            let fault = cranelisp_intrinsics::panic::take_dispatch_fault()
                .unwrap_or_else(|| cranelisp_intrinsics::panic::DispatchFault {
                    fn_name: "<unknown>".to_string(),
                    cause: "platform dispatch fault".to_string(),
                });
            Err(compose_dispatch_error(fault))
        }
        // 0 = clean: `outcome.exit_code` is the trampolined inner IO value
        // (or `__expr`'s own result for a non-IO expression). Unwrap the
        // type the same way `unwrap_io_inline` used to.
        _ => {
            let result_ty = if ty.is_io() { ty.unwrap_io().clone() } else { ty };
            Ok(ExprOutcome::Value { value: outcome.exit_code, ty: result_ty })
        }
    }
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

// `unwrap_io_inline` — DELETED (FIXME 0499 fix). It hand-rolled a
// REPL-only "drive the IO tree" step that duplicated a SLICE of
// `cranelisp_run_program`'s clear→call→peek→drive→peek sequence without the
// post-IO error-slot peek — the single-driver/dual-host-wrapper divergence
// this fix removes. `execute_compiled_expr` now calls
// `cranelisp_intrinsics::panic::cranelisp_run_program` directly (the same
// driver `--run`/`--link` use), and `program_outcome_to_result` performs the
// same type-unwrap this function used to. Its dedicated RC-balance unit
// tests are superseded by `cranelisp-intrinsics`'s own
// `decision24_run_io_pure_rc_balanced` (`crates/cranelisp-intrinsics/src/io/tests.rs`),
// which already pins the Decision-24 consuming-convention invariant at the
// driver's actual home.

// `compile_and_execute_expr_with_trace` — DELETED S76 (W-Collapse + trace
// ruling). The trace eval path no longer hand-rolls a JIT; trace codegen +
// discovery are backend-internal and `(trace ...)` flows through the unified
// `compile_to_module` path like any other form.

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------
//
// FIXME 0499: these pin `program_outcome_to_result`, the seam where the REPL
// eval path (`execute_compiled_expr`) translates the shared
// `cranelisp_run_program` driver's `ProgramOutcome` into the
// `(value, Type)` / `Result` contract. The former `unwrap_io_inline`
// unit tests (Sprint 57 Wave 6) covered only the clean-IO-unwrap slice of
// this seam and were deleted with the function — the driver's own
// Decision-24 RC-balance invariant is now pinned at its actual home
// (`decision24_run_io_pure_rc_balanced`,
// `crates/cranelisp-intrinsics/src/io/tests.rs`). These tests instead cover
// all three `ProgramOutcome::error_kind` discriminants this fn dispatches on,
// including the exact case FIXME 0499 fixed: a fatal runtime error raised
// DURING the IO drive (kind 1, post-IO) must produce an `Err`, not a
// synthesised value.

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_intrinsics::panic::ProgramOutcome;
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

    /// error_kind 0 (clean), non-IO type: passthrough unchanged — the common
    /// REPL case (a bare `Int`/`Bool`/etc result) pays nothing extra.
    #[test]
    fn program_outcome_to_result_clean_non_io_passthrough() {
        let outcome = ProgramOutcome { exit_code: 42, error_kind: 0 };
        let got = program_outcome_to_result(outcome, Type::Int).unwrap();
        assert_eq!(got, ExprOutcome::Value { value: 42, ty: Type::Int });
    }

    /// error_kind 0 (clean), IO type: the exit_code is already the
    /// trampolined inner value (the driver forced the IO tree internally),
    /// so this just unwraps the type `IO a` -> `a` — the same unwrap
    /// `unwrap_io_inline` used to perform after driving IO itself.
    #[test]
    fn program_outcome_to_result_clean_io_unwraps_type() {
        let outcome = ProgramOutcome { exit_code: 7, error_kind: 0 };
        let got = program_outcome_to_result(outcome, io_int_type()).unwrap();
        assert_eq!(
            got,
            ExprOutcome::Value { value: 7, ty: Type::Int },
            "IO a result must unwrap to a"
        );
    }

    /// error_kind 1 (runtime error): a fatal runtime error (a broken symbol's
    /// trap, an exhaustiveness failure, FIXME 0499's empty `(select [])`)
    /// surfaces as `Ok(ExprOutcome::Trap)` — NOT a `CranelispError` (§18.5:
    /// the printer renders `runtime error: {payload}` with no wrapper chain).
    /// The intrinsics-internal `runtime panic: ` slot prefix is normalized
    /// away at this chokepoint so the payload is the bare §18.5 message.
    #[test]
    fn program_outcome_to_result_runtime_error_is_trap_with_normalized_message() {
        let _ = cranelisp_intrinsics::panic::take_runtime_error(); // clear any stale slot
        cranelisp_intrinsics::panic::set_runtime_error(
            "runtime panic: select over empty collection".to_string(),
        );
        let outcome = ProgramOutcome { exit_code: 0, error_kind: 1 };
        let got = program_outcome_to_result(outcome, io_int_type())
            .expect("a trap is Ok(Trap), not Err");
        assert_eq!(
            got,
            ExprOutcome::Trap {
                // the `runtime panic: ` prefix is stripped — the printer adds
                // the §18.5 `runtime error: ` category prefix.
                message: "select over empty collection".to_string(),
            },
        );
        // The slot was drained (take, not peek) — a second read is empty.
        assert_eq!(cranelisp_intrinsics::panic::take_runtime_error(), None);
    }

    /// error_kind 1 with an empty slot (defensive: the driver contract says
    /// the slot is SET on a non-zero kind, but the translation must not
    /// panic/unwrap if it somehow isn't) falls back to a generic message.
    #[test]
    fn program_outcome_to_result_runtime_error_missing_slot_falls_back() {
        let _ = cranelisp_intrinsics::panic::take_runtime_error(); // ensure empty
        let outcome = ProgramOutcome { exit_code: 0, error_kind: 1 };
        let got = program_outcome_to_result(outcome, Type::Int).unwrap();
        assert_eq!(got, ExprOutcome::Trap { message: "runtime panic".to_string() });
    }

    /// error_kind 2 (platform-dispatch fault, FIXME 0327): composed into a
    /// structured `PlatformError::DispatchError` via `compose_dispatch_error`.
    #[test]
    fn program_outcome_to_result_dispatch_fault_is_err() {
        let _ = cranelisp_intrinsics::panic::take_dispatch_fault(); // clear any stale slot
        cranelisp_intrinsics::panic::set_dispatch_fault(
            cranelisp_intrinsics::panic::DispatchFault {
                fn_name: "stdio/read-line".to_string(),
                cause: "device unavailable".to_string(),
            },
        );
        let outcome = ProgramOutcome { exit_code: 0, error_kind: 2 };
        let err = program_outcome_to_result(outcome, Type::Int).unwrap_err();
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
        assert_eq!(cranelisp_intrinsics::panic::take_dispatch_fault(), None);
    }
}
