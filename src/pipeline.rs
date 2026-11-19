// Pipeline: shared compilation functions used by the v4 pipeline.
//
// This module provides:
// - Module file resolution
// - Expression compilation and execution (REPL eval)

use std::path::{Path, PathBuf};

use cranelisp_types::{CranelispError, ErrorLocation, ModuleFullPath, Span, Type};

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
    // Tier 2: project root.
    let root_candidate = project_root_candidate(module, project_root);
    if root_candidate.is_file() {
        return Some(root_candidate);
    }

    // Tier 3: lib directories.
    let relative = module_relative_path(module);
    for dir in lib_dirs {
        let candidate = dir.join(&relative);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

/// The file that `module`'s name maps to under `project_root`, and the first
/// file the module resolver probes for it: each `.` in the module path is a
/// directory separator, so `core.str` maps to `{project_root}/core/str.cl`.
///
/// The path is computed, not probed; it need not exist. A module whose
/// recorded file equals this path was resolved from the project root.
pub fn project_root_candidate(module: &ModuleFullPath, project_root: &Path) -> PathBuf {
    project_root.join(module_relative_path(module))
}

fn module_relative_path(module: &ModuleFullPath) -> String {
    format!("{}.cl", module.as_ref().replace('.', "/"))
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
///
/// `_ready` shows that every cached object load the code could call has
/// ended (`design/int/int.md` §7.1, *load before execution*).
pub fn execute_compiled_expr(
    display: Option<&cranelisp_types::DisplayInfo>,
    shared: &crate::session_v4::SharedState,
    current_module: &ModuleFullPath,
    _ready: crate::scheduler::ExecutionReadiness,
) -> Result<crate::result_owner::OwnedProgramResult, CranelispError> {
    let symbol_tables = &shared.symbol_tables;
    // Read the GOT address + observed type + code lifetime owner for the
    // compiled `__expr` entry, in ONE read (`design/int/result-owner.md` §4.3
    // — the result owner's release target must pair with the retention owner
    // of the code that produced the result, and the type must come from the
    // same read that produced the pointer).
    let (got_addr, ty, code_owner, codegen_result_ty) = {
        let table =
            symbol_tables
                .get(current_module)
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "no symbol table for current module at expr eval".into(),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                })?;
        let entry = table
            .get("__expr")
            .ok_or_else(|| CranelispError::CodegenError {
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
        // The release key backend itself keyed on, read in the SAME pass
        // (`design/int/result-owner.md` §4.3).
        let codegen_result_ty = entry.codegen_view().map(|view| view.body.ty().clone());
        let Some(callable) = entry.callable() else {
            return Err(CranelispError::CodegenError {
                message: "`__expr` entry is not a Def".into(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        };
        let cranelisp_types::Life::Concrete {
            realization: cranelisp_types::Realization::Body { code, .. },
            ast,
            ..
        } = &callable.arm.life
        else {
            return Err(CranelispError::CodegenError {
                message: "`__expr` entry is not a concrete body".into(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        };
        // `ast` is now `DefnVariant` (S69 Submission 35); `body` is a field.
        let inferred = ast.as_ref().and_then(|d| d.body.inferred_type().cloned());
        (
            table.got.load_slot(slot),
            observed_expr_type(display, inferred, &callable.arm.scheme.ty),
            code.clone(),
            codegen_result_ty,
        )
    };

    if got_addr.is_null() {
        return Err(CranelispError::CodegenError {
            message: "`__expr` GOT slot is null (codegen did not populate it)".into(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    // Run through the same C-ABI driver `--run` and `--link` use. A runtime
    // panic ends the process inside the driver, so it returns only after a
    // clean run (`design/int/io-integration.md` §1.2).
    //
    // SAFETY: `got_addr` is the finalized code pointer for the zero-arg
    // `__expr` wrapper, written by `compile_to_module`. The `Arc<Jit>` on the
    // `__expr` entry keeps the pages mapped for the duration of this call +
    // the IO drive the program driver performs internally.
    let is_io = ty.is_io();
    // A failed stdout write is ignored, as for every REPL display line.
    let _ = write_io_execution_notice(is_io, &mut std::io::stdout());
    let value = cranelisp_intrinsics::panic::cranelisp_run_program(got_addr, is_io);

    // The word crosses into the one program-result owner here. The owner stays
    // armed across the `EvalResult::Val` boundary and is released by the REPL
    // driver after the turn's `StyledDoc` is complete (result-owner §4.2).
    let resolver = crate::result_owner::SessionGlueResolver::for_result_code(
        code_owner.as_ref(),
        &shared.fresh_jit_drop_glues,
    );
    crate::result_owner::OwnedProgramResult::new(
        value,
        driver_result_type(ty),
        codegen_result_ty,
        current_module,
        symbol_tables,
        &resolver,
    )
}

/// The type an executed `__expr` is observed at (`design/int/result-owner.md`
/// §4.3.1): the check's display type, else the body's inferred type, else the
/// result of the arm's scheme. The chain is total; no type is supplied by
/// default.
fn observed_expr_type(
    display: Option<&cranelisp_types::DisplayInfo>,
    inferred: Option<Type>,
    scheme: &Type,
) -> Type {
    display
        .map(|d| d.ty.clone())
        .or(inferred)
        .unwrap_or_else(|| zero_arg_result(scheme).clone())
}

/// The result of a zero-argument definition's scheme: `ret` of `Fn([], ret)`,
/// else the scheme's own type.
pub(crate) fn zero_arg_result(scheme: &Type) -> &Type {
    match scheme {
        Type::Fn(_, ret) => ret,
        other => other,
    }
}

/// The type of the word `cranelisp_run_program` returns for a program of type
/// `ty`: the driver forces an `IO a` and returns its `a`. This is the one
/// `IO a` → `a` unwrap; the result owner refuses an `IO a` type.
pub(crate) fn driver_result_type(ty: Type) -> Type {
    if ty.is_io() {
        ty.unwrap_io().clone()
    } else {
        ty
    }
}

/// Write the §1.2.1 notice when the driver is about to force an IO action.
///
/// The notice must precede output that platforms write to stdout during the
/// driver call, so it is written and flushed here rather than returned with the
/// result. `is_io` must be the same value that selects forcing.
fn write_io_execution_notice(is_io: bool, out: &mut impl std::io::Write) -> std::io::Result<()> {
    if !is_io {
        return Ok(());
    }
    writeln!(out, "{}", crate::repl::format::io_execution_notice_line())?;
    out.flush()
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{FQTypeName, TypeName};

    fn io_int_type() -> Type {
        Type::ADT(
            FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("IO")),
            vec![Type::Int],
        )
    }

    // spec: design/int/result-owner.md §4.3.1 — with no display type and no
    // inferred body type, `__expr` is observed at its scheme's result, and an
    // `IO` scheme selects forcing.
    #[test]
    fn an_expr_with_no_display_or_inferred_type_takes_its_scheme_result() {
        let scheme = Type::Fn(vec![], Box::new(io_int_type()));
        let observed = observed_expr_type(None, None, &scheme);
        assert_eq!(observed, io_int_type());
        assert!(observed.is_io(), "an IO scheme selects forcing");
    }

    // spec: design/int/result-owner.md §4.3.1 — the display type comes first,
    // then the inferred body type.
    #[test]
    fn the_display_type_then_the_inferred_type_wins_over_the_scheme() {
        let scheme = Type::Fn(vec![], Box::new(io_int_type()));
        let display = cranelisp_types::DisplayInfo {
            ty: Type::String,
            scheme: None,
        };
        assert_eq!(
            observed_expr_type(Some(&display), Some(Type::Bool), &scheme),
            Type::String
        );
        assert_eq!(
            observed_expr_type(None, Some(Type::Bool), &scheme),
            Type::Bool
        );
    }

    // spec: design/int/result-owner.md §4.4 — a non-IO program's word has the
    // program's own type.
    #[test]
    fn driver_result_type_keeps_a_non_io_type() {
        assert_eq!(driver_result_type(Type::Int), Type::Int);
    }

    // spec: design/int/result-owner.md §4.4 — the driver forces `IO a`, so its
    // word is the inner `a`; the owner never sees `IO a`.
    #[test]
    fn driver_result_type_unwraps_io_once() {
        assert_eq!(driver_result_type(io_int_type()), Type::Int);
    }

    /// Records whether a flush followed the last write, so a notice left in a
    /// buffer (and therefore printed after the effects) is observable.
    #[derive(Default)]
    struct FlushProbe {
        bytes: Vec<u8>,
        flushed_after_write: bool,
    }

    impl std::io::Write for FlushProbe {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.bytes.extend_from_slice(buf);
            self.flushed_after_write = false;
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            self.flushed_after_write = true;
            Ok(())
        }
    }

    // spec: repl/spec/01-display-format.md §1.2.1 — the notice line precedes
    // the IO action's platform output, so it is flushed before the driver runs.
    #[test]
    fn io_execution_notice_is_written_as_one_line_and_flushed_for_io() {
        let mut out = FlushProbe::default();
        write_io_execution_notice(true, &mut out).unwrap();
        assert_eq!(
            String::from_utf8(out.bytes).unwrap(),
            format!("{}\n", crate::repl::format::io_execution_notice_line())
        );
        assert!(out.flushed_after_write, "the notice must be flushed");
    }

    // spec: repl/spec/01-display-format.md §1.2.1 — a non-IO expression MUST
    // NOT produce the notice.
    #[test]
    fn io_execution_notice_writes_nothing_for_non_io() {
        let mut out = FlushProbe::default();
        write_io_execution_notice(false, &mut out).unwrap();
        assert!(out.bytes.is_empty());
    }
}
