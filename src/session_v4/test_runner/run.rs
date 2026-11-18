//! Prepare, execute and report (`design/int/test-runner.md` §6): the one run
//! that `--test`, `/run-tests` and `/run-all-tests` share, executed in the
//! test child (§6.5). Everything fallible except writing a record happens in
//! preparation, before any test runs.

use std::time::Duration;

use cranelisp_intrinsics::alloc::HeapAdt;
use cranelisp_types::{
    CranelispError, FQSymbol, Life, ModuleFullPath, NULLARY_TAG_THRESHOLD, Realization, Type,
    Warning,
};

use super::child::{Record, RecordSink};
use super::discovery::{self, Discovery};
use super::selection::SelectionInputs;
use crate::result_owner::{OwnedProgramResult, ReleasePlan, SessionGlueResolver};
use crate::scheduler::ExecutionReadiness;
use crate::session_v4::{CompilerSession, SharedState};

/// The outcome of one test run: the report text, the discovery warnings and
/// the process exit status the run implies.
///
/// The text and the exit code are computed together from the same outcomes,
/// so they cannot disagree.
pub struct TestRunReport {
    text: String,
    warnings: Vec<Warning>,
    exit_code: i32,
}

impl TestRunReport {
    /// The report in the `/run-tests` format (`repl/spec/16-test-discovery.md`
    /// §16.2): one line per test with its fully qualified name, ending `ok`,
    /// `FAILED: <reason>` or `PANIC: <message>`, then a blank line and the
    /// summary. With no eligible test the text is exactly `No tests found`.
    /// Every client prints this same text.
    pub fn text(&self) -> &str {
        &self.text
    }

    /// The §16.1 discovery warnings: one for each `test-` function excluded
    /// because its scheme is not exactly `(Fn [] (Option String))`. The caller
    /// chooses the stream they are shown on.
    pub fn warnings(&self) -> &[Warning] {
        &self.warnings
    }

    /// `0` when no selected test failed or panicked, including an empty run;
    /// otherwise `1`.
    pub fn exit_code(&self) -> i32 {
        self.exit_code
    }

    pub(super) fn new(
        outcomes: Vec<(FQSymbol, TestOutcome)>,
        warnings: Vec<Warning>,
        elapsed: Duration,
    ) -> Self {
        if outcomes.is_empty() {
            return Self {
                text: "No tests found".to_string(),
                warnings,
                exit_code: 0,
            };
        }
        let mut lines = Vec::with_capacity(outcomes.len() + 2);
        let mut failed = 0usize;
        for (id, outcome) in &outcomes {
            let name = id.to_string();
            let dots = ".".repeat(REPORT_NAME_WIDTH.saturating_sub(name.len()));
            let result = match outcome {
                TestOutcome::Pass => "ok".to_string(),
                TestOutcome::Fail { reason } => format!("FAILED: {reason}"),
                TestOutcome::Panic { reason } => format!("PANIC: {reason}"),
            };
            if !matches!(outcome, TestOutcome::Pass) {
                failed += 1;
            }
            lines.push(format!("  {name} {dots} {result}"));
        }
        let passed = outcomes.len() - failed;
        let millis = elapsed.as_secs_f64() * 1000.0;
        lines.push(String::new());
        lines.push(if failed == 0 {
            format!("{passed} passed in {millis:.2}ms")
        } else {
            format!("{passed} passed, {failed} failed in {millis:.2}ms")
        });
        Self {
            text: lines.join("\n"),
            warnings,
            exit_code: i32::from(failed != 0),
        }
    }
}

/// Test names are padded with dots to this width before the outcome.
const REPORT_NAME_WIDTH: usize = 40;

/// The reason reported for an eligible test with no callable code.
const UNAVAILABLE_REASON: &str = "test function not found";

/// One test's outcome. The child records `Pass` and `Fail`; only the
/// supervisor, which sees a child end at a panic, produces `Panic`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum TestOutcome {
    Pass,
    Fail { reason: String },
    Panic { reason: String },
}

/// One test after preparation. `call` is `None` when the test has no callable
/// code; it is then reported failed, never passed.
struct PreparedTest {
    id: FQSymbol,
    call: Option<PreparedCall>,
}

/// Everything one call needs, captured in one entry read (result-owner
/// §4.3): the code pointer, the retention owner of the code it points into
/// (Principle 22) and the planned release of its result.
struct PreparedCall {
    code: *const u8,
    code_owner: crate::code::Code,
    release: ReleasePlan,
}

impl CompilerSession {
    /// The test child's engine (`design/int/test-runner.md` §6.5): run the
    /// selected tests in this process and append one record per test to
    /// `records`. The supervisor, `supervise_tests`, reads them and builds
    /// the report; a runtime panic ends this process with the test open.
    ///
    /// **Precondition:** the entry module has compiled and is loaded in
    /// memory: `register_module` and `wait_inmem_complete` both returned `Ok`.
    ///
    /// **Selection:** `modules` is the REPL's selection; each selected module
    /// that is not yet loaded is loaded first. `None` selects the entry
    /// module plus every project module reachable from it through `import`
    /// and `export` entries with a non-empty names list, `(mod …)`/`(mod- …)`
    /// children and the implicit prelude, as `--test` does
    /// (`repl/spec/00-cli-invocation.md` §0.2.2). Library modules end the
    /// chain.
    ///
    /// **Execution:** every eligible test (§16.1) that sorts after
    /// `resume_after` runs on the calling thread in FQ order. A failing test
    /// does not stop the run. `main` is never called.
    ///
    /// **Errors:** `Err` before any test has run means the run could not
    /// start: a program that references `discover-tests` (§16.6), a load or
    /// readiness failure, an unresolvable result-release target, or a record
    /// file that cannot be created. After a test has started, `Err` means
    /// only that a record could not be written. A failing test is never
    /// `Err`.
    pub fn run_tests(
        &self,
        records: &std::path::Path,
        modules: Option<&[ModuleFullPath]>,
        resume_after: Option<&FQSymbol>,
    ) -> Result<(), CranelispError> {
        let modules = match modules {
            Some(selected) => {
                for module in selected {
                    self.load_test_module(module)?;
                }
                selected.to_vec()
            }
            None => self.selection_inputs().chain_modules()?,
        };
        self.refuse_dev_session_externs()?;
        let ready = self.shared.scheduler.wait_cached_loads_settled()?;
        let Discovery { tests, warnings } =
            discovery::scan_modules(&self.shared.symbol_tables, &modules);
        let tests = tests
            .into_iter()
            .filter(|id| resume_after.is_none_or(|after| id > after))
            .collect();
        let prepared = prepare(&self.shared, tests, &ready)?;
        let mut sink = RecordSink::create(records)?;
        for warning in warnings {
            sink.write(&Record::Warning(warning.message))?;
        }
        execute(prepared, &mut sink)?;
        sink.write(&Record::End)
    }

    /// Load a selected module that this child has not loaded through the
    /// entry chain, by the same load-on-reference `/mod` uses.
    fn load_test_module(&self, module: &ModuleFullPath) -> Result<(), CranelispError> {
        if self.shared.symbol_tables.contains_key(module) {
            return Ok(());
        }
        if !self.has_module_file(module) {
            return Err(CranelispError::ModuleError {
                message: format!("module '{module}' selected for testing has no source file"),
                location: cranelisp_types::ErrorLocation::from_span(
                    cranelisp_types::Span::SYNTHETIC,
                ),
            });
        }
        self.load_module_by_reference(module)
            .map_err(CranelispError::from)
    }

    pub(crate) fn selection_inputs(&self) -> SelectionInputs<'_> {
        SelectionInputs {
            tables: &self.shared.symbol_tables,
            products: &self.shared.typecheck_products,
            prelude_fallback: &self.shared.prelude_fallback,
            entry: &self.shared.entry_module,
            project_root: &self.shared.project_root,
        }
    }
}

/// Prepare every test before any runs. `_ready` shows that every cached
/// object load a test could call has ended (`design/int/int.md` §7.1).
fn prepare(
    shared: &SharedState,
    tests: Vec<FQSymbol>,
    _ready: &ExecutionReadiness,
) -> Result<Vec<PreparedTest>, CranelispError> {
    tests
        .into_iter()
        .map(|id| {
            let call = prepare_call(shared, &id)?;
            Ok(PreparedTest { id, call })
        })
        .collect()
}

/// The code pointer, owner and result types of a callable test, read under one
/// table guard that is dropped before the release target is resolved.
struct EntryRead {
    code: *const u8,
    code_owner: crate::code::Code,
    result_ty: Type,
    codegen_result_ty: Option<cranelisp_types::ConcreteType>,
}

fn read_entry(shared: &SharedState, id: &FQSymbol) -> Option<EntryRead> {
    let table = shared.symbol_tables.get(&id.module)?;
    let entry = table.get(id.symbol.as_ref())?;
    let callable = entry.callable()?;
    let Life::Concrete {
        realization:
            Realization::Body {
                code: Some(code_owner),
                ..
            },
        ..
    } = &callable.arm.life
    else {
        return None;
    };
    let Type::Fn(_, result_ty) = &callable.arm.scheme.ty else {
        return None;
    };
    let code = table.got.load_slot(entry.callable_got_slot()?);
    if code.is_null() {
        return None;
    }
    Some(EntryRead {
        code,
        code_owner: code_owner.clone(),
        result_ty: *result_ty.clone(),
        codegen_result_ty: entry.codegen_view().map(|view| view.body.ty().clone()),
    })
}

fn prepare_call(
    shared: &SharedState,
    id: &FQSymbol,
) -> Result<Option<PreparedCall>, CranelispError> {
    let Some(read) = read_entry(shared, id) else {
        return Ok(None);
    };
    let resolver =
        SessionGlueResolver::for_result_code(Some(&read.code_owner), &shared.fresh_jit_drop_glues);
    let release = ReleasePlan::new(
        read.result_ty,
        read.codegen_result_ty,
        &id.module,
        &shared.symbol_tables,
        &resolver,
    )?;
    Ok(Some(PreparedCall {
        code: read.code,
        code_owner: read.code_owner,
        release,
    }))
}

/// Run each prepared test in order, recording `start` before the call and
/// its outcome after its result is released.
fn execute(prepared: Vec<PreparedTest>, sink: &mut RecordSink) -> Result<(), CranelispError> {
    for test in prepared {
        sink.write(&Record::Start(test.id))?;
        let outcome = match test.call {
            Some(call) => run_one(call),
            None => TestOutcome::Fail {
                reason: UNAVAILABLE_REASON.to_string(),
            },
        };
        sink.write(&Record::Outcome(outcome))?;
    }
    Ok(())
}

/// Call one test. A runtime panic ends the process inside the call, so a
/// return always carries a result to observe and release.
fn run_one(call: PreparedCall) -> TestOutcome {
    let PreparedCall {
        code,
        code_owner,
        release,
    } = call;
    // SAFETY: `code` is the non-null GOT slot value of a concrete zero-argument
    // callable whose scheme is exactly `(Fn [] (Option String))`, so it has the
    // `extern "C" fn() -> i64` convention. `code_owner` keeps its code mapped
    // until this function returns.
    let value = unsafe {
        let test: extern "C" fn() -> i64 = std::mem::transmute(code);
        test()
    };
    let result = release.own(value);
    let outcome = observe(&result);
    result.release();
    drop(code_owner);
    outcome
}

/// Read a test's `(Option String)` result: a bare tag is `None`, a heap
/// `Some` carries the failure reason in its one field.
fn observe(result: &OwnedProgramResult) -> TestOutcome {
    let value = result.observed_value();
    if (value as usize) < NULLARY_TAG_THRESHOLD {
        return TestOutcome::Pass;
    }
    // SAFETY: a word at or above the nullary threshold of an `(Option String)`
    // is a live heap `Some` box owned by `result`; field 0 is its `String`.
    let reason = unsafe {
        let base = value as *const u8;
        let string = *(base.add(HeapAdt::field_offset(0) as usize) as *const i64);
        cranelisp_intrinsics::heap_string::read_string_as_str(string).to_string()
    };
    TestOutcome::Fail { reason }
}

#[cfg(test)]
mod tests;
