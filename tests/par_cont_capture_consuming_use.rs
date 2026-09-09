// par_cont_capture_consuming_use.rs — S121. A heap value bound OUTSIDE an
// automatically-scheduled `Par` and used at a CONSUMING argument position
// INSIDE the `Par`'s continuation body.
//
// Provenance. `dev`'s pre/post probe of the S121 binder-scope repair
// (`design/backend/binding-scope.md`) measured an emission change on exactly
// this cell and nothing else, and the direction is pre-fix WRONG → post-fix
// CORRECT. This file is the permanent guard for that repair; it did not exist
// while the defect was open, so its RED is historical rather than authored.
//
// The defect, verified in source at S121 (not assumed from the probe's prose):
// `par_bind.rs`'s continuation-capture loop seeded each capture into
// `inner.variables` ONLY — no `variable_types` entry — while the repair routes
// the same captures through `fn_compiler.rs::bind_capture` with the type read
// from the ENCLOSING environment. `apply.rs`'s consuming-argument gate decides
// "owned binding" by `self.lookup_type(name).is_some()`, so pre-fix a heap
// capture at a consuming argument position took the fresh-temporary path and
// got NO consuming `rc_inc`. The closure environment's own reference (inc'd in
// `alloc_par_cont_closure`) was then consumed by the callee's exit dec and dec'd
// a second time by the closure's drop glue — a dec of an already-freed pointer.
//
// Measured by `dev`'s probe over five deterministic repeats per leg, and
// re-measured independently at this file's authoring against the same preserved
// pre-fix compiler (sha256 a913bc3a…) and the repaired build, 2026-09-08:
//
//   subject `--run`   pre: SIGABRT (`STALE RC DEC (consume_shallow)`,
//                          `crates/cranelisp-intrinsics/src/rc.rs:422`)   post: exit 8
//   subject `--link`  pre: SIGABRT, same message                          post: exit 8
//   C1 / C2 / C3 / C4 pre: exit 8                                         post: exit 8
//
// The four controls are each ONE structural step from the subject and were all
// GREEN on the pre-fix compiler, so a RED here that took a control with it would
// be a harness, platform or environment fault rather than this cell.
//
// Why an e2e cell and not a CLIF golden. `define_par_cont_body` compiles the
// continuation in its OWN Cranelift context, so `CRANELISP_CODEGEN_DUMP` never
// renders it: the dumped `main`/`g` CLIF is byte-identical pre- and post-fix.
// The golden lane is blind to this seam, which is plausibly why it sat
// unobserved. Running the program is the only available observation.
//
// Free-standing: `PreludeVariant::None`, every language name imported from
// `primitives`, the two scheduled effects from the workspace `test-capture`
// platform, no stdlib (root `CLAUDE.md` §"Stdlib separation").

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{CrOutput, Cranelisp, PreludeVariant};

// ===========================================================================
// Programs. The subject and its four controls, verbatim from the probe that
// measured them — each control differs from the subject in exactly one
// structural respect, named in its comment.
// ===========================================================================

/// SUBJECT. `s` is a `String` bound in `main`'s own scope; the two
/// `commutative-noop` effects are mutually independent, so the compiler groups
/// them into a `Par` (spec/10-io.md §10.12.5) whose continuation body captures
/// `s` and passes it TWICE to `g`, which consumes it. Result: 0 + 0 + 4 + 4 = 8.
const PAR_CONT_HEAP_CAPTURE: &str = "\
(platform test-capture)
(import [platform.test-capture [commutative-noop]])
(import [primitives [bind Pure str-len str-concat]])
(defn g [x] (str-len x))
(defn main []
  (let [s (str-concat \"ab\" \"cd\")]
    (bind (commutative-noop) (fn [a]
      (bind (commutative-noop) (fn [b]
        (Pure (primitives/add-i64 (primitives/add-i64 a b)
                                  (primitives/add-i64 (g s) (g s))))))))))
";

/// C1 — the SAME body with `s` bound INSIDE the continuation instead of
/// captured into it. Isolates the capture environment from the consuming use:
/// the two consuming `(g s)` calls, the `Par`, the heap value and the exit code
/// are unchanged; only the binder's home moves.
const C1_BOUND_INSIDE_CONTINUATION: &str = "\
(platform test-capture)
(import [platform.test-capture [commutative-noop]])
(import [primitives [bind Pure str-len str-concat]])
(defn g [x] (str-len x))
(defn main []
  (bind (commutative-noop) (fn [a]
    (bind (commutative-noop) (fn [b]
      (let [s (str-concat \"ab\" \"cd\")]
        (Pure (primitives/add-i64 (primitives/add-i64 a b)
                                  (primitives/add-i64 (g s) (g s))))))))))
";

/// C2 — the same capture shape with a SCALAR (`Int`) captured value. Isolates
/// the heap category: an `Int` capture carries no reference count, so a missing
/// consuming inc cannot double-free it.
const C2_SCALAR_CAPTURE: &str = "\
(platform test-capture)
(import [platform.test-capture [commutative-noop]])
(import [primitives [bind Pure]])
(defn h [x] (primitives/add-i64 x 0))
(defn main []
  (let [s 4]
    (bind (commutative-noop) (fn [a]
      (bind (commutative-noop) (fn [b]
        (Pure (primitives/add-i64 (primitives/add-i64 a b)
                                  (primitives/add-i64 (h s) (h s))))))))))
";

/// C3 — ONE `bind`, so there is no second independent effect to group and the
/// compiler emits no `Par`: the heap capture reaches an ordinary lambda
/// continuation instead of a par continuation. Isolates `par_bind.rs`'s
/// capture-seeding loop from `lambda.rs`'s.
const C3_SINGLE_BIND_NO_PAR: &str = "\
(platform test-capture)
(import [platform.test-capture [commutative-noop]])
(import [primitives [bind Pure str-len str-concat]])
(defn g [x] (str-len x))
(defn main []
  (let [s (str-concat \"ab\" \"cd\")]
    (bind (commutative-noop) (fn [a]
      (Pure (primitives/add-i64 a (primitives/add-i64 (g s) (g s))))))))
";

/// The automatic-IO-scheduling opt-out. C4 runs the SUBJECT with it set, so the
/// same source takes the unscheduled lowering and no par continuation is built.
const NO_IO_SCHEDULE_ENV: &str = "CRANELISP_NO_IO_SCHEDULE";

/// `(str-len "abcd")` twice, plus two `commutative-noop` results of 0.
const EXPECTED_EXIT: i32 = 8;

/// The intrinsics abort the pre-fix compiler produced on the subject. Named in
/// the assertion because the exit status alone would not distinguish this
/// premature-free abort from any other abnormal termination.
const STALE_RC_DEC: &str = "STALE RC DEC";

// ===========================================================================
// Harness
// ===========================================================================

/// `--run` the program with the workspace platforms on the search path, plus an
/// optional env overlay.
fn run_prog(src: &str, env: &[(&str, &str)]) -> CrOutput {
    let mut cr = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .use_workspace_platforms()
        .run("user.cl")
        .user(src);
    for (k, v) in env {
        cr = cr.env(k, v);
    }
    cr.output()
}

/// `--link` the program and RUN the produced executable (link-success alone
/// would not see this defect — it is a runtime fault).
fn link_then_run_prog(src: &str) -> CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .use_workspace_platforms()
        .link_then_run("user.cl")
        .user(src)
        .output()
}

/// The contract, applied identically to the subject and to every control: the
/// program answers 8 and no reference count is decremented on a freed pointer.
/// One invariant, five programs, SAME predicate — so the failing program names
/// the site by itself (`tests/CLAUDE.md` §"Coverage by definition variants").
///
/// Returns the violation rather than panicking, so a caller that observes more
/// than one mode reports EVERY mode's outcome instead of stopping at the first:
/// a defect that takes down both `--run` and `--link` is a different report
/// from one that takes down only one of them.
fn clean_result_violation(out: &CrOutput, mode: &str) -> Option<String> {
    if out.stderr.contains(STALE_RC_DEC) {
        return Some(format!(
            "`{mode}`: the runtime decremented a reference count on a pointer it \
             had already freed and reclaimed. spec/12-runtime.md §12.3.1(2) — \
             freed memory MUST NOT be accessed after deallocation.\n  exit: {:?}\n\
             stderr:\n{}",
            out.status.code(),
            out.stderr
        ));
    }
    if out.status.code() != Some(EXPECTED_EXIT) {
        return Some(format!(
            "`{mode}`: `(str-len \"abcd\")` twice plus two zero-valued effects is \
             {EXPECTED_EXIT}, so `main` MUST exit {EXPECTED_EXIT}; got {:?} (a \
             `None` code is termination by signal).\n  stdout:\n{}\n  stderr:\n{}",
            out.status.code(),
            out.stdout,
            out.stderr
        ));
    }
    None
}

/// Apply the contract to every `(mode, outcome)` pair and report all failures.
fn assert_clean_results(outcomes: &[(&str, CrOutput)], role: &str) {
    let violations: Vec<String> = outcomes
        .iter()
        .filter_map(|(mode, out)| clean_result_violation(out, mode))
        .collect();
    assert!(
        violations.is_empty(),
        "{role}: {} of {} observed mode(s) violated the contract.\n{}",
        violations.len(),
        outcomes.len(),
        violations.join("\n")
    );
}

// ===========================================================================
// The subject, through both compiled modes.
// ===========================================================================

// A `--run`/`--link` divergence is always a defect (root `CLAUDE.md`
// §Pipeline), and both modes were measured aborting pre-fix, so both are
// asserted here rather than trusting one to stand for the other.
// spec: spec/12-runtime.md §12.3.1 — a heap-allocated value MUST be freed when
// it is no longer reachable (1) and freed memory MUST NOT be accessed after
// deallocation (2); passing a captured value to a consuming callee transfers
// one reference, and spec/04-expressions.md §4.5.1 makes the closure's captured
// copy a value of its own, so the callee's consumption MUST NOT release the
// capture environment's reference.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/par_bind.rs::define_par_cont_body — the par continuation's captures were seeded into `inner.variables` with NO `variable_types` entry, so `apply.rs`'s consuming-argument gate (`lookup_type(name).is_some()`) classified a heap capture as a fresh temporary and emitted no consuming `rc_inc`; the callee's exit dec then consumed the closure environment's own reference and the closure drop glue dec'd it a second time, aborting on a freed pointer; the repair routes the same captures through `fn_compiler.rs::bind_capture` with the enclosing environment's type found=S121 owner=/dev fixed=S121
#[test]
fn par_continuation_heap_capture_survives_consuming_uses() {
    assert_clean_results(
        &[
            ("--run", run_prog(PAR_CONT_HEAP_CAPTURE, &[])),
            ("--link", link_then_run_prog(PAR_CONT_HEAP_CAPTURE)),
        ],
        "heap value captured into a par continuation, consumed twice",
    );
}

// ===========================================================================
// Controls. Each was GREEN on the pre-fix compiler, which is what attributes
// the subject's abort to the par-continuation CAPTURE of a HEAP value rather
// than to the program's other properties.
// ===========================================================================

// CONTROL — the binder moves inside the continuation, so nothing is captured.
// spec: spec/12-runtime.md §12.3.1(2) — a value bound inside the continuation
// and consumed there is released once; freed memory MUST NOT be accessed.
#[test]
fn continuation_local_binding_control_exits_clean() {
    assert_clean_results(
        &[("--run", run_prog(C1_BOUND_INSIDE_CONTINUATION, &[]))],
        "control: the heap value is bound INSIDE the continuation",
    );
}

// CONTROL — the captured value is a scalar, which owns no heap reference.
// spec: spec/12-runtime.md §12.3.1(2) — the requirement governs heap-allocated
// values; a captured `Int` carries no reference to release.
#[test]
fn scalar_capture_control_exits_clean() {
    assert_clean_results(
        &[("--run", run_prog(C2_SCALAR_CAPTURE, &[]))],
        "control: the captured value is a scalar",
    );
}

// CONTROL — one effect, so no `Par` is grouped and the capture reaches an
// ordinary lambda continuation.
// spec: spec/12-runtime.md §12.3.1(2) — the same consuming use through a
// non-par continuation MUST NOT access freed memory either.
#[test]
fn single_bind_no_par_capture_control_exits_clean() {
    assert_clean_results(
        &[("--run", run_prog(C3_SINGLE_BIND_NO_PAR, &[]))],
        "control: a single `bind`, so no `Par` is emitted",
    );
}

// CONTROL — the SUBJECT's own source with automatic IO scheduling switched off.
// One binary, one source, one environment variable apart from the subject cell
// above: it is the differential that attributes the fault to the scheduled
// lowering rather than to the program.
// spec: spec/12-runtime.md §12.4.3 — the structured fork-join of automatic IO
// scheduling is observationally equivalent to sequential evaluation, so the
// same source MUST answer identically with scheduling off, and §12.3.1(2)'s
// memory-safety requirement holds on both lowerings.
#[test]
fn io_scheduling_disabled_control_exits_clean() {
    assert_clean_results(
        &[(
            "--run",
            run_prog(PAR_CONT_HEAP_CAPTURE, &[(NO_IO_SCHEDULE_ENV, "1")]),
        )],
        "control: the subject with automatic IO scheduling disabled",
    );
}
