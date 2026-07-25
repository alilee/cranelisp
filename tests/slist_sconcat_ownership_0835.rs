// slist_sconcat_ownership_0835.rs — the permanent repros for FIXME 0835
// (`design/arch/fixmes/0835-slist-sexp-construction-corrupts-the-heap-at-small-sizes.md`),
// filed by `/stdlib` in S115 Phase 6b, ATTRIBUTED by `/qa` in S118 Phase 3
// (`tests/plan/s118-test-plan.md` §4.5; FIXME 0877 disposed into the ruling).
// Authored by `/testing` in S118 W1 per plan §2.3 / disposition 1 — which also
// discharges FIXME 0765's no-fix-without-a-repro precondition for the runtime
// fix.
//
// THE MECHANISM (ruled runtime-library-owned, NOT backend glue). Embedding a
// list as `sconcat`'s tail runs `marshal::deep_rc_inc_slist`
// (`crates/cranelisp-primitives/src/marshal.rs`, called by `sconcat`), which
// adds +1 to EVERY interior `SCons` node and every element — references no
// structural owner holds — while the intrinsics drop glue `consume_slist`
// (`crates/cranelisp-intrinsics/src/drop.rs`) correctly implements
// tree-ownership teardown (dec the head; descend only on the last reference).
// The interior +1s are therefore undischargeable. `/qa`'s falsification probe
// settled it empirically: the residual scales with the number of `sconcat` calls
// AND with `|ys|` at CONSTANT type-nesting depth, which falsifies the
// transitive-discharge (backend glue) hypothesis — whose residual would track
// type depth. Track-B backend slice S2 was removed from the backend wave on this
// evidence; the fix routes `/design`(intrinsics) → `/dev`(runtime pair).
//
// TWO FACES, ONE DEFECT. Undischargeable interior references are a LEAK; the
// same mis-ownership also hands the allocator inconsistent bookkeeping, and past
// ~6 cells glibc aborts. Both faces are pinned:
//
//   REPRO B — the leak face, `--run`, deterministic and exactly measurable.
//   REPRO A — the abort face on the test-runner path (`discover-tests` →
//             `/run-tests`), a SIGABRT (`free(): chunks in smallbin corrupted`),
//             measured 8/8 at HEAD.
//
// PROCESS-ABORT GUARD (the FIXME's request 1, and plan §2.3's requirement). The
// failure is a SIGABRT: a bare in-process value assertion would take the harness
// down with it. Every cell here runs the compiler in a FRESH SUBPROCESS through
// the `Cranelisp` builder (tests/CLAUDE.md §"Two tiers, no middle" /
// §"Fresh temp directory per test"), so an aborting child is captured as an exit
// STATUS this file asserts on — the harness process is never at risk. No cell
// touches an allocator internal and no cell arms a detector in this process.
//
// WHAT THE CELLS ASSERT — the spec-correct CONTRACT, never the fault signature
// (the `match_owned_temporary_scrutinee_0810.rs` discipline). Each cell demands
// (a) the program computes its documented value and terminates normally, and
// (b) `allocs == deallocs` EXACTLY. Asserting "it aborts" or "it leaks 4" would
// invert the moment the defect is fixed. The pairing also makes a partial fix
// unable to pass: a change that stops the abort while leaving the interior +1s
// still fails the balance half, and a change that balances the counters by
// releasing a genuinely shared tail fails the value half.
//
// LAYOUT SENSITIVITY IS NOT AN EXCUSE (tests/CLAUDE.md §"Failing-test
// discipline"). Which allocator face fires at which size varies — the FIXME
// records `corrupted double-linked list`, `free(): chunks in smallbin
// corrupted`, silent exit and hang for the same logical computation. That is the
// signature OF memory corruption, and it is why no cell here asserts a
// particular abort message or a particular exit code for the failure: the
// contract (right answer, clean exit, exact balance) is what is asserted, and it
// is violated deterministically today by at least one of its two halves in every
// cell — the leak half is exact and reproducible at every size.
//
// Free-standing: `PreludeVariant::PrimitivesOnly`, ZERO stdlib. The `macros`
// module (`SList`/`Sexp`/`sconcat`) is a synthetic bootstrap module
// (`src/bootstrap.rs`), not stdlib, so the FIXME's shapes reduce to
// compiler-only surface — a strictly smaller repro than the FIXME's own, whose
// repro A needed `core.syntax`/`testing` and whose repro B needed
// `core.syntax/sfold`.
//
// FIXME-0835 REPRO-A DRIFT, recorded honestly: the FIXME's original repro A was
// a TWO-cell list with NO `sconcat`, aborting on the stdlib runner path. That
// exact shape is GREEN at HEAD `e15ff20f` (4/4 clean runs, balanced). The abort
// face on the runner path now requires the `sconcat` ingredient, which is what
// `repro_a_*` below uses; the two-cell no-sconcat shape is retained as the
// `control_*` GREEN twin so a regression to the FIXME's original signature is
// still caught.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// ===========================================================================
// Shared program text
// ===========================================================================

/// `SList` plumbing every cell shares: a fold implemented as an ordinary
/// higher-order function (the shape the FIXME's `core.syntax/sfold` has, reduced
/// to compiler-only surface), a length over it, and the two-cell producer that
/// `sconcat` embeds as its tail.
const SLIST_PLUMBING: &str = "(import [macros [*]])\n\
     (defn sfold [f acc xs] (match xs [(SCons h t) (sfold f (f acc h) t) SNil acc]))\n\
     (defn slen [xs] (sfold (fn [n _] (add-i64 n 1)) 0 xs))\n\
     (defn two [] (SCons (SexpSym \"x\") (SCons (SexpBool true) SNil)))\n\
     (defn step [acc] (macros/sconcat acc (two)))\n";

/// `n` nested `step` applications over `SNil` — an `SList` of `2n` cells built
/// by `n` `sconcat` calls, each consuming freshly-allocated `SCons`/`Sexp` cells
/// in the same expression (the FIXME's identified corrupting ingredient; a
/// hand-chained `sconcat` over already-bound values does NOT reproduce).
fn steps(n: usize) -> String {
    let mut s = String::from("SNil");
    for _ in 0..n {
        s = format!("(step {s})");
    }
    s
}

// ===========================================================================
// Measurement — every run is a fresh subprocess; an abort is data, not a crash
// ===========================================================================

struct Measure {
    exit: Option<i32>,
    /// `None` when the child emitted no `[RC_STATS]` line — for a child that
    /// aborted before atexit that is expected, and is reported, never a silent
    /// pass.
    rc: Option<(i64, i64)>,
    stdout: String,
    stderr: String,
}

fn measure_run(program: &str) -> Measure {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user(program)
        .run("user.cl")
        .env("CRANELISP_RC_STATS", "1")
        .env("CRANELISP_NO_LENIENT", "1")
        .cli_flag("--no-cache")
        .output();
    Measure {
        exit: out.status.code(),
        rc: parse_rc(&out.stderr),
        stdout: out.stdout.clone(),
        stderr: out.stderr.clone(),
    }
}

fn measure_repl(lines: &str) -> Measure {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .env("CRANELISP_RC_STATS", "1")
        .env("CRANELISP_NO_LENIENT", "1")
        .output();
    Measure {
        exit: out.status.code(),
        rc: parse_rc(&out.stderr),
        stdout: out.stdout.clone(),
        stderr: out.stderr.clone(),
    }
}

fn parse_rc(stderr: &str) -> Option<(i64, i64)> {
    stderr
        .lines()
        .rev()
        .find(|l| l.contains("[RC_STATS]"))
        .and_then(|line| {
            let field = |k: &str| -> Option<i64> {
                line.split_whitespace()
                    .find_map(|t| t.strip_prefix(k).and_then(|v| v.parse().ok()))
            };
            Some((field("allocs=")?, field("deallocs=")?))
        })
}

/// The whole contract for a `--run` cell: the program computes `expect_exit`,
/// terminates normally (NOT a 134 glibc abort and not a signal), and balances
/// exactly. Ordered so the termination half reports first — a child that aborted
/// has no `[RC_STATS]` line to read.
fn assert_run_contract(label: &str, program: &str, expect_exit: i32) {
    let m = measure_run(program);
    assert_eq!(
        m.exit,
        Some(expect_exit),
        "[{label}] MUST compute {expect_exit} and terminate normally; got exit \
         {:?}. 134 = glibc abort (heap metadata corrupted by the undischargeable \
         interior references `deep_rc_inc_slist` adds); None = killed by a \
         signal.\nstdout:\n{}\nstderr:\n{}",
        m.exit,
        m.stdout,
        m.stderr
    );
    let (allocs, deallocs) = m.rc.unwrap_or_else(|| {
        panic!("[{label}] emitted no [RC_STATS] line:\nstderr:\n{}", m.stderr)
    });
    assert_eq!(
        allocs,
        deallocs,
        "[{label}] MUST balance EXACTLY: allocs={allocs} deallocs={deallocs} \
         (residue {}). Embedding a list as `sconcat`'s tail must take exactly \
         the references a structural owner holds; `deep_rc_inc_slist` incs every \
         interior node and element, and tree-ownership `consume_slist` cannot \
         discharge them.",
        allocs - deallocs
    );
}

// ===========================================================================
// REPRO B — the LEAK face (RED)
// ===========================================================================

// REPRO B, the FIXME's six-line no-macro no-runner shape reduced to compiler-only
// surface. ONE `sconcat` call over a freshly-built two-cell tail. Measured at
// HEAD `e15ff20f` through this file's own harness legs (`--run`, PrimitivesOnly,
// `--no-cache`, `CRANELISP_NO_LENIENT=1`, fresh tmpdir per run):
//
//   cell   sconcat calls   |ys|   allocs/deallocs   residual
//   C1       0 (control)     2        6 / 6              0
//   B1       1               2        7 / 4              3
//   B2       2               2       14 / 7              7
//   B4       1               4       12 / 6              6
//
// which reproduces `/qa`'s falsification-probe table (+3, +7, +6) name for name.
// The residual grows PER CALL and grows again with `|ys|` at constant type
// nesting (`SList<Sexp>` throughout) — `/qa`'s confirmation arm, reproduced here
// as a committed cell. The value is right in every row, which is why the balance
// half is the one that fires: this face is silent to anything that only watches
// for a crash.
// spec: spec/12-runtime.md §12.3.1 — a heap value MUST be freed when it is no
// longer reachable. Every interior `SCons` node of a consumed argument is
// unreachable once `sconcat` has taken over its cells.
// defect: class=rc-miscount locus=crates/cranelisp-primitives/src/marshal.rs::deep_rc_inc_slist vs crates/cranelisp-intrinsics/src/drop.rs::consume_slist — tail-embed incs every interior node/element while tree-ownership consume glue discharges only the head found=S115 owner=/dev
#[test]
fn repro_b_single_sconcat_tail_embed_balances() {
    let program = format!(
        "{SLIST_PLUMBING}(defn main [] (Pure (slen {})))\n",
        steps(1)
    );
    assert_run_contract("B1 one sconcat, |ys|=2", &program, 2);
}

// REPRO B scaled — the SAME shape at two and three chained `sconcat` calls. Two
// sizes are pinned because the property under test is a RATE: a fix that trims a
// constant residue while leaving the per-call leak would pass one size alone.
// The FIXME's own repro B is exactly the two-call row (`(slen (step (step
// SNil))))` = 4).
// spec: spec/12-runtime.md §12.3.1 — a heap value MUST be freed when it is no
// longer reachable; the requirement does not weaken with list length.
// defect: class=rc-miscount locus=crates/cranelisp-primitives/src/marshal.rs::deep_rc_inc_slist vs crates/cranelisp-intrinsics/src/drop.rs::consume_slist — per-call residual proportional to |ys| at constant type-nesting depth found=S115 owner=/dev
#[test]
fn repro_b_chained_sconcat_residual_does_not_grow_per_call() {
    let two = format!(
        "{SLIST_PLUMBING}(defn main [] (Pure (slen {})))\n",
        steps(2)
    );
    assert_run_contract("B2 two sconcat calls", &two, 4);
    let three = format!(
        "{SLIST_PLUMBING}(defn main [] (Pure (slen {})))\n",
        steps(3)
    );
    assert_run_contract("B3 three sconcat calls", &three, 6);
}

// REPRO B, the `|ys|` axis — ONE `sconcat` call embedding a FOUR-cell tail leaks
// more than the same call embedding a two-cell tail (6 vs 3 at HEAD) while the
// type nesting is identical in both. This is the cell that discriminates the
// ruled mechanism from the falsified one: a transitive-discharge (backend glue)
// defect's residual would track type depth, which does not move here.
// spec: spec/12-runtime.md §12.3.1 — a heap value MUST be freed when it is no
// longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-primitives/src/marshal.rs::deep_rc_inc_slist vs crates/cranelisp-intrinsics/src/drop.rs::consume_slist — residual scales with |ys| at constant type depth (the /qa falsification arm) found=S115 owner=/dev
#[test]
fn repro_b_longer_embedded_tail_balances() {
    let program = format!(
        "(import [macros [*]])\n\
         (defn sfold [f acc xs] (match xs [(SCons h t) (sfold f (f acc h) t) SNil acc]))\n\
         (defn slen [xs] (sfold (fn [n _] (add-i64 n 1)) 0 xs))\n\
         (defn four [] (SCons (SexpSym \"x\") (SCons (SexpBool true) \
         (SCons (SexpSym \"y\") (SCons (SexpBool false) SNil)))))\n\
         (defn main [] (Pure (slen (macros/sconcat SNil (four)))))\n"
    );
    assert_run_contract("B4 one sconcat, |ys|=4", &program, 4);
}

// ===========================================================================
// REPRO A — the ABORT face on the test-runner path (RED)
// ===========================================================================

// REPRO A — the FIXME's higher-value repro: the `SList` is built and dropped
// INSIDE a `test-*` function reached through `discover-tests` → the runner, not
// at the top level. Free-standing: `/run-tests` drives the same `discover-tests`
// primitive the stdlib runner does, so no stdlib touchpoint is needed.
//
// Measured at HEAD `e15ff20f`, 8/8 fresh subprocesses: exit 134 with
// `free(): chunks in smallbin corrupted`, aborting BEFORE the runner prints its
// tally. The assertion below is the contract — the runner reports the pass and
// the process terminates normally — so it flips GREEN when the runtime fix lands
// and cannot be satisfied by suppressing the diagnostic.
//
// This cell carries NO balance half: an aborting child never reaches atexit, so
// there is no `[RC_STATS]` line to read, and the balance property is already
// pinned exactly by the repro-B cells above on the same mechanism.
// spec: spec/12-runtime.md §12.3.1 — a heap value MUST NOT be freed while it is
// still reachable; a teardown that releases a reference no owner holds corrupts
// the allocator's own bookkeeping.
// defect: class=rc-miscount locus=crates/cranelisp-primitives/src/marshal.rs::deep_rc_inc_slist vs crates/cranelisp-intrinsics/src/drop.rs::consume_slist — abort face: undischargeable interior refs corrupt glibc heap metadata past ~6 cells found=S115 owner=/dev
#[test]
fn repro_a_slist_teardown_on_the_test_runner_path_does_not_abort() {
    let session = format!(
        "{SLIST_PLUMBING}\
         (defn test-six-cells [] (if (eq-i64 6 (slen {})) None (Some \"wrong length\")))\n\
         /run-tests\n",
        steps(3)
    );
    let m = measure_repl(&session);
    assert_eq!(
        m.exit,
        Some(0),
        "the test runner MUST complete normally over a `test-*` fn that builds \
         and drops a 6-cell SList; got exit {:?}. 134 = glibc abort (measured \
         `free(): chunks in smallbin corrupted` / `corrupted double-linked \
         list`); None = killed by a signal.\nstdout:\n{}\nstderr:\n{}",
        m.exit,
        m.stdout,
        m.stderr
    );
    assert!(
        m.stdout.contains("1 passed") && !m.stdout.contains("FAIL"),
        "the runner MUST report the single test as passing (the SList length IS \
         6 — this defect's leak face is silent to the assertion itself); \
         stdout:\n{}\nstderr:\n{}",
        m.stdout,
        m.stderr
    );
}

// REPRO A, the top-level twin — the SAME 6-cell value built and dropped at the
// REPL rather than through the runner. Measured aborting at HEAD
// (`corrupted double-linked list` / `free(): chunks in smallbin corrupted`; the
// harness reports a signalled child as `exit None`, and five consecutive
// per-binary runs are RED). It is pinned as a separate cell because the FIXME's
// controls used the runner path to argue the fault was runner-specific, and this
// cell falsifies that: the runner is an amplifier, not the mechanism.
// spec: spec/12-runtime.md §12.3.1 — a heap value MUST NOT be freed while it is
// still reachable.
// defect: class=rc-miscount locus=crates/cranelisp-primitives/src/marshal.rs::deep_rc_inc_slist vs crates/cranelisp-intrinsics/src/drop.rs::consume_slist — abort face reachable from ordinary top-level code, no runner involved found=S115 owner=/dev
#[test]
fn repro_a_top_level_six_cell_slist_teardown_does_not_abort() {
    let session = format!("{SLIST_PLUMBING}(slen {})\n", steps(3));
    let m = measure_repl(&session);
    assert_eq!(
        m.exit,
        Some(0),
        "a 6-cell `sconcat`-built SList MUST tear down without aborting the \
         process; got exit {:?}.\nstdout:\n{}\nstderr:\n{}",
        m.exit,
        m.stdout,
        m.stderr
    );
    assert!(
        m.stdout.contains(":primitives/Int 6"),
        "the session MUST print the correct length 6; stdout:\n{}\nstderr:\n{}",
        m.stdout,
        m.stderr
    );
}

// ===========================================================================
// DISCRIMINATING CONTROLS — GREEN today, and must stay GREEN
// ===========================================================================

// CONTROL — the identical `SList` shape built WITHOUT `sconcat` balances exactly
// (6/6 at HEAD) and exits with the right value. This is the sharp pair with
// repro B1: same type, same nesting, same fold, same teardown — the ONE variable
// isolated is whether a list was embedded as `sconcat`'s tail. It is also the
// fence against the wrong fix: making `consume_slist` walk deep would balance
// the leaking cells and BREAK this one, because a genuinely shared tail must not
// be torn down by the embedding list's release.
// spec: spec/12-runtime.md §12.3.1 — a heap value MUST be freed when it is no
// longer reachable, and MUST NOT be freed while it is.
#[test]
fn control_slist_built_without_sconcat_balances_green() {
    let program =
        format!("{SLIST_PLUMBING}(defn main [] (Pure (slen (two))))\n");
    assert_run_contract("C1 no sconcat", &program, 2);
}

// CONTROL — the FIXME's ORIGINAL repro A shape (a two-cell list, no `sconcat`,
// folded inside a `test-*` fn reached through the runner). It aborted when the
// FIXME was filed; it is GREEN at HEAD (4/4). Retained so a regression to the
// FIXME's own reported signature is caught, and so the drift is visible in the
// corpus rather than only in this file's header.
// spec: spec/12-runtime.md §12.3.1 — a heap value MUST be freed when it is no
// longer reachable.
#[test]
fn control_two_cell_slist_on_the_test_runner_path_green() {
    let session = format!(
        "{SLIST_PLUMBING}\
         (defn test-two-cell [] (if (eq-i64 2 (slen (two))) None (Some \"wrong length\")))\n\
         /run-tests\n"
    );
    let m = measure_repl(&session);
    assert_eq!(
        m.exit,
        Some(0),
        "the FIXME-0835 original repro-A shape MUST stay clean; got exit {:?}.\n\
         stdout:\n{}\nstderr:\n{}",
        m.exit,
        m.stdout,
        m.stderr
    );
    assert!(
        m.stdout.contains("1 passed"),
        "stdout:\n{}\nstderr:\n{}",
        m.stdout,
        m.stderr
    );
}
