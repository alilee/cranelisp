// match_owned_temporary_scrutinee_0810.rs — the pin batch for FIXME 0810
// (`design/arch/fixmes/0810-match-over-owned-adt-temporary-leaks-or-over-releases.md`),
// filed by `/port` in S115 Phase 6a with a complete measured repro. Authored by
// `/testing` in the S115 Phase-6b pin batch; the FIXME stays OPEN as the record
// until the fix lands — these cells are its trigger.
//
// THE DEFECT — two polarities of ONE seam: the release of an OWNED TEMPORARY
// scrutinee under a CONSTRUCTOR pattern
// (`crates/cranelisp-backend/src/compiler/match_codegen.rs`). FIXME 0782 is the
// VAR-pattern sibling of the same seam; the two cross-reference each other and a
// fix that closes only one is a partial fix.
//
//   FACE A — the scrutinee spelled INLINE leaks the wrapper.
//     `(match (mk i) [(Mk v) …])` in a tail loop: the `Mk` box is allocated every
//     iteration and never released. Slope is exactly 1 object/iteration; with a
//     HEAP payload the box AND its Vec field strand together, slope 2.
//
//   FACE B — the SAME program with the scrutinee LET-BOUND over-releases it.
//     The wrapper IS released, but the extracted payload goes with it, so the
//     next loop iteration reads freed memory: SIGBUS in `--run`, heap-corruption
//     abort in `--link`. RC balances (102/102) precisely BECAUSE the free happens
//     — balance alone cannot see this polarity, which is why the Face-B cells
//     assert the computed VALUE, not just a number.
//
//   There is therefore NO correct spelling for this shape today: inline leaks it,
//   let-bound frees it too early.
//
// MEASURED AT HEAD (`/testing`, 2026-07-21, `CRANELISP_NO_LENIENT=1`
// `CRANELISP_RC_STATS=1`, reproducing `/port`'s Phase-6a numbers exactly):
//
//   cell                                    N=100            N=1100         slope
//   A1 inline call-wrapper, Int payload     101 / 1          1101 / 1        1
//   A2 inline CONSTRUCTOR, no call at all   101 / 1          1101 / 1        1
//   A3 inline call-wrapper, heap payload    201 / 1          2201 / 1        2
//   A4 wrapper-from-call ⇒ tail loop param  103 / 3          1103 / 3        1
//   B1 let-bound scrutinee, tail loop       exit 135 (SIGBUS) / --link 134
//   B2 B1 with the result outer-matched     exit 1 `match failed`, 102 / 102
//   C1 CONTROL let-bound, Int payload       101 / 101        1101 / 1101     GREEN
//   C2 CONTROL match in a callee (Borrowed) 101 / 101        1101 / 1101     GREEN
//
// PRE-EXISTING, not an S115 regression: `/port` measured the same numbers at
// `4d20cea1` (pre-S115-RC-wave) and at HEAD.
//
// TOGGLE-INDEPENDENT (measured, every cell): ownership analysis ON and
// `CRANELISP_NO_OWNERSHIP=1` (the conservative all-Owned oracle) produce
// IDENTICAL exits and IDENTICAL alloc/dealloc counts. The differential RC face
// is therefore structurally BLIND to this class — both lowerings share the
// fault — which is exactly the FIXME-0761 blindness that made
// `gen_ownership_flows.rs` assert exact balance rather than a differential.
// Every cell below pins BOTH toggles anyway, so a future "fix" that merely
// suppresses the analysis cannot flip them.
//
// MODE-INDEPENDENT (measured): `--run` and `--link` agree on every cell.
//
// WHAT THESE CELLS ASSERT — the SPEC-CORRECT CONTRACT, never the fault
// signature. Each cell demands (a) the program computes its documented value,
// abort-free, and (b) `allocs == deallocs` EXACTLY. Asserting "it crashes" or
// "it leaks" would invert the moment the defect is fixed; asserting the contract
// flips GREEN and stays a regression guard forever.
//
// WHY BOTH HALVES ARE ON EVERY CELL — the partial-fix trap (dispatch
// deliverable 2). The two faces are opposite polarities of one decision, so a
// one-sided fix is the likely failure mode:
//   - a fix that cures Face B by going back to LEAKING passes the value half of
//     B1/B2 but fails their BALANCE half (and leaves A1–A4 RED);
//   - a fix that cures Face A by releasing the inline temporary the way the
//     let-bound path already does turns A1–A4 into the Face-B over-release and
//     fails their VALUE half;
//   - a fix that merely stops the ABORT (e.g. suppressing the fault) without
//     curing the over-release still fails B2, whose symptom is a WRONG TAG read
//     off freed memory (`match failed`) and not a fault at all.
// Only a fix that releases the wrapper exactly once, after the payload has been
// extracted and taken over, turns the whole file GREEN.
//
// EXEMPLAR STAKE: `/port`'s Phase-6a attribution shows this defect is ~99.6% of
// the Sudoku exemplar's ~11.8k-objects-per-solve residue (the old FIXME 0720
// figure) — 11,767 of 11,820 objects, all from `solver/eliminate` returning
// `(Some g)` into a Face-A match. It is not a corner case.
//
// Stdlib-free (`PrimitivesOnly`; root CLAUDE.md §Design Principles).
// `CRANELISP_NO_LENIENT=1` on every run: the loops have no sparks, and it keeps
// the RC counts deterministic (tests/CLAUDE.md §"RC tests run serially").

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// ===========================================================================
// Measurement
// ===========================================================================

/// One subprocess run's observable facts. `rc: None` means the run emitted no
/// `[RC_STATS]` line at all — for a crashing run that is expected and is
/// reported as such; it is never a silent pass.
struct Measure {
    exit: Option<i32>,
    rc: Option<(i64, i64)>,
    stderr: String,
}

fn measure(program: &str, ownership_off: bool, link: bool) -> Measure {
    let mut b = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user(program)
        .env("CRANELISP_RC_STATS", "1")
        .env("CRANELISP_NO_LENIENT", "1");
    b = if link {
        b.link_then_run("user.cl")
    } else {
        b.run("user.cl")
    };
    if ownership_off {
        b = b.env("CRANELISP_NO_OWNERSHIP", "1");
    }
    let out = b.output();
    // The LAST `[RC_STATS]` line: under `--link` the compiler process and the
    // produced binary both emit one, and the produced binary's is last.
    let rc = out
        .stderr
        .lines()
        .rev()
        .find(|l| l.contains("[RC_STATS]"))
        .and_then(|line| {
            let field = |k: &str| -> Option<i64> {
                line.split_whitespace()
                    .find_map(|t| t.strip_prefix(k).and_then(|v| v.parse().ok()))
            };
            Some((field("allocs=")?, field("deallocs=")?))
        });
    Measure {
        exit: out.status.code(),
        rc,
        stderr: out.stderr.clone(),
    }
}

/// The whole contract for one cell, in one mode, in one toggle state: the
/// program computes `expect_exit`, abort-free, with `allocs == deallocs`.
///
/// Both halves apply in `--link` too. Under `--link` the compiler process emits
/// its own (empty) `[RC_STATS]` line before the produced binary emits the real
/// one, so `measure` takes the LAST line; the exit assertion runs first, which
/// means the balance half is only ever reached on a run whose binary actually
/// executed to completion and therefore contributed that last line.
fn assert_contract(label: &str, program: &str, expect_exit: i32, ownership_off: bool, link: bool) {
    let m = measure(program, ownership_off, link);
    let toggle = if ownership_off {
        "CRANELISP_NO_OWNERSHIP=1"
    } else {
        "ownership ON"
    };
    let mode = if link { "--link" } else { "--run" };
    assert_eq!(
        m.exit,
        Some(expect_exit),
        "[{label}] {mode} ({toggle}) MUST compute {expect_exit} and exit cleanly; \
         got exit {:?}. 135 = SIGBUS / 134 = heap-corruption abort (the Face-B \
         over-release: the wrapper was freed while its extracted payload was still \
         live); 1 with `match failed` = a wrong tag read off the freed box.\n\
         stderr:\n{}",
        m.exit,
        m.stderr
    );
    let (allocs, deallocs) = m.rc.unwrap_or_else(|| {
        panic!(
            "[{label}] {mode} ({toggle}) emitted no [RC_STATS] line:\n{}",
            m.stderr
        )
    });
    assert_eq!(
        allocs,
        deallocs,
        "[{label}] {mode} ({toggle}) MUST balance EXACTLY: allocs={allocs} \
         deallocs={deallocs} (residue {}). Every `match` scrutinee this frame \
         owns is released exactly once, after the arm has taken over its payload.",
        allocs - deallocs
    );
}

/// The `--run` × {ownership ON, OFF} legs — the balance-bearing pair. Every cell
/// runs these; the faces are measured toggle-independent, so a divergence here
/// is itself new information.
fn assert_both_toggles(label: &str, program: &str, expect_exit: i32) {
    assert_contract(label, program, expect_exit, false, false);
    assert_contract(label, program, expect_exit, true, false);
}

// ===========================================================================
// The programs
// ===========================================================================

/// FACE A cell 1 / CONTROL C1 share this shape modulo the scrutinee spelling.
/// `mk` returns a fresh `Mk` wrapper; the loop matches it and folds the payload.
/// The answer is `sum(0..n) mod 256`.
fn inline_call_wrapper(n: i64) -> String {
    format!(
        "(deftype B (Mk [v]))\n\
         (defn mk [n] (Mk n))\n\
         (defn go [i n acc]\n\
         \x20 (if (eq-i64 i n) acc\n\
         \x20   (match (mk i)\n\
         \x20     [(Mk v) (go (add-i64 i 1) n (add-i64 acc v))])))\n\
         (defn main [] (Pure (go 0 {n} 0)))\n"
    )
}

/// CONTROL C1 — the identical program with the scrutinee LET-BOUND and an Int
/// payload. GREEN today.
fn let_bound_int_payload(n: i64) -> String {
    format!(
        "(deftype B (Mk [v]))\n\
         (defn mk [n] (Mk n))\n\
         (defn go [i n acc]\n\
         \x20 (if (eq-i64 i n) acc\n\
         \x20   (let [b (mk i)]\n\
         \x20     (match b [(Mk v) (go (add-i64 i 1) n (add-i64 acc v))]))))\n\
         (defn main [] (Pure (go 0 {n} 0)))\n"
    )
}

/// FACE A cell 2 — the scrutinee is an inline CONSTRUCTOR expression; there is no
/// call anywhere, which is what rules out "a post-call-seam artifact".
fn inline_constructor_no_call(n: i64) -> String {
    format!(
        "(deftype B (Mk [v]))\n\
         (defn go [i n acc]\n\
         \x20 (if (eq-i64 i n) acc\n\
         \x20   (match (Mk i)\n\
         \x20     [(Mk v) (go (add-i64 i 1) n (add-i64 acc v))])))\n\
         (defn main [] (Pure (go 0 {n} 0)))\n"
    )
}

/// FACE A cell 3 — HEAP payload. The box and its Vec field strand together, so
/// the slope doubles: this is the cell that proves the leak is the whole
/// scrutinee object graph, not just the wrapper header.
fn inline_call_wrapper_heap_payload(n: i64) -> String {
    format!(
        "(deftype B (Mk [v]))\n\
         (defn mk [n] (Mk [n n n]))\n\
         (defn go [i n acc]\n\
         \x20 (if (eq-i64 i n) acc\n\
         \x20   (match (mk i)\n\
         \x20     [(Mk v) (go (add-i64 i 1) n acc)])))\n\
         (defn main [] (Pure (go 0 {n} 7)))\n"
    )
}

/// FACE A cell 4 — the exemplar's own shape: a wrapper returned by a called
/// function whose PAYLOAD supersedes a tail-recursive loop parameter. This is
/// `solver/eliminate` returning `(Some g)` reduced to two ADTs.
fn wrapper_from_call_supersedes_loop_param(n: i64) -> String {
    format!(
        "(deftype G (Gr [cells]))\n\
         (deftype O (Non) (Jus [g]))\n\
         (defn step [g i] (Jus g))\n\
         (defn go [g i n]\n\
         \x20 (if (eq-i64 i n) g\n\
         \x20   (match (step g i)\n\
         \x20     [Non g\n\
         \x20      (Jus g2) (go g2 (add-i64 i 1) n)])))\n\
         (defn main [] (Pure (match (go (Gr [1 2 3]) 0 {n}) [(Gr c) 7])))\n"
    )
}

/// FACE B — the cell-4 program with the scrutinee LET-BOUND. The wrapper is
/// released while `g2` (its payload) is still the live loop parameter.
fn let_bound_scrutinee_supersedes_loop_param(n: i64) -> String {
    format!(
        "(deftype G (Gr [cells]))\n\
         (deftype O (Non) (Jus [g]))\n\
         (defn step [g i] (Jus g))\n\
         (defn go [g i n]\n\
         \x20 (if (eq-i64 i n) g\n\
         \x20   (let [r (step g i)]\n\
         \x20     (match r\n\
         \x20       [Non g\n\
         \x20        (Jus g2) (go g2 (add-i64 i 1) n)]))))\n\
         (defn main [] (let [x (go (Gr [1 2 3]) 0 {n})] (Pure 7)))\n"
    )
}

/// FACE B sibling — the same loop, but the caller MATCHES the returned `Gr`
/// instead of dropping it. The freed box's tag is read back wrong, so this one
/// does not fault at all: it exits 1 with `runtime panic: match failed`.
fn let_bound_scrutinee_result_outer_matched(n: i64) -> String {
    format!(
        "(deftype G (Gr [cells]))\n\
         (deftype O (Non) (Jus [g]))\n\
         (defn step [g i] (Jus g))\n\
         (defn go [g i n]\n\
         \x20 (if (eq-i64 i n) g\n\
         \x20   (let [r (step g i)]\n\
         \x20     (match r\n\
         \x20       [Non g\n\
         \x20        (Jus g2) (go g2 (add-i64 i 1) n)]))))\n\
         (defn main [] (Pure (match (go (Gr [1 2 3]) 0 {n}) [(Gr c) 7])))\n"
    )
}

/// CONTROL C2 — the `match` moved INSIDE a callee, over a `Borrowed` parameter.
/// GREEN today: the callee does not own the scrutinee, so the seam under test is
/// never reached. This is the cell the generative harness already covers.
fn match_in_callee_on_borrowed_param(n: i64) -> String {
    format!(
        "(deftype B (Mk [v]))\n\
         (defn mk [n] (Mk n))\n\
         (defn peek [b] (match b [(Mk v) v]))\n\
         (defn go [i n acc]\n\
         \x20 (if (eq-i64 i n) acc\n\
         \x20   (go (add-i64 i 1) n (add-i64 acc (peek (mk i))))))\n\
         (defn main [] (Pure (go 0 {n} 0)))\n"
    )
}

// `sum(0..N) mod 256` — the answer the folding cells must produce.
const SUM_100: i32 = 86; // 4950 mod 256
const SUM_1100: i32 = 34; // 604450 mod 256

// ===========================================================================
// FACE A — the inline scrutinee leaks the wrapper (RED)
// ===========================================================================

// A1 — the base face. `(match (mk i) [(Mk v) …])` in a tail loop allocates one
// `Mk` box per iteration and frees none: N=100 → 101/1, N=1100 → 1101/1. Two Ns
// are pinned because the property under test is a SLOPE — a fix that trims a
// constant residue while leaving the per-iteration leak would pass one N alone.
// spec: spec/12-runtime.md §12.3.1 — a heap value MUST be freed when it is no
// longer reachable. The `Mk` wrapper is unreachable the moment its arm has taken
// the payload.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/match_codegen.rs — owned temporary scrutinee under constructor patterns (0782 is the var-pattern sibling) found=S115 owner=/dev
#[test]
fn inline_call_wrapper_scrutinee_does_not_leak() {
    assert_both_toggles("A1 N=100", &inline_call_wrapper(100), SUM_100);
    assert_both_toggles("A1 N=1100", &inline_call_wrapper(1100), SUM_1100);
}

// A1-link — the `--link` face of A1. Measured identical to `--run` (101/1,
// exit 86), so this cell exists to keep the mode-independence pinned: a fix that
// lands only on the JIT path is a `mode-divergence` defect in its own right.
// spec: spec/12-runtime.md §12.3.1 — the requirement is on the language, not on
// a mode; `--run` and `--link` MUST agree.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/match_codegen.rs — owned temporary scrutinee under constructor patterns, `--link` face found=S115 owner=/dev
#[test]
fn inline_call_wrapper_scrutinee_does_not_leak_linked() {
    assert_contract(
        "A1 N=100 link",
        &inline_call_wrapper(100),
        SUM_100,
        false,
        true,
    );
}

// A2 — the scrutinee is an inline CONSTRUCTOR with no call at all. Same
// 101/1 and 1101/1. This is the discriminating cell for the attribution: the
// leak is the match's release of an owned temporary, NOT anything about the
// post-call seam or a returned value's ownership summary.
// spec: spec/06-pattern-matching.md §6.2.1 — a constructor pattern destructures
// the scrutinee; the scrutinee object itself is the matching frame's to release.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/match_codegen.rs — owned temporary scrutinee under constructor patterns (inline-ctor face, no call) found=S115 owner=/dev
#[test]
fn inline_constructor_scrutinee_does_not_leak() {
    assert_both_toggles("A2 N=100", &inline_constructor_no_call(100), SUM_100);
    assert_both_toggles("A2 N=1100", &inline_constructor_no_call(1100), SUM_1100);
}

// A3 — HEAP payload: slope 2, not 1 (N=100 → 201/1, N=1100 → 2201/1). The box
// and its Vec field strand TOGETHER, which means the missing release is the
// scrutinee's whole drop-glue call, not a single header dec. A fix that decs the
// wrapper header without running its glue would halve this cell and still fail
// it — which is the point of pinning the heap-payload face separately.
// spec: spec/12-runtime.md §12.3.1 — freeing a value frees the heap values it
// solely owns.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/match_codegen.rs — owned temporary scrutinee under constructor patterns, heap-payload face (box + field strand together) found=S115 owner=/dev
#[test]
fn inline_scrutinee_with_heap_payload_does_not_leak_box_or_field() {
    assert_both_toggles("A3 N=100", &inline_call_wrapper_heap_payload(100), 7);
    assert_both_toggles("A3 N=1100", &inline_call_wrapper_heap_payload(1100), 7);
}

// A4 — the exemplar's shape: a wrapper returned BY A CALL whose payload
// supersedes a tail-loop parameter (N=100 → 103/3, N=1100 → 1103/3). This is the
// cell that carries the ~11.8k/solve exemplar residue; A1–A3 are its reductions.
// spec: spec/12-runtime.md §12.3.1 — the superseded wrapper is unreachable at the
// tail jump and MUST be freed there.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/match_codegen.rs — owned temporary scrutinee under constructor patterns, wrapper-from-call superseding a tail-loop param (the exemplar shape) found=S115 owner=/dev
#[test]
fn wrapper_from_call_superseding_loop_param_does_not_leak() {
    assert_both_toggles("A4 N=100", &wrapper_from_call_supersedes_loop_param(100), 7);
    assert_both_toggles(
        "A4 N=1100",
        &wrapper_from_call_supersedes_loop_param(1100),
        7,
    );
}

// ===========================================================================
// FACE B — the let-bound scrutinee is over-released (RED, memory corruption)
// ===========================================================================

// B1 — the SAME program as A4 with the scrutinee spelled as a `let` binding.
// `--run` exit 135 (SIGBUS, core dumped), `--link` exit 134 — at EVERY N,
// including N=1, in BOTH toggle states. RC balances 102/102 precisely because
// the wrapper IS freed; the payload `g2` goes with it and the next iteration
// reads freed memory.
//
// This cell asserts exit 7 AND exact balance together, which is what makes a
// partial fix unable to pass: curing the fault by going back to leaking (the
// Face-A behaviour) satisfies the exit assertion and fails the balance one.
// spec: spec/06-pattern-matching.md §6.3.2 — a pattern binding is in scope for
// its arm body, and the value it names outlives the match when the body returns
// it. Freeing the scrutinee must not free what the arm bound out of it.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/match_codegen.rs — let-bound owned scrutinee released while its extracted payload is still live (0782 is the var-pattern sibling) found=S115 owner=/dev
#[test]
fn let_bound_scrutinee_payload_outlives_the_match() {
    assert_both_toggles("B1 N=1", &let_bound_scrutinee_supersedes_loop_param(1), 7);
    assert_both_toggles(
        "B1 N=100",
        &let_bound_scrutinee_supersedes_loop_param(100),
        7,
    );
}

// B1-link — the `--link` face. Measured exit 134 (glibc heap-corruption abort)
// where `--run` gives 135; the two mode faces of one over-release. Pinned
// separately because `--link` is the release gate and because heap corruption is
// mode-sensitive in its SYMPTOM while identical in its cause.
// spec: spec/06-pattern-matching.md §6.3.2 — same requirement, `--link` mode.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/match_codegen.rs — let-bound owned scrutinee over-release, `--link` face (exit 134) found=S115 owner=/dev
#[test]
fn let_bound_scrutinee_payload_outlives_the_match_linked() {
    assert_contract(
        "B1 N=100 link",
        &let_bound_scrutinee_supersedes_loop_param(100),
        7,
        false,
        true,
    );
}

// B2 — the same loop with its RESULT outer-matched instead of dropped. This cell
// does NOT fault: it exits 1 with `runtime panic: match failed`, having read a
// wrong tag off the freed box, and its RC balances 102/102. It is the cell that
// makes "the abort stopped" insufficient as a fix criterion — a silent wrong
// value is the worse half of this defect, and only a VALUE assertion sees it.
// spec: spec/06-pattern-matching.md §6.2.1 — a constructor pattern matches on the
// scrutinee's live tag; a `(Gr c)` match on a live `Gr` MUST succeed.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/match_codegen.rs — let-bound owned scrutinee over-release surfacing as a wrong-tag read (`match failed`) rather than a fault found=S115 owner=/dev
#[test]
fn let_bound_scrutinee_loop_result_still_matches_its_own_tag() {
    assert_both_toggles(
        "B2 N=100",
        &let_bound_scrutinee_result_outer_matched(100),
        7,
    );
}

// B2-link — the `--link` face of B2: exit 134 rather than the `--run` exit 1,
// because the linked allocator notices the corruption the JIT run tolerates.
// spec: spec/06-pattern-matching.md §6.2.1 — same requirement, `--link` mode.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/match_codegen.rs — let-bound owned scrutinee over-release, outer-match `--link` face (exit 134) found=S115 owner=/dev
#[test]
fn let_bound_scrutinee_loop_result_still_matches_its_own_tag_linked() {
    assert_contract(
        "B2 N=100 link",
        &let_bound_scrutinee_result_outer_matched(100),
        7,
        false,
        true,
    );
}

// ===========================================================================
// THE VAR-PATTERN SIBLING — FIXME 0782, pinned here on purpose (RED)
// ===========================================================================

// 0782 is the SAME seam under a VAR pattern instead of a constructor pattern:
// an owned temporary scrutinee whose arm CONSUMES it is released twice
// (`compile_var_pattern_arm`'s `is_alias` scope cleanup AND `compile_match`'s
// `dec_temporary_scrutinee`). It was filed by `/dev` in W4c explicitly WITHOUT a
// fix because "choosing which of the two releases is correct is a seam decision
// better made with `/testing` cover in place", and it had no committed repro.
//
// It lives in THIS file rather than its own because 0782 and 0810 are one seam
// decision with two polarities — 0782 releases an owned temporary TWICE, 0810
// (Face A) releases it ZERO times — and a fix that picks an owner for one
// pattern kind while leaving the other alone is precisely the partial fix these
// cells exist to catch. Whichever release path `/dev` deletes, BOTH pattern
// kinds must end up releasing exactly once.
//
// MEASURED at HEAD (2026-07-21): `--run` exit 8 with allocs=2 deallocs=2 — the
// double-dec does not perturb the alloc counters at all, so `--run` alone reads
// GREEN. Only `--link` is a deterministic signal: exit 134,
// `corrupted double-linked list`, both toggles. That asymmetry is itself the
// lesson — the `--run` + RC-balance instrument this file otherwise relies on is
// blind to a double-release of a value that was going to be freed anyway.
// spec: spec/06-pattern-matching.md §6.2.4 — a variable pattern binds the whole
// scrutinee for the arm; the scrutinee object is released once, by one owner.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/match_codegen.rs::compile_var_pattern_arm — var-pattern arm consuming an owned temporary scrutinee releases it twice (0810 is the constructor-pattern sibling) found=S115 owner=/dev
#[test]
fn var_pattern_arm_consuming_owned_temporary_releases_it_once_linked() {
    let program = "(defn f [] (match [7 8 9] [xs (vec-get xs 1)]))\n\
                   (defn main [] (Pure (f)))\n";
    assert_contract("0782 var-pattern link", program, 8, false, true);
    assert_contract("0782 var-pattern link", program, 8, true, true);
}

// 0782 CONTROL — the identical program with the scrutinee spelled as a BINDING
// is clean (exit 8, 2/2, `--link` included). Note that this is the OPPOSITE
// polarity from C1-vs-B1 above: under a var pattern the let-bound spelling is
// the correct one, under a constructor pattern with an escaping payload it is
// the broken one. That inversion is why the seam needs one derived answer rather
// than a per-spelling rule.
// spec: spec/06-pattern-matching.md §6.2.4 — same requirement, binding scrutinee.
#[test]
fn control_var_pattern_arm_over_let_bound_scrutinee_linked() {
    let program = "(defn f [] (let [v [7 8 9]] (match v [xs (vec-get xs 1)])))\n\
                   (defn main [] (Pure (f)))\n";
    assert_contract("0782 control link", program, 8, false, true);
}

// ===========================================================================
// DISCRIMINATING CONTROLS (METHOD §2.2) — GREEN today, and must stay GREEN
// ===========================================================================

// C1 — a let-bound scrutinee with an INT payload balances exactly (101/101,
// 1101/1101) in both toggles and both modes. C1 vs B1 is the sharp pair in this
// file: the SAME spelling change, opposite outcomes. The variable isolated is
// whether the extracted payload OUTLIVES the match (B1 feeds it to a tail-call
// loop parameter; C1 consumes an Int in place) — not the `let`, not the match,
// not the ADT.
//
// C1 is also the fence that stops the obvious wrong fix for Face A: "release the
// inline temporary the way the let-bound path does" would turn A1 into B1. C1
// says the let-bound path is only correct when nothing escapes the arm.
// spec: spec/12-runtime.md §12.3.1 — a let-bound owned scrutinee whose payload
// does not escape the arm is freed exactly once.
#[test]
fn control_let_bound_int_payload_scrutinee_balances() {
    assert_both_toggles("C1 N=100", &let_bound_int_payload(100), SUM_100);
    assert_both_toggles("C1 N=1100", &let_bound_int_payload(1100), SUM_1100);
}

// C1-link — the `--link` face of the sharp pair's GREEN half, so that the
// B1-link RED is read against a same-mode GREEN rather than against `--run`.
// spec: spec/12-runtime.md §12.3.1 — same requirement, `--link` mode.
#[test]
fn control_let_bound_int_payload_scrutinee_balances_linked() {
    assert_contract(
        "C1 N=100 link",
        &let_bound_int_payload(100),
        SUM_100,
        false,
        true,
    );
}

// C2 — `match` performed INSIDE a callee on a `Borrowed` parameter balances
// exactly (101/101, 1101/1101). The callee never owns the scrutinee, so the seam
// under test is not reached at all. This is the shape the generative harness
// `gen_ownership_flows.rs` already generates (its `bxlen` reader is exactly this
// program), and it is why that harness runs green over all 45 cells while the
// defect above is live — see FIXME 0830.
// spec: spec/12-runtime.md §12.3.1 — a borrowed parameter is not the callee's to
// release; the caller's temporary is freed once at the caller.
#[test]
fn control_match_in_callee_on_borrowed_param_balances() {
    assert_both_toggles("C2 N=100", &match_in_callee_on_borrowed_param(100), SUM_100);
    assert_both_toggles(
        "C2 N=1100",
        &match_in_callee_on_borrowed_param(1100),
        SUM_1100,
    );
}
