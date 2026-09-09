// shadowed_param_reach_stale_rc_dec.rs — S121. Rows C and C′ of
// `design/typecheck/ownership-inference.md` §20.1: a `let` binder that reuses a
// PARAMETER's name, with the returned value minted from that parameter BEFORE
// the shadow. The two control cells differ from their subjects in EXACTLY ONE
// IDENTIFIER — the inner binder's name — so a RED that is really a harness or
// environment fault would take them down too.
//
// HISTORY. Every cell in this file is GREEN on the S121-repaired build; three
// of them were authored RED and are now regression guards. Two repairs closed
// them, in this order:
//
// 1. §20.3 (typecheck, 2026-09-07) — parameter reach carried as an INDEX,
//    replacing the name-keyed `ownership/transfer.rs::param_roots` walk, since
//    deleted from source. All four §20 subjects were RED at authoring (binary
//    sha256 d3c10369…, the S121 census binary); this closed three of them:
//    `allocs=3 deallocs=2` on both halves, marginal residual 0, no
//    `STALE RC DEC`, `--run`/`--link`/ownership-OFF in agreement.
//      was RED `shadowed_param_binder_run_does_not_abort_with_stale_rc_dec`
//      was RED `shadowed_param_binder_safety_matrix_run_and_link_agree`
//      was RED `shadowed_fresh_rhs_binder_rc_balance_matches_ownership_off`
//
// 2. The binder-scope repair (backend, S121 — `design/backend/binding-scope.md`,
//    per-binder scope slots replacing the flat name-keyed maps) closed the
//    remaining three:
//      was RED `binder_rename_must_not_change_rc_counters`
//      was RED `outer_local_binding_is_reachable_after_inner_shadow_scope_closes`
//      was RED `shadowed_outer_local_heap_value_is_not_leaked`
//
// `binder_rename_must_not_change_rc_counters` was NOT a §20 residual.
// `dev`(typecheck) ran the ownership control and `qa` classified the result:
// with the carrier out of the pipeline (`CRANELISP_NO_OWNERSHIP=1`) the
// subject/control RC asymmetry was unchanged and the published ABI summary was
// byte-identical across the pair, so the defect was ownership-independent and
// attributed to backend.
//
// Faces D and E were added at S121 when the backend probe fired the refuter QA
// had named on that cell: a shadow of a NON-parameter local lost the identical
// cell, so the mechanism was any shadowing rebinding, not collision with a
// parameter's name. Probing it one identifier away from the programs above
// produced those two further faces of the same seam (established in source —
// see the faces D/E section header). Their controls were GREEN throughout:
//   GREEN `renamed_binder_control_run_exits_clean`
//   GREEN `renamed_fresh_rhs_binder_control_safety_matrix_green`
//   GREEN `renamed_inner_binder_outer_ref_control_exits_clean`
//   GREEN `two_non_shadowing_renames_measure_zero_marginal_control`
//
// Each cell's own comment records what it measured before its repair, because
// that measurement is what makes the guard's assertions discriminating.
//
// Row B of §20.1 is deliberately absent: its measured program never returns the
// parameter at runtime, so it has no runtime face to pin.
//
// Absolute allocator balance is NOT an oracle for these programs: the renamed
// control itself exits with `allocs=3 deallocs=2` (the returned string is still
// live at exit), so the only truthful reading is the MARGINAL one against that
// control (tests/CLAUDE.md §"Allocator balance is measured MARGINALLY").
//
// Free-standing: `PreludeVariant::None`, every name imported from `primitives`,
// no stdlib (root CLAUDE.md §"Stdlib separation").

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant, assert_safety_matrix};
use helpers::marginal::{Child, MarginalPair};

// ===========================================================================
// Programs — §20.1 rows C and C′ and their one-identifier rename controls.
// Each returns `x`, which IS parameter `a` ("m"), so `main` exits 1.
// ===========================================================================

// Row C — SUBJECT. The inner `let` rebinds the name `a` to parameter `n`
// (an `Int`). `x` was minted from parameter `a` BEFORE the shadow.
const C_SHADOWED_PARAM: &str = "\
(import [primitives [str-len Pure]])
(defn f [a n]
  (let [x a]
    (let [a n]
      x)))
(defn main []
  (Pure (str-len (f \"m\" 1))))
";

// Row C — CONTROL. Identical but for the inner binder's name (`a` → `z`).
const D_RENAMED_CONTROL: &str = "\
(import [primitives [str-len Pure]])
(defn f [a n]
  (let [x a]
    (let [z n]
      x)))
(defn main []
  (Pure (str-len (f \"m\" 1))))
";

// Row C′ — SUBJECT. The shadow binder's RHS is a FRESH LITERAL reaching no
// parameter at all, and the same wrong ABI half was published for it. This face
// never aborted; it freed the argument string early and silently.
const C_PRIME_FRESH_RHS_SHADOW: &str = "\
(import [primitives [str-len Pure]])
(defn f [a n]
  (let [x a]
    (let [a \"q\"]
      x)))
(defn main []
  (Pure (str-len (f \"m\" 1))))
";

// Row C′ — CONTROL. Identical but for the inner binder's name (`a` → `w`).
const G_PRIME_RENAMED_CONTROL: &str = "\
(import [primitives [str-len Pure]])
(defn f [a n]
  (let [x a]
    (let [w \"q\"]
      x)))
(defn main []
  (Pure (str-len (f \"m\" 1))))
";

fn run_with_rc_stats(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .user(src)
        .env("CRANELISP_RC_STATS", "1")
        .output()
}

fn assert_no_stale_rc_dec(out: &helpers::e2e::CrOutput, what: &str) {
    assert!(
        !out.stderr.contains("STALE RC DEC"),
        "{what}: the runtime tripped the stale-dec guard — a still-live heap \
         value was dec'd after it had been freed and its chunk reclaimed.\n\
         exit: {:?}\nstderr:\n{}",
        out.status.code(),
        out.stderr
    );
}

// ===========================================================================
// Face C — the loud face, `--run`.
// ===========================================================================

// §20.1 row C. `(let [x a] (let [a n] x))` returns parameter `a`, so the
// program MUST exit 1 with no stale-dec abort. At authoring the published ABI
// half read `modes=[Borrowed, Copy] flow=[Consumed, Consumed]` while the result
// WAS parameter 0, the argument's return-protect was dropped, and the child died
// on `STALE RC DEC (consume_shallow)` (SIGABRT, exit 134). §20.3 closed that.
// spec: spec/04-expressions.md §4.3 — a `let` binding MAY shadow an outer
// binding of the same name; the inner binding takes precedence WITHIN ITS
// SCOPE, so a value bound before the shadow still denotes the parameter.
#[test]
fn shadowed_param_binder_run_does_not_abort_with_stale_rc_dec() {
    let out = run_with_rc_stats(C_SHADOWED_PARAM);
    assert_no_stale_rc_dec(&out, "shadowed-parameter binder under `--run`");
    assert_eq!(
        out.status.code(),
        Some(1),
        "`(f \"m\" 1)` returns the parameter \"m\", so `main` MUST exit 1.\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

// Row C CONTROL (GREEN) — the same program with the inner binder renamed `z`.
// One identifier apart from the subject: it pins the SHADOW, not the nesting,
// the `Int` parameter, or the harness, as what breaks the subject.
// spec: spec/04-expressions.md §4.3 — a distinctly-named inner binding leaves
// the outer parameter's reach untouched.
#[test]
fn renamed_binder_control_run_exits_clean() {
    let out = run_with_rc_stats(D_RENAMED_CONTROL);
    assert_no_stale_rc_dec(&out, "renamed-binder control under `--run`");
    assert_eq!(
        out.status.code(),
        Some(1),
        "the renamed control MUST exit 1.\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

// Face C through the differential-oracle matrix (MS-P1): modes × ownership
// toggle. `CRANELISP_NO_OWNERSHIP=1` — the conservative all-Owned reference
// semantics — makes this program exit cleanly, so an ON path diverging from it
// attributes the failure to the ownership elision rather than to codegen or to
// the program. The `--link` face is on the same cell because a memory-safety
// repro is not closed on the JIT alone; `qa` measured no `--run`/`--link`
// divergence, and this cell is what keeps that true.
// spec: spec/12-runtime.md §12.3.1 — a heap value MUST NOT be freed while it is
// still reachable; the ownership elision must agree with the conservative
// lowering in every mode.
#[test]
fn shadowed_param_binder_safety_matrix_run_and_link_agree() {
    assert_safety_matrix(C_SHADOWED_PARAM, PreludeVariant::None, 1);
}

// ===========================================================================
// Face C′ — the silent face. Exit code is NOT a sufficient oracle here.
// ===========================================================================

// §20.1 row C′. The shadow binder's RHS is a fresh literal, so nothing in the
// inner scope reaches a parameter — yet the same wrong ABI half was published.
// The program exited 1, correctly, while freeing the argument string early: the
// ownership-ON child reported `allocs=3 deallocs=3` where the conservative
// ownership-OFF reference reported `allocs=3 deallocs=2`. §20.3 closed that. The
// matrix's RC-balance face is the differential that sees this shape; exit code
// and `--link` do not, which is why the cell stays.
// spec: spec/12-runtime.md §12.3.1 — the ownership elision MUST NOT free a value
// the conservative lowering keeps live.
#[test]
fn shadowed_fresh_rhs_binder_rc_balance_matches_ownership_off() {
    assert_safety_matrix(C_PRIME_FRESH_RHS_SHADOW, PreludeVariant::None, 1);
}

// Row C′ CONTROL (GREEN) — inner binder renamed `w`. Same matrix, one
// identifier apart: the matrix does not false-positive on this shape.
// spec: spec/12-runtime.md §12.3.1 — a distinctly-named inner binding leaves the
// argument's lifetime alone in every mode.
#[test]
fn renamed_fresh_rhs_binder_control_safety_matrix_green() {
    assert_safety_matrix(G_PRIME_RENAMED_CONTROL, PreludeVariant::None, 1);
}

// ===========================================================================
// The rename-control RC parity oracle — QA's named instrument for C′.
// ===========================================================================

/// The counters a pure rename MUST leave untouched.
#[derive(Debug, PartialEq, Eq)]
struct RcCounters {
    rc_inc: i64,
    rc_dec: i64,
    allocs: i64,
    deallocs: i64,
}

fn rc_counters(stderr: &str, role: &str) -> RcCounters {
    let line = stderr
        .lines()
        .find(|l| l.contains("[RC_STATS]") && l.contains("allocs="))
        .unwrap_or_else(|| {
            panic!("{role}: no `[RC_STATS]` counter line — the child did not reach a normal exit.\nstderr:\n{stderr}")
        });
    let field = |k: &str| -> i64 {
        line.split_whitespace()
            .find_map(|t| t.strip_prefix(k).and_then(|v| v.parse().ok()))
            .unwrap_or_else(|| panic!("{role}: no `{k}` in: {line}"))
    };
    RcCounters {
        rc_inc: field("rc_inc="),
        rc_dec: field("rc_dec="),
        allocs: field("allocs="),
        deallocs: field("deallocs="),
    }
}

// The oracle `qa` allocated for the silent face: two programs that differ in
// EXACTLY ONE IDENTIFIER — the inner binder is `a` (shadowing parameter `a`) in
// the subject and `w` in the control — must produce identical RC traffic,
// because a rename changes no semantics and must change no codegen. Measured
// through the marginal harness so both children are spawned identically by
// construction (same binary, private tempdirs, `--run --no-cache`, `env_clear`
// + one allow-list).
//
// Authored RED, and not a §20 residual (see the header); closed by the S121
// binder-scope repair. Measured before that repair: control `rc_inc=3 rc_dec=4`
// against subject `rc_inc=2 rc_dec=3` — one inc and one dec short — with
// `allocs=3 deallocs=2` on both halves and the asymmetry unchanged under
// `CRANELISP_NO_OWNERSHIP=1`. Under `CRANELISP_RC_SITE_STATS` the subject was
// missing a materialisation site at the function's return value
// (`crossing_cells` 2 vs 1): one FEWER protect. Balanced on this program,
// unproven in general — nothing here witnessed a premature free, and neither
// exit code nor the absence of the abort string would have seen the difference
// at all. Only the parity did, which is why the cell is the instrument for this
// face and why it stays as the guard.
// spec: spec/12-runtime.md §12.3.1 — a heap value MUST remain live while it is
// still reachable, and renaming a local binder MUST NOT change that.
// defect: class=binder-name-underkey locus=crates/cranelisp-backend return-value materialisation site — MEASURED: the subject dropped one `crossing_cells` entry at the function's return value under CRANELISP_RC_SITE_STATS. The historical locus stays as recorded because the precise seam was never established from this cell alone; read `design/backend/binding-scope.md` and the faces D/E cells below for the mechanism the S121 repair converged on — the flat name-keyed binding environment could not tell two same-named binders apart, which the S121 backend probe confirmed by losing the identical cell for a shadow of a NON-parameter local found=S121 owner=/dev fixed=S121
#[test]
fn binder_rename_must_not_change_rc_counters() {
    let measured = MarginalPair::new(
        "inner let-binder renamed off a parameter's name (§20.1 row C′)",
        Child::new(G_PRIME_RENAMED_CONTROL),
        Child::new(C_PRIME_FRESH_RHS_SHADOW),
    )
    .measure();

    let control = rc_counters(&measured.control().stderr, "control (inner binder `w`)");
    let subject = rc_counters(&measured.subject().stderr, "subject (inner binder `a`)");

    assert_eq!(
        control,
        subject,
        "renaming the inner `let` binder off the parameter's name changed the \
         program's RC traffic. A rename has no semantics to change, so the \
         difference is in codegen, not in the program. Attributed to backend; \
         the seam is not established — see this test's defect annotation.\n  \
         control (`w`): {control:?}\n  subject (`a`): {subject:?}\n{}",
        measured.report()
    );
}

// ===========================================================================
// Faces D and E — the OUTER binding a shadow destroys.
//
// Rows C and C′ above shadow a PARAMETER and never look at the shadowed name
// again. The two subjects below do look at what the shadow displaced: face D
// references the outer binding BY NAME once the inner scope has closed, face E
// only through the release the function still owes it. Both shadow a plain
// `let` local rather than a parameter, deliberately — the S121 probe's refuter
// established the mechanism is ANY shadowing rebinding, so the minimal
// statement of it uses no parameter at all.
//
// The seam was established from source, not hypothesised. `FnCompiler::pop_scope`
// (`crates/cranelisp-backend/src/compiler/fn_compiler.rs`) popped a frame by
// REMOVING every name that frame introduced from the flat, name-keyed
// `variables` and `variable_types` maps. Nothing was held to restore from, so an
// inner binding of an outer name did not shadow it — it DELETED it, and the
// structure was correct only while every binder name in a function was unique.
// (`borrowed_stack`, a fourth map on the same axis, was given its own frame
// stack at S114 W4 / FIXME 0692 for exactly this reason; these were not.) The
// S121 repair replaced the flat maps with per-binder scope slots
// (`design/backend/binding-scope.md`); both cells below are its guards.
//
// Spec authority, read at S121:
//   • spec/04-expressions.md §Notation — "The environment `E` is a chain of
//     lexical scopes: local bindings (from `let`, `fn`, `match`) shadow
//     module-scope names." A chain restores; a flat map cannot.
//   • spec/04-expressions.md §4.3 "Shadowing" — "A binding MAY shadow an outer
//     binding of the same name. The inner binding takes precedence WITHIN ITS
//     SCOPE", with §4.3's environment-EXTENSION rule (`E[x1 -> v1] |- e2 => v2`)
//     and "bindings go out of scope after `body` is evaluated". Outside the
//     inner scope the outer binding is in force again — face D's subject is a
//     legal program and MUST compile.
//   • spec/12-runtime.md §12.3.1(1) — heap-allocated values "MUST be freed when
//     they are no longer reachable from any live binding or data structure",
//     restated for `let` in §4.3 ("Any heap-allocated values bound by `let` that
//     are not captured by a closure or returned from the body become eligible
//     for deallocation"). Face E's subject did not free the outer local's
//     string before the repair.
//
// Each subject is ONE IDENTIFIER from its control — the inner binder `b` → `c`
// — so a RED that were really a harness, environment or nesting-depth fault
// would take the control down with it.
// ===========================================================================

// Face D — SUBJECT. `b` is bound to a string; the innermost `let` rebinds the
// name `b` to the `Int` parameter INSIDE ITS OWN SCOPE. Once that scope closes,
// `b` denotes "hello" again, so `(str-len b)` is 5 and `main` exits 5.
const OUTER_REF_AFTER_SHADOW: &str = "\
(import [primitives [str-len Pure]])
(defn f [n]
  (let [b \"hello\"]
    (let [z (let [b n] b)]
      (str-len b))))
(defn main []
  (Pure (f 7)))
";

// Face D — CONTROL. Identical but for the innermost binder's name (`b` → `c`),
// which shadows nothing.
const OUTER_REF_AFTER_RENAME_CONTROL: &str = "\
(import [primitives [str-len Pure]])
(defn f [n]
  (let [b \"hello\"]
    (let [z (let [c n] c)]
      (str-len b))))
(defn main []
  (Pure (f 7)))
";

// Face E — SUBJECT. The same shadow, but the outer `b` is never referenced
// again: the only thing owed to it is its release when `f` returns. `f` yields
// the `Int` 7, so `main` exits 7 whether or not the string is freed — the exit
// code is NOT an oracle for this face, which is why it is measured marginally.
const OUTER_LOCAL_RELEASE_SHADOWED: &str = "\
(import [primitives [Pure]])
(defn f [n]
  (let [b \"hello\"]
    (let [z (let [b n] b)]
      z)))
(defn main []
  (Pure (f 7)))
";

// Face E — CONTROL. Innermost binder `b` → `c`; shadows nothing.
const OUTER_LOCAL_RELEASE_RENAME_CONTROL: &str = "\
(import [primitives [Pure]])
(defn f [n]
  (let [b \"hello\"]
    (let [z (let [c n] c)]
      z)))
(defn main []
  (Pure (f 7)))
";

// Face E — the CONTROL's own twin, one identifier from it (`c` → `w`) and
// likewise shadowing nothing. Paired against the control it gives the
// instrument's zero polarity on this program shape: a rename BY ITSELF must
// measure nothing, so the subject cell's reading is attributable to the shadow.
const OUTER_LOCAL_RELEASE_RENAME_CONTROL_TWIN: &str = "\
(import [primitives [Pure]])
(defn f [n]
  (let [b \"hello\"]
    (let [z (let [w n] w)]
      z)))
(defn main []
  (Pure (f 7)))
";

/// Drive `src` through `--run` and through `--link`-then-run, returning both
/// outcomes. Two modes because a `--run`/`--link` divergence is itself a defect
/// (root `CLAUDE.md` §Pipeline) and because a repair that reached only the JIT
/// path must not be able to pass this cell.
fn run_and_link_outcomes(src: &str) -> Vec<(&'static str, helpers::e2e::CrOutput)> {
    vec![
        ("--run", run_with_rc_stats(src)),
        (
            "--link",
            Cranelisp::new()
                .with_prelude(PreludeVariant::None)
                .link_then_run("user.cl")
                .user(src)
                .env("CRANELISP_RC_STATS", "1")
                .output(),
        ),
    ]
}

/// The face-D contract, applied identically to the subject and to its rename
/// control — the twin-fixture shape (`tests/CLAUDE.md` §"Coverage by definition
/// variants"): one invariant, two programs one identifier apart, SAME
/// assertion, so the failing twin names the site by itself.
fn assert_outer_local_binding_survives_the_inner_scope(src: &str, role: &str) {
    for (mode, out) in run_and_link_outcomes(src) {
        assert!(
            !out.stderr.contains("absent from the backend scope stack"),
            "{role} under `{mode}`: the compiler REFUSED a legal program. Once \
             the inner `let`'s scope closes, `b` denotes the outer binding again \
             (spec/04-expressions.md §4.3 — the inner binding takes precedence \
             WITHIN ITS SCOPE), but the backend's binding environment no longer \
             holds it: `pop_scope` removed the name instead of restoring what it \
             meant outside the frame.\nexit: {:?}\nstderr:\n{}",
            out.status.code(),
            out.stderr
        );
        assert_eq!(
            out.status.code(),
            Some(5),
            "{role} under `{mode}`: `b` is \"hello\" outside the inner scope, so \
             `(str-len b)` is 5 and `main` MUST exit 5.\nstdout:\n{}\nstderr:\n{}",
            out.stdout,
            out.stderr
        );
    }
}

// Face D — the LOUD face: a spec-conforming program was refused at codegen with
// `internal invariant violation (VarRef::Local): binder 'b' for reference 'b'
// is absent from the backend scope stack`. Repaired at S121; this cell is the
// regression guard. Measured at authoring, before the repair (binary sha256
// dafe264c…, HEAD 18bca20d + the user's dirty tree): subject exit 1 with that
// message under BOTH `--run` and `--link`; the rename control exited 5 in both.
// The assertion names the message because the exit code alone would not
// distinguish this refusal from any other compile failure.
// spec: spec/04-expressions.md §4.3 — a `let` binding MAY shadow an outer
// binding of the same name; the inner binding takes precedence WITHIN ITS
// SCOPE, so once that scope closes the outer binding is in force again and a
// reference to the name MUST resolve to it.
// defect: class=binder-name-underkey locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::pop_scope — the flat name-keyed `variables`/`variable_types` maps were popped by REMOVE, so an inner shadow DELETED the outer binding instead of restoring it, and the reference after the scope closed missed in `literals.rs::compile_var`; the loud face of the one keying mechanism found=S121 owner=/dev fixed=S121
#[test]
fn outer_local_binding_is_reachable_after_inner_shadow_scope_closes() {
    assert_outer_local_binding_survives_the_inner_scope(
        OUTER_REF_AFTER_SHADOW,
        "shadowed outer local, referenced after the inner scope closes",
    );
}

// Face D CONTROL (GREEN) — the same program with the innermost binder renamed
// `c`. One identifier apart from the subject and driven through the SAME
// assertion: it pins the SHADOW, not the three-deep nesting, the `Int`
// parameter, the `str-len` call or the harness, as what breaks the subject.
// spec: spec/04-expressions.md §4.3 — a distinctly-named inner binding leaves
// the outer local reachable after its scope closes.
#[test]
fn renamed_inner_binder_outer_ref_control_exits_clean() {
    assert_outer_local_binding_survives_the_inner_scope(
        OUTER_REF_AFTER_RENAME_CONTROL,
        "renamed innermost binder (shadows nothing)",
    );
}

// Face E — the SILENT face, and the one that matters on the default path: the
// outer local's string was never freed. Nothing aborts, the exit code is
// correct, and no diagnostic is printed — only the allocator accounting sees
// it, so the marginal pair IS the instrument. Repaired at S121; this cell is
// the regression guard. Measured at authoring, before the repair: subject
// `allocs=2 deallocs=1`, control `allocs=2 deallocs=2` ⇒ MARGINAL residual +1,
// unchanged under `CRANELISP_NO_OWNERSHIP=1` (so the defect was not in the
// ownership elision) and deterministic over repeats. One leaked object per
// call, so the same shadow inside a loop or a recursive function leaked
// without bound.
// spec: spec/12-runtime.md §12.3.1 — a heap-allocated value MUST be freed when
// it is no longer reachable from any live binding; §4.3 says a `let`-bound heap
// value not captured or returned becomes eligible for deallocation when its
// binding goes out of scope, and shadowing its name does not make it live.
// defect: class=binder-name-underkey locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::pop_scope — the outer binding's TYPE was removed from `variable_types` by the inner frame's pop, so `collect_frame_heap_decs` filtered the binding out of the release set and the outer local's drop glue was never called (a single missing `call fn0(v2)` in CLIF); same seam as the face-D cell, opposite direction — silent rather than loud found=S121 owner=/dev fixed=S121
#[test]
fn shadowed_outer_local_heap_value_is_not_leaked() {
    let measured = MarginalPair::new(
        "an inner `let` binder shadowing an outer local's name",
        Child::new(OUTER_LOCAL_RELEASE_RENAME_CONTROL),
        Child::new(OUTER_LOCAL_RELEASE_SHADOWED),
    )
    .measure();

    assert_eq!(
        measured.subject().exit_code(),
        Some(7),
        "the subject MUST still yield 7 — this cell is about the string it \
         leaves behind, not about its result.\n{}",
        measured.report()
    );
    measured.assert_balanced(
        "shadowing an outer local's name leaked that local's heap value: the \
         outer binding's release is owed when `f` returns (spec/12-runtime.md \
         §12.3.1), and the two programs differ in one identifier, so the \
         difference is in codegen and not in the program.",
    );
}

// Face E CONTROL (GREEN) — the instrument's zero polarity on this exact program
// shape. Two children that BOTH rename the innermost binder (`c` and `w`) and
// so both shadow nothing: a rename by itself must move no counter. Without this
// cell the subject's +1 could be read as the marginal reacting to renaming
// rather than to shadowing.
// spec: spec/12-runtime.md §12.3.1 — renaming a local binder that shadows
// nothing changes no value's reachability, and so must change no allocation
// accounting.
#[test]
fn two_non_shadowing_renames_measure_zero_marginal_control() {
    let measured = MarginalPair::new(
        "two non-shadowing renames of the innermost binder (`c` against `w`)",
        Child::new(OUTER_LOCAL_RELEASE_RENAME_CONTROL),
        Child::new(OUTER_LOCAL_RELEASE_RENAME_CONTROL_TWIN),
    )
    .measure();

    assert_eq!(
        measured.subject().exit_code(),
        Some(7),
        "the control twin MUST yield 7.\n{}",
        measured.report()
    );
    measured.assert_balanced(
        "two programs that differ only in a binder name, NEITHER of them \
         shadowing, measured a non-zero marginal — the instrument is reacting \
         to the rename itself, which would invalidate the subject cell above.",
    );
}
