// same_form_rebinding.rs — S121. **Rebinding a name a second time inside ONE
// `let` binding vector**: `(let [a 1 a (+ a 1)] a)`.
//
// User ruling (2026-09-08): this is legal. The second initializer is evaluated
// in the environment extended by every PRECEDING binding, so it reads the first
// `a`; the new binding then displaces it for everything after. That is exactly
// §4.3's inference rule applied with `x1 == x2` — no new rule, no exception —
// and the user's chosen example evaluates to `2`.
//
// Spec authority, read at S121:
//   • spec/04-expressions.md §4.3 — the environment-EXTENSION rule
//     (`E |- e1 => v1`, `E[x1 -> v1] |- e2 => v2`, …) plus "Sequential
//     visibility: each binding can refer to previously bound names in the same
//     `let`" and "Shadowing: … the inner binding takes precedence within its
//     scope". Nothing in §4.3 requires the binder names to be distinct; the only
//     stated binder constraints are the even-form-count rule and the bare-symbol
//     rule, and this program satisfies both.
//   • spec/04-expressions.md §4.3 — "Any heap-allocated values bound by `let`
//     that are not captured by a closure or returned from the body become
//     eligible for deallocation", and spec/12-runtime.md §12.3.1 — a heap value
//     MUST be freed when it is no longer reachable. A DISPLACED binding is
//     unreachable from the moment its name is rebound, so its value is owed a
//     release no later than the `let`'s exit.
//   • spec/12-runtime.md §12.4.3 — "A `let` binding is independent if its free
//     variables do not include any name bound earlier in the same `let` block",
//     and "Lenient evaluation is semantically transparent — programs MUST NOT
//     depend on whether any particular binding or argument is parallelized."
//
// HISTORY. Two cells here were authored RED (2026-09-08; HEAD 18bca20d + the
// user's dirty tree — the S121 census source tree), and the S121 binder-scope
// repair (`design/backend/binding-scope.md` — per-binder scope slots replacing
// the flat name-keyed maps) closed both. Every cell in the file is GREEN on the
// repaired build; the two former REDs are now regression guards:
//   was RED `lenient_spark_reads_the_rebound_value_not_the_displaced_one`
//   was RED `displaced_same_form_binding_heap_value_is_not_leaked`
// Their pre-repair numbers were first measured on the census build (binary
// sha256 dafe264c…) and re-measured identically on the pre-repair build the
// cells were authored against (sha256 a913bc3a…); the two differ only by a
// relink. Each cell's own comment records what it measured then, because that
// measurement is what makes the guard's assertions discriminating; the class
// and locus are on its `defect:` line.
//
// The two were DIFFERENT seams of one keying mechanism, and neither was the
// `pop_scope` face pinned by `tests/shadowed_param_reach_stale_rc_dec.rs`
// (which shadows across NESTED scopes; here there is one scope and one binding
// vector):
//   • the lenient/spark face was a name-keyed dependency map in the lenient
//     decision + emission pair, and it produced a WRONG VALUE;
//   • the heap face was the displaced binding's release, and it was silent —
//     correct result, one object leaked per call.
//
// Free-standing: `PreludeVariant::None` (or `TestStandard` for the one cell that
// runs the user's example verbatim with `+`), every other name imported from
// `primitives`, no stdlib (root CLAUDE.md §"Stdlib separation").

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{CrOutput, Cranelisp, PreludeVariant};
use helpers::marginal::{Child, MarginalPair};

// ===========================================================================
// The user's example, and the same shape driven through `--run` / `--link`.
// ===========================================================================

/// The user's example verbatim. `+` is a prelude trait method, so this one cell
/// runs under `PreludeVariant::TestStandard`; every other program in this file
/// is `PreludeVariant::None` + explicit `primitives` imports.
const USER_EXAMPLE_TURN: &str = "(let [a 1 a (+ a 1)] a)\n";

/// The user's example as a module, free-standing (`add-i64` for `+`), so the
/// same shape can be observed through `--run` and `--link` where the result is
/// the process exit code.
const USER_EXAMPLE_MODULE: &str = "\
(import [primitives [add-i64 Pure]])
(defn main []
  (Pure (let [a 1 a (add-i64 a 1)] a)))
";

// The ruling's own example, at the boundary it was stated at (the REPL). The
// second initializer reads the FIRST `a` (§4.3 sequential visibility), then the
// second binding displaces it, so the body sees `2` and not `1`. This is a
// POSITIVE control — it passed before the S121 binder-scope repair as well as
// after it, and this cell exists to keep it passing.
// spec: spec/04-expressions.md §4.3 — each binding's value is computed in the
// environment extended by all preceding bindings, and a binding MAY shadow an
// outer binding of the same name.
#[test]
fn user_example_same_form_rebinding_evaluates_to_two_in_repl() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin(USER_EXAMPLE_TURN)
        .output()
        .assert_stdout_contains(":primitives/Int 2");
}

// The same shape through the two compiled modes. A `--run`/`--link` divergence
// is always a defect (root `CLAUDE.md` §Pipeline), and the REPL cell above
// cannot see one.
// spec: spec/04-expressions.md §4.3 — sequential visibility inside one binding
// vector: `a`'s second initializer reads the first `a`, and the body reads the
// second.
#[test]
fn same_form_rebinding_initializer_reads_preceding_binding_run_and_link() {
    for (mode, out) in run_and_link(USER_EXAMPLE_MODULE) {
        assert_eq!(
            out.status.code(),
            Some(2),
            "{mode}: `(let [a 1 a (add-i64 a 1)] a)` is 2 — the second \
             initializer reads the first `a`, the body reads the second.\n\
             stdout:\n{}\nstderr:\n{}",
            out.stdout,
            out.stderr
        );
    }
}

// ===========================================================================
// Face 1 — lenient evaluation reads the DISPLACED binding (wrong value).
//
// `ping`/`pong` are MUTUALLY recursive on purpose. The default spark-admission
// filter (`CRANELISP_SPARK_ADMIT=mstatic`) admits a candidate only when its
// callee is in a recursive SCC of the static call graph, and the call graph's
// `callees` feed drops self-edges — so a merely SELF-recursive callee is not
// admitted when called from another function, and no `let`-path spark site is
// created at all (measured: a self-recursive `sum-to` in the identical program
// shape emits no `[SPARK_SITE_STATS]` line and no spark). Mutual recursion is
// the smallest shape that reaches the `let` spark path from a caller's binding
// vector.
//
// `ping n` = n + (n-1) + … + 1 = n(n+1)/2, so ping(3)=6, ping(5)=15, ping(6)=21.
// ===========================================================================

/// The two mutually-recursive definitions every program in this section shares.
const PING_PONG: &str = "\
(import [primitives [add-i64 sub-i64 lt-i64 Pure]])
(defn pong [n] (if (lt-i64 n 1) 0 (add-i64 n (ping (sub-i64 n 1)))))
(defn ping [n] (if (lt-i64 n 1) 0 (add-i64 n (pong (sub-i64 n 1)))))
";

fn ping_pong_program(body: &str) -> String {
    format!("{PING_PONG}(defn f [n]\n{body})\n(defn main [] (Pure (f 3)))\n")
}

// SUBJECT. `a` is bound to an expensive call, then REBOUND to the cheap literal
// `5`, then read by `c`. By §4.3, `c`'s initializer sees the SECOND `a`, so
// `c` = ping(5) = 15.
const REBIND_SUBJECT_BODY: &str = "\
  (let [a (ping n)
        a 5
        c (ping a)]
    c)";

// CONTROL, one identifier from the subject: the FIRST binder is `q`, so nothing
// is rebound. `c` reads the only `a` there is — still the literal `5` — so the
// correct answer is unchanged at 15.
const RENAME_FIRST_BINDER_CONTROL_BODY: &str = "\
  (let [q (ping n)
        a 5
        c (ping a)]
    c)";

// CONTROL, no rebinding at all: the arming case for this whole section. `c`
// depends on the sparked `a`, `a` is not displaced, and the answer is
// ping(ping(3)) = ping(6) = 21.
const DEPENDENT_SPARK_CONTROL_BODY: &str = "\
  (let [a (ping n)
        c (ping a)]
    c)";

// CONTROL / REFUTER: `a` is rebound, but to ANOTHER expensive call rather than
// to a cheap literal. `c` reads the second `a` = ping(4) = 10, so
// `c` = ping(10) = 55.
const REBIND_SPARK_WITH_SPARK_BODY: &str = "\
  (let [a (ping n)
        a (ping 4)
        c (ping a)]
    c)";

/// Drive `src` through the three modes a language-semantics cell must agree
/// across (root `CLAUDE.md` §Pipeline). The REPL observation loads the program
/// as `user.cl` and evaluates `(main)`; typing the two mutually-recursive
/// definitions as separate turns cannot work (the first forward-references the
/// second), which is a REPL turn-model property and not this feature's concern.
fn all_three_modes(src: &str) -> Vec<(&'static str, CrOutput, Option<i32>)> {
    let repl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::None)
        .user(src)
        .stdin("(main)\n")
        .output();
    let repl_observed = parse_repl_int(&repl.stdout);
    let mut out = vec![("REPL", repl, repl_observed)];
    for (mode, o) in run_and_link(src) {
        let code = o.status.code();
        out.push((mode, o, code));
    }
    out
}

fn run_and_link(src: &str) -> Vec<(&'static str, CrOutput)> {
    vec![
        (
            "--run",
            Cranelisp::new()
                .with_prelude(PreludeVariant::None)
                .run("user.cl")
                .user(src)
                .output(),
        ),
        (
            "--link",
            Cranelisp::new()
                .with_prelude(PreludeVariant::None)
                .link_then_run("user.cl")
                .user(src)
                .output(),
        ),
    ]
}

/// The single `:primitives/Int N` the REPL printed for `(main)`.
fn parse_repl_int(stdout: &str) -> Option<i32> {
    stdout
        .split(":primitives/Int ")
        .nth(1)
        .and_then(|rest| rest.split_whitespace().next())
        .and_then(|tok| tok.parse().ok())
}

/// One invariant, applied identically to the subject and to each of its
/// controls — the twin-fixture shape (`tests/CLAUDE.md` §"Coverage by
/// definition variants"): the programs are one identifier apart and go through
/// the SAME assertion, so the failing twin names the site by itself.
fn assert_rebound_value_is_read(body: &str, expected: i32, role: &str) {
    let src = ping_pong_program(body);
    for (mode, out, observed) in all_three_modes(&src) {
        assert_eq!(
            observed,
            Some(expected),
            "{role} under `{mode}`: `c`'s initializer is evaluated in the \
             environment extended by ALL preceding bindings, so the `a` it \
             reads is the LAST one bound before it (spec/04-expressions.md \
             §4.3). Expected {expected}.\nstdout:\n{}\nstderr:\n{}",
            out.stdout,
            out.stderr
        );
    }
}

// Face 1 — the loud face: a WRONG VALUE, silently. Repaired at S121; this cell
// is the regression guard.
//
// Measured at authoring, before the repair, in all three modes: 21 where the
// spec requires 15. 21 was ping(6) = ping(ping(3)) — the value of the FIRST
// `a`, the one the rebinding displaced. The same program with
// `CRANELISP_NO_LENIENT=1` answered 15 (the control cell below), so the
// divergence was between the lenient and sequential lowerings of ONE program,
// which §12.4.3 forbids outright.
//
// Source seam as it stood then, read at S121 and consistent with the
// measurement: `sparkability.rs::find_sparkable_bindings_with` tracked admitted
// bindings in a name-keyed `sparked_names: HashSet<Symbol>` and only ever
// INSERTED. A binding that rebound an already-sparked name without itself being
// admitted left the stale entry in place, so a later binding's dependency check
// (`fv.filter(bound).all(|v| sparked_names.contains(v))`) reported the
// dependency as available-as-an-IVar and admitted it.
// `let_if.rs::compile_let_lenient` then resolved that dependency through the
// equally name-keyed `sparked_name_to_ivar`, which held the DISPLACED binding's
// IVar — so the dependent thunk forced the displaced value. §12.4.3's own
// independence rule says `c` is not independent at all ("its free variables …
// include a name bound earlier in the same `let` block"), which is what the
// carve-out was mis-answering.
//
// Why the assertion is shaped this way: NOT sparking `c` is a conforming
// outcome (§12.4.3's parallelisation permission is a MAY at the level of any
// particular binding), so this cell deliberately asserts only the VALUE and
// never that a spark fired. The arming cell below is what keeps the spark path
// exercised.
// spec: spec/12-runtime.md §12.4.3 — lenient evaluation is semantically
// transparent; a program MUST NOT depend on whether any binding is
// parallelized, and a binding whose free variables include a name bound earlier
// in the same `let` block is not independent.
// defect: class=binder-name-underkey locus=crates/cranelisp-backend/src/compiler/control_flow/sparkability.rs::find_sparkable_bindings_with — the name-keyed `sparked_names` reach-set was insert-only, so a non-admitted rebinding of an already-sparked name left a stale entry and a later dependent binding was admitted against an IVar holding the DISPLACED value (`let_if.rs::compile_let_lenient`'s `sparked_name_to_ivar` was name-keyed on the same axis); the wrong-VALUE face of the one keying mechanism found=S121 owner=/dev fixed=S121
#[test]
fn lenient_spark_reads_the_rebound_value_not_the_displaced_one() {
    assert_rebound_value_is_read(
        REBIND_SUBJECT_BODY,
        15,
        "a sparked binding rebound to a cheap value, then read",
    );
}

// CONTROL (GREEN) — the SAME program, with lenient evaluation switched off by
// the §12.4.3 opt-out. Measured at authoring: 15, correct, in `--run` and
// `--link`. This is the differential that attributes the subject's 21 to the
// lenient lowering and not to the program, the mutual recursion, or the
// harness: one binary, one source, one environment variable apart.
// spec: spec/12-runtime.md §12.4.3 — an implementation MAY provide an opt-out
// for lenient evaluation, and the sequential lowering it selects is the
// reference semantics the lenient one must reproduce.
#[test]
fn lenient_disabled_control_reads_the_rebound_value() {
    let src = ping_pong_program(REBIND_SUBJECT_BODY);
    for (mode, out) in [
        (
            "--run",
            Cranelisp::new()
                .with_prelude(PreludeVariant::None)
                .run("user.cl")
                .user(&src)
                .env("CRANELISP_NO_LENIENT", "1")
                .output(),
        ),
        (
            "--link",
            Cranelisp::new()
                .with_prelude(PreludeVariant::None)
                .link_then_run("user.cl")
                .user(&src)
                .env("CRANELISP_NO_LENIENT", "1")
                .output(),
        ),
    ] {
        assert_eq!(
            out.status.code(),
            Some(15),
            "{mode} with `CRANELISP_NO_LENIENT=1`: the sequential lowering of \
             the subject program MUST read the rebound `a` (5) and answer \
             ping(5) = 15.\nstdout:\n{}\nstderr:\n{}",
            out.stdout,
            out.stderr
        );
    }
}

// CONTROL (GREEN) — one identifier from the subject (the first binder `a` → `q`),
// so nothing is rebound and the correct answer is unchanged at 15. It pins the
// REBINDING, not the three-binding vector, the mutual recursion, the cheap
// literal, or the harness, as what breaks the subject.
// spec: spec/04-expressions.md §4.3 — a distinctly-named earlier binding leaves
// the later binding's reference resolving to the binding that actually precedes
// it.
#[test]
fn distinctly_named_displaced_binder_control_reads_the_rebound_value() {
    assert_rebound_value_is_read(
        RENAME_FIRST_BINDER_CONTROL_BODY,
        15,
        "distinctly-named first binder (nothing is rebound)",
    );
}

// ARMING CELL (GREEN) — the detection proof for the section. A cell family that
// never reaches the lenient dependent-binding path would be GREEN for a reason
// that has nothing to do with the defect, and the subject above deliberately
// cannot assert that a spark fired (declining to spark is a conforming repair).
// This program is the subject minus the rebinding: `c` depends on the sparked
// `a`, the site is admitted, and both bindings spark. Measured at authoring and
// over ten repeats: `[SPARK_STATS] spawns=2 serial_continues=0`, two
// `[SPARK_SITE_STATS] … admit=true` lines for `f`'s binding vector, and the
// correct answer ping(ping(3)) = ping(6) = 21.
//
// The runtime spark count is asserted as well as the compile-time admission,
// because admission alone does not prove the lenient ARM ran — the create-gate
// (`let_if.rs::emit_create_gate`) can still take the sequential arm when the
// spark budget is exhausted, and that path would answer 21 too.
// spec: spec/12-runtime.md §12.4.3 — an implementation MUST evaluate
// independent `let` bindings in parallel where its cost heuristic determines it
// is beneficial; a binding that depends only on an earlier parallelised binding
// is joined at its use.
#[test]
fn dependent_spark_without_a_rebinding_is_admitted_and_correct() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .user(&ping_pong_program(DEPENDENT_SPARK_CONTROL_BODY))
        .env("CRANELISP_SPARK_STATS", "1")
        .output();

    assert_eq!(
        out.status.code(),
        Some(21),
        "the no-rebinding control MUST answer ping(ping(3)) = 21.\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    assert!(
        out.stderr.contains("admit=true"),
        "no admitted spark site: the `let`-path lenient decision never accepted \
         this binding vector, so every cell in this section would be GREEN for a \
         reason unrelated to lenient evaluation.\nstderr:\n{}",
        out.stderr
    );
    let spawns = parse_spark_spawns(&out.stderr);
    assert!(
        spawns.is_some_and(|n| n >= 1),
        "no spark actually ran (`[SPARK_STATS] spawns={spawns:?}`): admission \
         happened at compile time but the create-gate took the sequential arm, \
         so the lenient EMISSION path this section is about was never \
         executed.\nstderr:\n{}",
        out.stderr
    );
}

/// `spawns=N` out of the `[SPARK_STATS]` atexit line, if the child printed one.
fn parse_spark_spawns(stderr: &str) -> Option<u64> {
    stderr
        .lines()
        .find(|l| l.contains("[SPARK_STATS]"))?
        .split_whitespace()
        .find_map(|t| t.strip_prefix("spawns=")?.parse().ok())
}

// CONTROL / REFUTER (GREEN) — `a` is still rebound, but to another expensive
// call, so the rebinding is ITSELF admitted as a spark and overwrites the
// name→IVar entry rather than leaving it stale. Measured at authoring:
// `spawns=3` and the correct ping(ping(4)) = ping(10) = 55.
//
// This is what narrowed the subject's defect from "rebinding a name" to
// "rebinding a SPARKED name with a NON-sparked value". If this cell ever goes
// RED alongside the subject, the mechanism is wider than the annotation on the
// subject records and the class is /qa's to re-rule.
// spec: spec/12-runtime.md §12.4.3 — lenient evaluation is semantically
// transparent; the value a binding's reference reads is the last one bound
// before it (spec/04-expressions.md §4.3), whether or not either was
// parallelised.
#[test]
fn rebinding_one_spark_with_another_spark_reads_the_rebound_value() {
    assert_rebound_value_is_read(
        REBIND_SPARK_WITH_SPARK_BODY,
        55,
        "a sparked binding rebound to another sparked value",
    );
}

// ===========================================================================
// Face 2 — the displaced binding's heap value was never released (silent).
// Repaired at S121; these cells are the regression guards.
//
// One scope, one binding vector, no nesting, no parameter: the smallest program
// in which a name is bound twice and the first value becomes unreachable at the
// second binding. Both subjects answer correctly, so the exit code is NOT an
// oracle here and the marginal pair IS the instrument (`tests/CLAUDE.md`
// §"Allocator balance is measured MARGINALLY").
//
// Source seam as it stood then, read at S121: `let_if.rs::compile_let_sequential`
// inserted each binder into the flat, name-keyed `variables` / `variable_types`
// maps and pushed the NAME onto the current scope frame. A second binding of the
// same name overwrote the maps — the first binder's Cranelift `Variable` became
// unreachable — while the frame carried that one name twice, so the
// frame-cleanup release set could no longer name the displaced value at all.
// Same name-keyed-binding-environment axis as `fn_compiler.rs::pop_scope`
// (`tests/shadowed_param_reach_stale_rc_dec.rs` faces D and E), reached without
// any nesting.
// ===========================================================================

// SUBJECT (the user's example shape at heap type): the second initializer reads
// the first `s`, exactly as `(let [a 1 a (+ a 1)] a)` does.
const HEAP_READ_PRECEDING_SUBJECT: &str = "\
(import [primitives [str-len str-concat Pure]])
(defn f [n]
  (let [s (str-concat \"h\" \"e\")
        s (str-concat s \"llo\")]
    (str-len s)))
(defn main [] (Pure (f 1)))
";

// SUBJECT's CONTROL, one identifier apart (the first binder `s` → `t`).
const HEAP_READ_PRECEDING_CONTROL: &str = "\
(import [primitives [str-len str-concat Pure]])
(defn f [n]
  (let [t (str-concat \"h\" \"e\")
        s (str-concat t \"llo\")]
    (str-len s)))
(defn main [] (Pure (f 1)))
";

// The CONTROL's own twin, one identifier from it (`t` → `u`) and likewise
// rebinding nothing. Paired against the control it gives the instrument's zero
// polarity on this program shape.
const HEAP_READ_PRECEDING_CONTROL_TWIN: &str = "\
(import [primitives [str-len str-concat Pure]])
(defn f [n]
  (let [u (str-concat \"h\" \"e\")
        s (str-concat u \"llo\")]
    (str-len s)))
(defn main [] (Pure (f 1)))
";

// SUBJECT, second shape: the rebinding's initializer reads NOTHING, so the
// displaced value is plainly dead at the second binding rather than consumed by
// it. Measured separately from the shape above so a repair cannot close one
// while leaving the other.
const HEAP_FRESH_REBIND_SUBJECT: &str = "\
(import [primitives [str-len str-concat Pure]])
(defn f [n]
  (let [s (str-concat \"he\" \"llo\")
        s (str-concat \"wor\" \"ld!\")]
    (str-len s)))
(defn main [] (Pure (f 1)))
";

const HEAP_FRESH_REBIND_CONTROL: &str = "\
(import [primitives [str-len str-concat Pure]])
(defn f [n]
  (let [t (str-concat \"he\" \"llo\")
        s (str-concat \"wor\" \"ld!\")]
    (str-len s)))
(defn main [] (Pure (f 1)))
";

// Face 2 — the SILENT face. Nothing aborts, the result is right, no diagnostic
// is printed; only the allocator accounting sees it, which is why this cell is
// the instrument for the face. Measured at authoring, before the repair, and
// deterministic over three repeats:
//
//   read-preceding  subject `allocs=6 deallocs=5`  control `allocs=6 deallocs=6`
//   fresh-rebinding subject `allocs=7 deallocs=6`  control `allocs=7 deallocs=7`
//
// ⇒ MARGINAL residual +1 on each pair, then. It was unchanged under
// `CRANELISP_NO_OWNERSHIP=1` (so the defect was not in the ownership elision)
// and present under `--link` as well as `--run`: one leaked object per call, so
// the same rebinding inside a loop or a recursive function leaked without
// bound. The assertion is the same either side of the repair — residual 0.
//
// Both pairs are measured in ONE cell and BOTH residuals are reported, so
// neither shape can be masked by the other's failure — they are the same
// structural probe over two initializer shapes, which is one condition
// (`.agents/skills/test/SKILL.md` §Work item 7).
// spec: spec/04-expressions.md §4.3 — heap values bound by `let` that are not
// captured by a closure or returned from the body become eligible for
// deallocation; a displaced binding is unreachable from the moment its name is
// rebound (spec/12-runtime.md §12.3.1).
// defect: class=binder-name-underkey locus=crates/cranelisp-backend/src/compiler/control_flow/let_if.rs::compile_let_sequential — a second binding of the same name overwrote the flat name-keyed `variables`/`variable_types` entry and pushed the name onto the scope frame a second time, so the displaced binder's value was no longer nameable by the frame-cleanup release set and its drop glue was never called; sibling of the `fn_compiler.rs::pop_scope` faces in tests/shadowed_param_reach_stale_rc_dec.rs on the same name-keyed axis, reached with NO nesting found=S121 owner=/dev fixed=S121
#[test]
fn displaced_same_form_binding_heap_value_is_not_leaked() {
    let cases = [
        (
            "the rebinding's initializer reads the displaced binding",
            HEAP_READ_PRECEDING_CONTROL,
            HEAP_READ_PRECEDING_SUBJECT,
            5,
        ),
        (
            "the rebinding's initializer is independent of the displaced binding",
            HEAP_FRESH_REBIND_CONTROL,
            HEAP_FRESH_REBIND_SUBJECT,
            6,
        ),
    ];

    let mut failures = String::new();
    for (label, control, subject, expected_exit) in cases {
        let measured = MarginalPair::new(label, Child::new(control), Child::new(subject)).measure();

        assert_eq!(
            measured.subject().exit_code(),
            Some(expected_exit),
            "{label}: the subject MUST still answer {expected_exit} — this cell \
             is about the value it leaves behind, not about its result.\n{}",
            measured.report()
        );
        if measured.residual() != 0 {
            failures.push_str(&format!("\n=== {label} ===\n{}", measured.report()));
        }
    }

    assert!(
        failures.is_empty(),
        "rebinding a name inside one `let` binding vector leaked the displaced \
         binding's heap value. The displaced value is unreachable from the \
         moment the name is rebound, so its release is owed no later than the \
         `let`'s exit (spec/04-expressions.md §4.3, spec/12-runtime.md \
         §12.3.1). Each pair differs in ONE identifier, so the difference is in \
         codegen and not in the program.{failures}"
    );
}

// Face 2 CONTROL (GREEN) — the instrument's zero polarity on this exact program
// shape. Two children that BOTH use a distinct first binder (`t` and `u`), so
// neither rebinds anything: a rename by itself must move no counter. Without
// this cell the subject's +1 could be read as the marginal reacting to renaming
// rather than to rebinding.
// spec: spec/12-runtime.md §12.3.1 — renaming a local binder that displaces
// nothing changes no value's reachability, and so must change no allocation
// accounting.
#[test]
fn rename_only_pair_measures_zero_marginal_control() {
    let measured = MarginalPair::new(
        "two distinct first-binder names (`t` against `u`), neither rebinding",
        Child::new(HEAP_READ_PRECEDING_CONTROL),
        Child::new(HEAP_READ_PRECEDING_CONTROL_TWIN),
    )
    .measure();

    assert_eq!(
        measured.subject().exit_code(),
        Some(5),
        "the control twin MUST answer 5.\n{}",
        measured.report()
    );
    measured.assert_balanced(
        "two programs that differ only in a binder name, NEITHER of them \
         rebinding, measured a non-zero marginal — the instrument is reacting \
         to the rename itself, which would invalidate the subject cell above.",
    );
}

// ===========================================================================
// Face 3 — tail transfer must move only the latest same-name binder.
//
// A bare `x` tail argument is a move into the next iteration's parameter.
// The first `x` in the subject is already displaced, so it is not that move and
// must be released before the jump.  The control changes only that discarded
// binder's name (`x` to `y`); both programs return the carried String's length.
// The fixed one-step countdown reaches the tail-jump cleanup without relying
// on an infinite illustrative loop.
// ===========================================================================

const TAIL_TRANSFER_SAME_NAME_SUBJECT: &str = "\
(import [primitives [eq-i64 str-concat str-len sub-i64 Pure]])
(defn go [n x]
  (if (eq-i64 n 0)
      (str-len x)
      (let [x (str-concat \"discard\" \"ed\")
            x (str-concat \"carry\" \"ing\")]
        (go (sub-i64 n 1) x))))
(defn main [] (Pure (go 1 (str-concat \"in\" \"put\"))))
";

const TAIL_TRANSFER_RENAME_CONTROL: &str = "\
(import [primitives [eq-i64 str-concat str-len sub-i64 Pure]])
(defn go [n x]
  (if (eq-i64 n 0)
      (str-len x)
      (let [y (str-concat \"discard\" \"ed\")
            x (str-concat \"carry\" \"ing\")]
        (go (sub-i64 n 1) x))))
(defn main [] (Pure (go 1 (str-concat \"in\" \"put\"))))
";

// spec: spec/04-expressions.md §4.3 — the later `x` binding shadows the
// earlier one within the same binding vector; spec/12-runtime.md §12.3.1 — the
// displaced heap value becomes unreachable and MUST be freed.
// defect: class=binder-name-underkey locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::flush_let_scopes_before_tail_jump found=S121 owner=/dev fixed=S121
#[test]
fn tail_transfer_releases_the_displaced_same_name_binder_run_and_link() {
    let mut failures = String::new();
    for (mode, control, subject) in [
        (
            "--run",
            Child::new(TAIL_TRANSFER_RENAME_CONTROL),
            Child::new(TAIL_TRANSFER_SAME_NAME_SUBJECT),
        ),
        (
            "--link",
            Child::new(TAIL_TRANSFER_RENAME_CONTROL).link_then_run(),
            Child::new(TAIL_TRANSFER_SAME_NAME_SUBJECT).link_then_run(),
        ),
    ] {
        let measured = MarginalPair::new(
            "the discarded first tail-frame binder is renamed, not transferred",
            control,
            subject,
        )
        .measure();

        if measured.control().exit_code() != Some(8) || measured.subject().exit_code() != Some(8) {
            failures.push_str(&format!(
                "\n=== {mode}: terminating-value witness ===\n{}\n\
                 control stdout:\n{}\ncontrol stderr:\n{}\n\
                 subject stdout:\n{}\nsubject stderr:\n{}",
                measured.report(),
                measured.control().stdout,
                measured.control().stderr,
                measured.subject().stdout,
                measured.subject().stderr,
            ));
        }
        if measured.residual() != 0 {
            failures.push_str(&format!(
                "\n=== {mode}: marginal ownership witness ===\n{}",
                measured.report(),
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "a tail self-call moved only its latest same-name binder, but the \
         name-keyed transfer skip also retained the displaced first binder. \
         The control differs in one identifier, so a non-zero marginal is the \
         tail-frame cleanup defect rather than the terminating program or its \
         common parameter replacement.{failures}"
    );
}

// ===========================================================================
// Face 2, TYPE-CHANGING axis (`qa` allocation T2, 2026-09-08).
//
// Every Face-2 cell above rebinds String→String, so the axis where the two
// binders carry DIFFERENT types is uncovered. This is that cell: `s` is bound
// to a String and rebound — by an initializer that READS it — to an Int.
//
// PRE-REPAIR MEASUREMENT (2026-09-08, binary sha256 a913bc3a…, the same build
// every cell above was measured on): subject `allocs=4 deallocs=4`, control
// `allocs=4 deallocs=4` ⇒ marginal residual **0**, and both answer 2. This cell
// is GREEN before the S121 backend repair as well as after it; it is a
// REGRESSION GUARD on an axis the repair touches, not a defect repro, and it
// carries no `defect:` line.
//
// Why a GREEN here is not vacuous — the instrument was armed both ways on this
// exact program family and harness before the repair: it reported +1 on the
// pre-repair String→String shapes
// (`displaced_same_form_binding_heap_value_is_not_leaked`) and 0 on a pair that
// renames without rebinding (`rename_only_pair_measures_zero_marginal_control`).
// The zero polarity is still measured every run by that rename control.
//
// What this cell may NOT be read as saying. A non-zero residual here would
// establish only that the type-changing rebinding leaks; it would NOT
// discriminate a distinct mechanism from the frame-cleanup loss the cells above
// pinned, because that loss was present on this shape family too. Attribution
// is `qa`'s and needs a control that separates the two, which a marginal on
// this subject cannot supply.
// ===========================================================================

// SUBJECT — `s` is String, then rebound to the Int its own initializer derives
// from the displaced String (§4.3 sequential visibility, `x1 == x2`).
const HEAP_TYPE_CHANGING_SUBJECT: &str = "\
(import [primitives [str-len str-concat Pure]])
(defn f [n]
  (let [s (str-concat \"h\" \"e\")
        s (str-len s)]
    s))
(defn main [] (Pure (f 1)))
";

// CONTROL, one identifier apart (first binder `s` → `t`): the same two types in
// the same order, binding nothing twice.
const HEAP_TYPE_CHANGING_CONTROL: &str = "\
(import [primitives [str-len str-concat Pure]])
(defn f [n]
  (let [t (str-concat \"h\" \"e\")
        s (str-len t)]
    s))
(defn main [] (Pure (f 1)))
";

// The value assertion is the second half of this cell and is not redundant with
// the marginal: it is what would catch the rebinding's initializer resolving
// the displaced name at the WRONG type (reading the String binder's storage as
// the Int the rebinding declares), which need not move the allocator counters
// at all.
// spec: spec/04-expressions.md §4.3 — the second initializer is evaluated in the
// environment extended by the preceding binding, so `(str-len s)` reads the
// String `s` and the `let` answers 2; the displaced String is unreachable from
// that moment and its release is owed no later than the `let`'s exit
// (spec/12-runtime.md §12.3.1).
#[test]
fn type_changing_same_form_rebinding_answers_correctly_and_leaks_nothing() {
    let measured = MarginalPair::new(
        "the rebinding changes the name's type (String → Int) and reads the \
         displaced binding",
        Child::new(HEAP_TYPE_CHANGING_CONTROL),
        Child::new(HEAP_TYPE_CHANGING_SUBJECT),
    )
    .measure();

    assert_eq!(
        measured.subject().exit_code(),
        Some(2),
        "`(let [s (str-concat \"h\" \"e\") s (str-len s)] s)` MUST answer 2: the \
         rebinding's initializer reads the PRECEDING `s`, which is the String \
         \"he\" (spec/04-expressions.md §4.3).\n{}",
        measured.report()
    );
    assert_eq!(
        measured.control().exit_code(),
        Some(2),
        "the rename control MUST answer 2 as well — the pair differs in one \
         identifier only.\n{}",
        measured.report()
    );
    measured.assert_balanced(
        "a `let` binder rebound at a DIFFERENT type left the displaced String \
         unreleased. The displaced value is unreachable from the moment the \
         name is rebound, so its release is owed no later than the `let`'s exit \
         (spec/04-expressions.md §4.3, spec/12-runtime.md §12.3.1). The pair \
         differs in ONE identifier, so the difference is in codegen and not in \
         the program.",
    );
}
