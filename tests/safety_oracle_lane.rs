// safety_oracle_lane.rs — the memory-safety differential-oracle lane (MS-P2/P4/P5,
// tests/plan/s113-test-plan.md §2; user-approved W5 depth, W0 gate CONFIRMED
// memory-safety as the top correctness risk).
//
// The lane drives memory-safety probes through the `assert_safety_matrix`
// combinator (MS-P1, `helpers/e2e.rs`) — modes × ownership-toggle {on, off} ×
// {behavioral equivalence, RC balance, RC_DEC_CHECK zero, `--link` face}. The
// conservative all-Owned lowering (`CRANELISP_NO_OWNERSHIP=1`) is the reference
// semantics; an ownership-elision defect diverges the ON path from it.
//
// ACCEPTANCE (strategy §1.3 / plan §2 MS-P2):
//   - the 0641 B-1 program goes RED under the lane on day one (the elision frees a
//     returned alias — ON diverges from the conservative fallback / --link aborts);
//   - a clean program and a §3.7-cured COW program stay GREEN (the lane does not
//     false-positive);
//   - lane wall ≤ 60s.
//
// The drop-glue collision family (0633, MS-P4) is ORDER-keyed, NOT toggle-
// dependent, so the differential combinator is the wrong instrument for it — that
// cell is hand-authored on the ABSOLUTE corruption face (no SIGABRT / no
// RC_DEC_CHECK abort / REPL≡run) below.
//
// Stdlib-free: `primitives` only (root CLAUDE.md §Design Principles). RC-reading
// runs are per-subprocess, safe under nextest process isolation.
//
// SCOPE NOTE (W1): MS-P1/P2/P4/P5 land here. MS-P3 (mechanical retro-wrap of the
// ~10 existing ownership/RC repro files through the combinator) is the follow-on
// (may ride or follow MS-P1); MS-P6 (diagnostic-mode self-tests) rides the W5
// build change-sets per the depth ruling. Neither is W1 authoring.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{assert_safety_matrix, Cranelisp, PreludeVariant, SafetyMatrix};

// MS-P2 ACCEPTANCE (RED day one) — 0641 B-1. `(defn f [v] (vec-get [v] 0))`
// returns its own param `v` via a fresh-container projection; the ownership walk
// publishes a false `result=Fresh`, the return protect is elided, and the alias
// is freed before the caller reads it. `(vec-get (f [1 2 3]) 1)` MUST yield 2
// (`main` returns `(Pure 2)` → exit 2). Under ownership ON the elision corrupts
// (the `--link` binary deterministically aborts, 6/6; the differential diverges);
// toggle-off is clean. The lane catches it → RED, flips when 0641's false-`Fresh`
// class closes by mechanism (§3 frame, W5).
// spec: spec/12-runtime.md §12.1 — a param returned via a fresh-container
// projection MUST remain live for the caller.
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/transfer.rs::VecLit-element-store-ProjectionOf-composition found=S111 owner=/dev
#[test]
fn safety_lane_b1_false_fresh_returned_alias_differential_red() {
    SafetyMatrix::new(
        "(defn f [v] (vec-get [v] 0))\n\
         (defn main [] (Pure (vec-get (f [1 2 3]) 1)))\n",
    )
    .prelude(PreludeVariant::PrimitivesOnly)
    .expect_exit(2)
    .without_rc_balance() // the corrupting path aborts; the differential + link faces are the RED
    .assert();
}

// MS-P2 GREEN acceptance — a trivially clean vec read. `[10 20 30]` element 1 = 20.
// No aliasing subtlety: ON≡OFF, RC balanced, `--link` clean, no dec-check abort.
// Proves the lane does NOT false-positive.
// spec: spec/12-runtime.md §12.1 — vec construction + indexed read is memory-safe.
#[test]
fn safety_lane_clean_vec_read_green() {
    assert_safety_matrix(
        "(defn main [] (Pure (vec-get [10 20 30] 1)))\n",
        PreludeVariant::PrimitivesOnly,
        20,
    );
}

// The COW-set→project program: `(vec-set v 0 9)` returns a COW copy; reading
// element 0 = 9. Under `--run` the answer is correct (9); the `--link` binary
// DETERMINISTICALLY ABORTS ("corrupted double-linked list"). The §3.7 `MayAliasOf`
// COW-truth work (S111) did NOT cover this direct COW-set→project shape.
const COW_SET_READ_PROG: &str = "(defn f [v] (vec-get (vec-set v 0 9) 0))\n\
     (defn main [] (Pure (f [1 2 3])))\n";

// MS-P7 pin (R-2 re-shape) — the SPEC-CORRECT CONTRACT, RED under ALL mode configs.
// `(vec-get (vec-set v 0 9) 0)` MUST return the set value 9, abort-free, in EVERY
// mode. This asserts the contract directly (NOT the differential detection shape),
// so its color tracks the DEFECT's existence, never lane-config/detection quality
// (R-2: a pin whose color depends on lane config cannot serve as the flip trigger).
// The `--link` abort is config-independent → RED under all combinations until the
// W5 0641/§3 increment (typecheck rule-table + backend vec-set-result consume fix)
// lands, verified under the lane.
// spec: spec/12-runtime.md §12.1 — a COW `vec-set` result read by the caller returns
// the set value and is memory-safe in all modes.
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership (COW-set→project result, --link mode-divergent double-free; §3.7 MayAliasOf gap; 0641-adjacent) found=S113 owner=/dev
#[test]
fn safety_lane_cow_set_read_returns_set_value_abort_free_red() {
    // --run: returns the set value 9.
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(COW_SET_READ_PROG)
        .output()
        .assert_exit(9);
    // --link: MUST also return 9 (today it aborts — the config-independent RED).
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(COW_SET_READ_PROG)
        .output()
        .assert_exit(9);
    // REPL: MUST evaluate to 9.
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(defn f [v] (vec-get (vec-set v 0 9) 0))\n(f [1 2 3])\n")
        .output()
        .assert_stdout_contains(":primitives/Int 9");
}

// MS-P6 self-test (R-2) — the safety LANE's DETECTION CAPABILITY, kept SEPARATE
// from the pin above (detection quality is separately valuable but must not be the
// pin's color). Running the corrupting program through the differential-oracle
// matrix MUST flag the planted-class fault (the matrix panics on the `--link`
// divergence). GREEN: the lane sees the fault. (The panic hook is silenced around
// the expected panic so the detection is not mistaken for a test failure.)
// spec: spec/12-runtime.md §12.1 — the safety lane detects a COW-UAF planted fault.
#[test]
fn safety_lane_detects_cow_set_read_corruption_capability_green() {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let detected = std::panic::catch_unwind(|| {
        SafetyMatrix::new(COW_SET_READ_PROG)
            .prelude(PreludeVariant::PrimitivesOnly)
            .expect_exit(9)
            .without_rc_balance()
            .assert();
    })
    .is_err();
    std::panic::set_hook(prev);
    assert!(
        detected,
        "the safety-matrix lane MUST DETECT the COW-set-read corruption — running \
         the corrupting program through the matrix must flag it (panic); it did not"
    );
}

// MS-P4 — 0633 module-axis drop-glue collision, RE-AUTHORED on the CORRUPTION
// face. Two ADTs with the SAME bare type name `Thing` from two different modules,
// different field layouts (String = heap; Int = non-heap). `FQTypeName`
// distinguishes them everywhere upstream; only the glue-naming fn drops the module
// qualifier, so `runtime/drop_glue_Thing` collides in the importing module's batch
// — first-build-wins serves ONE glue for both instantiations. The existing leak
// cell (`adt_drop_glue_underkey.rs::adt_vec_drop_glue_module_axis_leak_r2`) pins
// the LEAK face; this cell adds the CORRUPTION face the leak cell lacks: the
// `--link` binary must not SIGABRT, `CRANELISP_RC_DEC_CHECK` must not trip an
// underflow abort (a DEC on a non-heap Int-as-pointer slot), and the REPL must
// agree with `--run` (the S111 reachability record's REPL-vs-`--run` divergence
// face: per-turn Jit batches vs whole-module ObjectModule). Correct answer: two
// vec-lens of 1 → exit 2. RED until the 0633 re-key (W5 R4 census).
// spec: spec/12-runtime.md §12.3.1 — heap value freed when no longer reachable;
// drop glue must not DEC a non-heap slot.
// defect: class=drop-glue-underkey locus=crates/cranelisp-backend/src/compiler/{resolution.rs::adt_drop_glue_name,vec_codegen.rs::build_elem_dec_fn} found=S111 owner=/dev
#[test]
fn safety_lane_module_axis_same_name_adt_corruption_face() {
    let ma = "(deftype Thing (MkA [:String s]))\n";
    let mb = "(deftype Thing (MkB [:Int n]))\n";
    let main = "(import [primitives [Pure]])\n\
         (import [ma [MkA]])\n\
         (import [mb [MkB]])\n\
         (defn main []\n\
           (let [va [(MkA \"hi\")]\n\
                 vb [(MkB 7)]]\n\
             (Pure (add-i64 (vec-len va) (vec-len vb)))))\n";

    // --run: correct value, no abort.
    let run = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("ma.cl", ma)
        .file("mb.cl", mb)
        .file("main.cl", main)
        .run("main.cl")
        .output();
    assert_eq!(
        run.status.code(),
        Some(2),
        "[--run] two same-bare-name `Thing` ADTs must produce exit 2 (vec-len 1 + \
         1); got {:?}:\n{}{}",
        run.status.code(),
        run.stdout,
        run.stderr
    );

    // --link corruption face: the linked binary must run cleanly, never SIGABRT on
    // a mis-slotted DEC.
    let link = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("ma.cl", ma)
        .file("mb.cl", mb)
        .file("main.cl", main)
        .link_then_run("main.cl")
        .output();
    assert_eq!(
        link.status.code(),
        Some(2),
        "[--link] the bare-name-keyed drop-glue collision must NOT corrupt the heap \
         (SIGABRT / DEC-on-wrong-slot); linked binary MUST exit 2; got {:?}:\n{}{}",
        link.status.code(),
        link.stdout,
        link.stderr
    );

    // RC_DEC_CHECK corruption face: a DEC of the non-heap Int slot (served the
    // String-field glue) trips the underflow check — the run must stay exit 2.
    let dc = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .env("CRANELISP_RC_DEC_CHECK", "1")
        .file("ma.cl", ma)
        .file("mb.cl", mb)
        .file("main.cl", main)
        .run("main.cl")
        .output();
    assert_eq!(
        dc.status.code(),
        Some(2),
        "[RC_DEC_CHECK] the collision must not trip an RC-underflow abort (a DEC on \
         a non-heap Int slot); got {:?}:\n{}{}",
        dc.status.code(),
        dc.stdout,
        dc.stderr
    );

    // REPL-vs-run divergence face (per-turn Jit batch vs whole-module ObjectModule).
    let repl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("ma.cl", ma)
        .file("mb.cl", mb)
        .stdin(
            "(import [ma [MkA]])\n\
             (import [mb [MkB]])\n\
             (add-i64 (vec-len [(MkA \"hi\")]) (vec-len [(MkB 7)]))\n",
        )
        .output();
    let rc = format!("{}{}", repl.stdout, repl.stderr);
    assert!(
        rc.contains(":primitives/Int 2"),
        "[repl] the REPL must agree with `--run` (exit 2 ⇒ `:primitives/Int 2`); \
         a REPL-vs-run divergence is the S111 reachability-record collision-scope \
         face; got:\n{rc}"
    );
}
