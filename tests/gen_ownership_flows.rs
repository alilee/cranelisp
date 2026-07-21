// gen_ownership_flows.rs — the GENERATIVE ownership/RC flow harness, v1
// (`tests/plan/memory-safety-coverage.md` §2 "Generative / property harness";
// matrix item O4, S115 W7).
//
// WHY GENERATION. Every leak this project shipped in S115 was found by hand-
// measuring `allocs == deallocs` on a shape someone thought to write (FIXME 0749,
// 0753, 0760 — all three say so in their own bodies). Hand enumeration shares the
// implementer's mental model, so it is blind to exactly the axes that model
// missed. This file does not enumerate shapes; it enumerates a PRODUCT
//
//     {owning type, incl. nesting depth} x {position} x {ownership toggle}
//                                        x {iteration count}
//
// and asserts the same four faults over every cell. A shape nobody thought of is
// a cell in the product, not a gap.
//
// WHAT IT ASSERTS (per cell, per toggle):
//   1. VALUE      — the program's answer is the expected one.
//   2. DIVERGENCE — ownership-ON and the conservative all-Owned oracle
//                   (`CRANELISP_NO_OWNERSHIP=1`) agree (the differential face).
//   3. BALANCE    — `allocs == deallocs` EXACTLY, in BOTH polarities. Not a
//                   residue allowance and not a differential: FIXME 0761 showed
//                   the standing differential RC face is structurally blind to a
//                   leak both lowerings share (four such leaks shipped under it in
//                   one wave), and W3c/W5a showed a `residue <= 8` pin cannot see
//                   a constant residue of 1. OVER-RELEASE (deallocs > allocs) is
//                   asserted as its own fault: no residue allowance in any
//                   direction ever catches that polarity.
//   4. SCALING    — the imbalance does not GROW with iteration count. Every cell
//                   runs its flow once AND `ITERS` times through a TCO repeater;
//                   a per-iteration leak is reported with its rate, separately
//                   from a constant one.
//
// CAPABILITY FENCES (METHOD §2.2 — "an instrument is unverified until it is
// proven to detect"; `memory-safety-coverage.md` §4.1). The four `_capability_`
// tests at the bottom plant SYNTHETIC faults — never a live defect, per the
// §4.1 prong-2 amendment (twice now a fence planted on a live defect inverted to
// RED when someone else fixed it). Each fence takes a REAL measurement of a real
// clean program (so the fence also proves the stderr parse -> verdict wiring),
// perturbs it arithmetically, and asserts `verdict` names the right fault class.
//
// COST. 45 cells x 4 `--run` subprocesses = 180 runs, ~1.5s wall, split across
// five nextest test fns (one per owning type) so they parallelize. Stdlib-free
// (`PrimitivesOnly`); every subprocess gets its own tmpdir and its own env, so the
// lane is safe under nextest process isolation.
//
// v1 SCOPE — what is DELIBERATELY NOT GENERATED YET (a modest product that runs
// green and proves its own detection beats a large one that is unproven):
//   - the `--link` and REPL faces. v1 is `--run` x toggle only. The two `--link`
//     abort families this project has (0706/0772) are shape-specific and already
//     pinned cell-by-cell in `safety_oracle_lane.rs`, which owns the four-face
//     combinator; adding a link run per cell here would ~triple the wall for a
//     face that is covered. v2: run the product through `assert_safety_matrix`
//     behind `CRANELISP_SAFETY_FULL=1`.
//   - depth-2 COMPOSITION of positions (`returned ∘ captured`, `curried ∘
//     loop-carried`, …). v1 is depth-1: one position per cell. The strategy's
//     §2.2 target is depth-2; the product is written as two independent
//     enumerations precisely so composing them is a loop, not a rewrite.
//   - `vec-set`/`vec-push` COW operators as flow steps (the `MayAliasOf` family),
//     match/projection steps, spark & macro-expansion flows (strategy §2.2 "v2").
//   - the program-RESULT-heap face — see `single_program` below (FIXME 0745).
//
// spec: spec/12-runtime.md §12.3.1 — Requirements (a heap value MUST be freed when
// it is no longer reachable, and MUST NOT be freed while it is).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// ===========================================================================
// The generation space
// ===========================================================================

/// One owning type: what the flow threads, and how a cell reads an `Int` out of
/// it. `nesting` is the heap-object depth (1 = a leaf heap object, 3 = a Vec of
/// ADTs each owning a String) — the axis FIXME 0760's `MAX_DROP_GLUE_DEPTH`
/// cliff lives on.
struct OwningType {
    name: &'static str,
    /// Extra top-level definitions the type needs (ADT decl + its reader).
    defs: &'static str,
    /// The written type, for the parameter annotations that make every generated
    /// program well-typed BY CONSTRUCTION (annotations ASSERT — a generated
    /// program must never depend on inference finding a type nobody wrote).
    ty: &'static str,
    /// An expression constructing a fresh value of the type.
    mk: &'static str,
    /// A monomorphic `(Fn [ty] Int)` reader applied to the value.
    read: &'static str,
    /// What `read` returns for `mk`.
    expect: i32,
    nesting: u8,
}

const ADT_DEFS: &str = "(deftype Bx (MkBx [:String s]))\n\
     (defn bxlen [:Bx b] (match b [(MkBx s) (str-len s)]))\n";

fn owning_types() -> Vec<OwningType> {
    vec![
        OwningType {
            name: "str",
            defs: "",
            ty: "String",
            mk: "\"abc\"",
            read: "str-len",
            expect: 3,
            nesting: 1,
        },
        OwningType {
            name: "vec_of_scalars",
            defs: "",
            ty: "(Vec Int)",
            mk: "[1 2 3]",
            read: "vec-len",
            expect: 3,
            nesting: 1,
        },
        OwningType {
            name: "vec_of_heap",
            defs: "",
            ty: "(Vec String)",
            mk: "[\"a\" \"b\" \"c\"]",
            read: "vec-len",
            expect: 3,
            nesting: 2,
        },
        OwningType {
            name: "adt_with_heap_field",
            defs: ADT_DEFS,
            ty: "Bx",
            mk: "(MkBx \"abcd\")",
            read: "bxlen",
            expect: 4,
            nesting: 2,
        },
        OwningType {
            name: "vec_of_adt_with_heap_field",
            defs: ADT_DEFS,
            ty: "(Vec Bx)",
            mk: "[(MkBx \"a\") (MkBx \"b\")]",
            read: "vec-len",
            expect: 2,
            nesting: 3,
        },
    ]
}

/// One position: WHERE the owned value sits relative to the frame that made it.
/// Every position emits a nullary `cell` returning the read `Int`, so the
/// repeater below is position-agnostic.
struct Position {
    name: &'static str,
    emit: fn(&OwningType) -> String,
}

fn positions() -> Vec<Position> {
    vec![
        Position {
            name: "applied_in_place",
            emit: |t| format!("(defn cell [] ({} {}))\n", t.read, t.mk),
        },
        Position {
            name: "let_bound",
            emit: |t| format!("(defn cell [] (let [v {}] ({} v)))\n", t.mk, t.read),
        },
        Position {
            name: "borrowed_argument",
            emit: |t| {
                format!(
                    "(defn ba [:{} x] ({} x))\n(defn cell [] (ba {}))\n",
                    t.ty, t.read, t.mk
                )
            },
        },
        Position {
            name: "returned",
            emit: |t| {
                format!(
                    "(defn mkv [] {})\n(defn cell [] ({} (mkv)))\n",
                    t.mk, t.read
                )
            },
        },
        Position {
            name: "returned_through_1_let",
            emit: |t| {
                format!(
                    "(defn mkv [] (let [v {}] v))\n(defn cell [] ({} (mkv)))\n",
                    t.mk, t.read
                )
            },
        },
        Position {
            name: "returned_through_2_lets",
            emit: |t| {
                format!(
                    "(defn mkv [] (let [v {}] (let [w v] w)))\n(defn cell [] ({} (mkv)))\n",
                    t.mk, t.read
                )
            },
        },
        Position {
            name: "curried_partial_application",
            emit: |t| {
                format!(
                    "(defn cur [:{} x :Int y] (add-i64 ({} x) y))\n\
                     (defn cell [] (let [h (cur {})] (h 0)))\n",
                    t.ty, t.read, t.mk
                )
            },
        },
        Position {
            name: "captured_in_escaping_closure",
            emit: |t| {
                format!(
                    "(defn mkc [] (let [v {}] (fn [] ({} v))))\n\
                     (defn cell [] (let [h (mkc)] (h)))\n",
                    t.mk, t.read
                )
            },
        },
        Position {
            name: "loop_carried",
            emit: |t| {
                format!(
                    "(defn go [:Int n :{} x] (if (le-i64 n 0) ({} x) (go (sub-i64 n 1) x)))\n\
                     (defn cell [] (go 3 {}))\n",
                    t.ty, t.read, t.mk
                )
            },
        },
    ]
}

/// How many times the scaled variant runs the flow. Any per-iteration leak is
/// multiplied by this, so a rate of 1 is unmissable in the reported numbers.
const ITERS: i64 = 25;

/// `main` ALWAYS returns `(Pure <Int>)`.
///
/// PRE-REGISTERED EXCLUSION (dispatch caveat (a); FIXME 0745, carried to S116):
/// the program-RESULT-heap face — `main` returning an `IO` whose payload is a
/// heap value — leaks by construction today, because nobody releases the program
/// result value in any mode. It is pinned by
/// `adt_drop_glue_underkey::entry_main_ioresult_heap_payload_toggle_off_leak_r2`
/// and owned by `/design`(int) + an `/arch` mechanism ruling. Generating it here
/// would make every cell of this harness's first run read as noise for a defect
/// that already has a pin, an owner and a trigger. The exclusion is STRUCTURAL —
/// there is no `Pure <heap>` template in the generator — not a suppressed
/// assertion. When 0745 lands, `main`-returns-heap becomes a third variant here.
fn single_program(t: &OwningType, p: &Position) -> String {
    format!("{}{}(defn main [] (Pure (cell)))\n", t.defs, (p.emit)(t))
}

fn scaled_program(t: &OwningType, p: &Position) -> String {
    format!(
        "{}{}(defn rep [:Int n :Int acc] (if (le-i64 n 0) acc (rep (sub-i64 n 1) (cell))))\n\
         (defn main [] (Pure (rep {} 0)))\n",
        t.defs,
        (p.emit)(t),
        ITERS
    )
}

// ===========================================================================
// Measurement
// ===========================================================================

/// One subprocess run's observable facts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Measure {
    exit: Option<i32>,
    /// `None` when the run emitted no `[RC_STATS]` line at all — an unmeasured
    /// run, which is a FAULT, never a silent pass (the failure mode where an
    /// instrument reads nothing and reports green).
    rc: Option<(i64, i64)>,
}

impl Measure {
    fn imbalance(&self) -> Option<i64> {
        self.rc.map(|(a, d)| a - d)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Toggle {
    OwnershipOn,
    OwnershipOff,
}

fn measure(program: &str, toggle: Toggle) -> Measure {
    let mut b = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(program)
        .env("CRANELISP_RC_STATS", "1");
    if toggle == Toggle::OwnershipOff {
        b = b.env("CRANELISP_NO_OWNERSHIP", "1");
    }
    let out = b.output();
    let rc = out
        .stderr
        .lines()
        .find(|l| l.contains("[RC_STATS]"))
        .and_then(|line| {
            let field = |k: &str| -> Option<i64> {
                line.split_whitespace()
                    .find_map(|tok| tok.strip_prefix(k).and_then(|v| v.parse().ok()))
            };
            Some((field("allocs=")?, field("deallocs=")?))
        });
    Measure {
        exit: out.status.code(),
        rc,
    }
}

// ===========================================================================
// The verdict — the harness's detection logic, isolated as a PURE function so
// the capability fences can plant synthetic faults straight into it.
// ===========================================================================

#[derive(Debug, PartialEq, Eq)]
enum Fault {
    /// The program did not produce the expected answer.
    Value,
    /// Ownership-ON disagreed with the conservative all-Owned oracle.
    Divergence,
    /// `allocs > deallocs` — something the program owned was never freed.
    Leak { count: i64 },
    /// `deallocs > allocs` — the opposite polarity. NO residue allowance in any
    /// direction can see this, which is why it is its own fault class.
    OverRelease { count: i64 },
    /// The imbalance grew with the iteration count: a per-iteration leak, not a
    /// one-off residue.
    Scaling { per_iteration: i64 },
    /// A run produced no `[RC_STATS]` line — unmeasured, never "clean".
    NoMeasurement,
}

/// Faces 1–4 over one cell's four measurements. `balance` selects whether the
/// RC faces (3 and 4) are asserted; see `balance_exclusion`.
fn verdict(
    expect: i32,
    single_on: Measure,
    single_off: Measure,
    scaled_on: Measure,
    scaled_off: Measure,
    balance: bool,
) -> Vec<Fault> {
    let mut faults = Vec::new();
    let all = [single_on, single_off, scaled_on, scaled_off];

    // Face 1 — value.
    if all.iter().any(|m| m.exit != Some(expect)) {
        faults.push(Fault::Value);
    }
    // Face 2 — differential (ON vs the conservative oracle).
    if single_on.exit != single_off.exit || scaled_on.exit != scaled_off.exit {
        faults.push(Fault::Divergence);
    }
    if !balance {
        return faults;
    }
    // Faces 3/4 need measurements to exist.
    if all.iter().any(|m| m.rc.is_none()) {
        faults.push(Fault::NoMeasurement);
        return faults;
    }
    // Face 3 — EXACT balance, both polarities, both toggles.
    for m in all {
        match m.imbalance().unwrap() {
            0 => {}
            n if n > 0 => faults.push(Fault::Leak { count: n }),
            n => faults.push(Fault::OverRelease { count: -n }),
        }
    }
    // Face 4 — scaling. Reported even when face 3 already fired: a constant
    // residue and a per-iteration leak are different defects with different
    // owners, and the rate names the flow that leaks.
    for (s, k) in [(single_on, scaled_on), (single_off, scaled_off)] {
        let growth = k.imbalance().unwrap() - s.imbalance().unwrap();
        if growth != 0 {
            faults.push(Fault::Scaling {
                per_iteration: growth / (ITERS - 1),
            });
        }
    }
    faults
}

/// The one place a `(type, position)` cell may opt out of the RC faces, with a
/// named open defect that already carries a pin, an owner and a CI trigger.
/// Adding a second RED for one unfixed defect buys nothing and costs a triage
/// cycle every certification run (FIXME 0745's own rider says so).
///
/// The value and differential faces still run on every excluded cell.
///
/// The exclusion is EXACTLY the measured fault set — verified by disabling it and
/// re-running the sweep (S115 W7, HEAD `99bd23a8`): the six excluded cells fail
/// and NOTHING else does. Per-iteration rates at that HEAD, identical under both
/// toggles (so the standing DIFFERENTIAL RC face passes all six — FIXME 0761):
///
///   vec_of_heap              x {curried, captured}  3/iteration
///   adt_with_heap_field      x {curried, captured}  1/iteration
///   vec_of_adt_with_heap_fld x {curried, captured}  4/iteration
///
/// `curried_partial_application` is a reaching context FIXME 0760 does not name —
/// its evidence and its repro file cover only explicit `fn` captures. Auto-curry's
/// implicit closure env strands identically, at the identical rate. Routed to
/// `/design`(backend) as FIXME 0796; it does not change the a-vs-b ruling, it
/// widens what option (b) has to collapse.
fn balance_exclusion(t: &OwningType, p: &Position) -> Option<&'static str> {
    let captured = matches!(
        p.name,
        "captured_in_escaping_closure" | "curried_partial_application"
    );
    if captured && t.nesting >= 2 {
        return Some(
            "FIXME 0760 — the capture drop glue releases a Vec-of-heap / \
             ADT-with-heap-field capture with a bare dec, stranding what the \
             capture owns (leak-only, toggle-independent, per-iteration). Pinned \
             failing-not-ignored by tests/capture_drop_glue_strands_nested_heap_0760.rs; \
             open on a /design(backend) a-vs-b ruling. Remove this exclusion when \
             those pins flip.",
        );
    }
    None
}

// ===========================================================================
// The sweep
// ===========================================================================

fn sweep(type_name: &str) {
    let types = owning_types();
    let t = types
        .iter()
        .find(|t| t.name == type_name)
        .expect("unknown owning type");
    let mut failures: Vec<String> = Vec::new();
    let mut run = 0usize;
    let mut excluded = 0usize;

    for p in positions() {
        let single = single_program(t, &p);
        let scaled = scaled_program(t, &p);
        let excl = balance_exclusion(t, &p);
        let m = (
            measure(&single, Toggle::OwnershipOn),
            measure(&single, Toggle::OwnershipOff),
            measure(&scaled, Toggle::OwnershipOn),
            measure(&scaled, Toggle::OwnershipOff),
        );
        let faults = verdict(t.expect, m.0, m.1, m.2, m.3, excl.is_none());
        if excl.is_some() {
            excluded += 1;
        }
        run += 1;
        if !faults.is_empty() {
            failures.push(format!(
                "cell {}/{} (nesting {}) — {:?}\n  expected exit {}\n  \
                 single ON  {:?}\n  single OFF {:?}\n  x{ITERS} ON  {:?}\n  x{ITERS} OFF {:?}\n\
                 --- program (single) ---\n{}",
                t.name, p.name, t.nesting, faults, t.expect, m.0, m.1, m.2, m.3, single
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "[gen-ownership-flows] {} of {run} cells FAILED for owning type `{}` \
         ({excluded} cell(s) opted out of the RC faces by named exclusion).\n\n{}",
        failures.len(),
        t.name,
        failures.join("\n\n")
    );
}

// spec: spec/12-runtime.md §12.3.1 — Requirements (heap values freed exactly once).
#[test]
fn gen_flows_str_exact_balance_and_differential() {
    sweep("str");
}

// spec: spec/12-runtime.md §12.3.1 — Requirements (heap values freed exactly once).
#[test]
fn gen_flows_vec_of_scalars_exact_balance_and_differential() {
    sweep("vec_of_scalars");
}

// spec: spec/12-runtime.md §12.3.1 — Requirements (heap values freed exactly once).
#[test]
fn gen_flows_vec_of_heap_exact_balance_and_differential() {
    sweep("vec_of_heap");
}

// spec: spec/12-runtime.md §12.3.1 — Requirements (heap values freed exactly once).
#[test]
fn gen_flows_adt_with_heap_field_exact_balance_and_differential() {
    sweep("adt_with_heap_field");
}

// spec: spec/12-runtime.md §12.3.1 — Requirements (heap values freed exactly once).
#[test]
fn gen_flows_vec_of_adt_with_heap_field_exact_balance_and_differential() {
    sweep("vec_of_adt_with_heap_field");
}

// ===========================================================================
// Capability fences — the harness proving it detects each class it claims.
//
// All four plants are SYNTHETIC (§4.1 prong-2 amendment): each starts from a
// REAL measurement of a real, currently-clean program — so the fence also proves
// the `[RC_STATS]` parse and the measure -> verdict wiring are live — and then
// perturbs the numbers arithmetically. No fence depends on a live compiler
// defect, so none of them can expire when someone else's fix lands.
// ===========================================================================

/// A real, currently-balanced cell: `str` x `let_bound`. Measured, not asserted
/// clean by construction — if this ever stops balancing, the sweep above says so
/// first, and these fences say why their baseline moved.
fn fence_baseline() -> (Measure, Measure) {
    let types = owning_types();
    let t = types.iter().find(|t| t.name == "str").unwrap();
    let ps = positions();
    let p = ps.iter().find(|p| p.name == "let_bound").unwrap();
    (
        measure(&single_program(t, p), Toggle::OwnershipOn),
        measure(&scaled_program(t, p), Toggle::OwnershipOn),
    )
}

// The instrument reads real numbers, and reads them as CLEAN when they are clean.
// Without this, the three fault fences below could all pass against an instrument
// that reports a fault unconditionally.
// spec: spec/12-runtime.md §12.3.1 — Requirements.
#[test]
fn gen_flows_capability_measures_a_real_clean_cell_as_clean() {
    let (single, scaled) = fence_baseline();
    assert!(
        single.rc.is_some() && scaled.rc.is_some(),
        "the harness MUST parse an [RC_STATS] line out of a real run; it read \
         nothing (single {single:?}, scaled {scaled:?}) — an instrument that \
         measures nothing reports green forever"
    );
    let (allocs, _) = single.rc.unwrap();
    assert!(
        allocs > 0,
        "the baseline cell MUST actually allocate (got allocs={allocs}); a \
         zero-allocation baseline would make every balance assertion vacuous"
    );
    assert_eq!(
        verdict(3, single, single, scaled, scaled, true),
        vec![],
        "a real clean cell MUST verdict clean — otherwise the fault fences below \
         prove nothing"
    );
}

// PLANTED LEAK (synthetic): one allocation never freed, constant across
// iteration counts. MUST be reported as `Leak`, and MUST NOT be misreported as
// `Scaling` — a constant residue and a per-iteration leak are different defects.
// This is the class our own `residue <= 8` pins could not see at a residue of 1,
// so the plant is deliberately of size 1.
// spec: spec/12-runtime.md §12.3.1 — Requirements.
#[test]
fn gen_flows_capability_detects_planted_constant_leak() {
    let (single, scaled) = fence_baseline();
    let bump_allocs = |m: Measure, n: i64| Measure {
        rc: m.rc.map(|(a, d)| (a + n, d)),
        ..m
    };
    let faults = verdict(
        3,
        bump_allocs(single, 1),
        single,
        bump_allocs(scaled, 1),
        scaled,
        true,
    );
    assert!(
        faults.contains(&Fault::Leak { count: 1 }),
        "the harness MUST detect a planted CONSTANT leak of 1 allocation; got {faults:?}"
    );
    assert!(
        !faults.iter().any(|f| matches!(f, Fault::Scaling { .. })),
        "a constant leak MUST NOT be reported as scaling — the two classes are \
         distinguished by the iteration axis; got {faults:?}"
    );
}

// PLANTED OVER-RELEASE (synthetic): one more dealloc than alloc — the polarity
// NO residue allowance in any direction ever catches, and the direction that is
// a double-free rather than a leak. MUST be reported as `OverRelease`, never
// swallowed and never miscalled a leak.
// spec: spec/12-runtime.md §12.3.1 — Requirements (a heap value MUST NOT be freed
// while it is still reachable).
#[test]
fn gen_flows_capability_detects_planted_over_release() {
    let (single, scaled) = fence_baseline();
    let bump_deallocs = |m: Measure, n: i64| Measure {
        rc: m.rc.map(|(a, d)| (a, d + n)),
        ..m
    };
    let faults = verdict(
        3,
        bump_deallocs(single, 1),
        single,
        bump_deallocs(scaled, 1),
        scaled,
        true,
    );
    assert!(
        faults.contains(&Fault::OverRelease { count: 1 }),
        "the harness MUST detect a planted OVER-RELEASE of 1 dealloc — the \
         polarity a residue allowance is blind to in principle; got {faults:?}"
    );
    assert!(
        !faults.iter().any(|f| matches!(f, Fault::Leak { .. })),
        "an over-release MUST NOT be reported as a leak; got {faults:?}"
    );
}

// PLANTED SCALING FAULT (synthetic): the imbalance grows by 1 per iteration
// while the single-shot run stays clean. This is the shape of every leak S115
// shipped (0749, 0753, 0760 — all per-iteration), and the reason the harness
// runs each cell at two iteration counts. MUST be reported as `Scaling` with the
// right RATE, so a reader can tell a growing leak from a one-off residue.
// spec: spec/12-runtime.md §12.3.1 — Requirements.
#[test]
fn gen_flows_capability_detects_planted_per_iteration_scaling_leak() {
    let (single, scaled) = fence_baseline();
    let leaky_scaled = Measure {
        rc: scaled.rc.map(|(a, d)| (a + (ITERS - 1), d)),
        ..scaled
    };
    let faults = verdict(3, single, single, leaky_scaled, scaled, true);
    assert!(
        faults.contains(&Fault::Scaling { per_iteration: 1 }),
        "the harness MUST detect a planted PER-ITERATION leak of 1/iteration and \
         report its rate; got {faults:?}"
    );
    assert!(
        faults.contains(&Fault::Leak {
            count: ITERS - 1
        }),
        "the scaled run's absolute imbalance MUST also be reported (the exact \
         balance face is asserted at every iteration count, not only at 1); got \
         {faults:?}"
    );
}

// UNMEASURED RUN (synthetic): a run that emitted no `[RC_STATS]` line MUST be a
// fault, not a silent pass. This is the instrument-reads-nothing failure mode
// that made an early probe of this very harness report 0/0 (and therefore
// "balanced") for programs that failed to compile.
// spec: spec/12-runtime.md §12.3.1 — Requirements.
#[test]
fn gen_flows_capability_detects_unmeasured_run() {
    let (single, scaled) = fence_baseline();
    let blind = Measure {
        rc: None,
        ..single
    };
    let faults = verdict(3, blind, single, scaled, scaled, true);
    assert!(
        faults.contains(&Fault::NoMeasurement),
        "a run with no [RC_STATS] line MUST be reported as unmeasured, never \
         treated as balanced; got {faults:?}"
    );
}
