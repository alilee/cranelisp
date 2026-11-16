//! S123 U-1 to U-3 and U-5, through public process boundaries.
//! Before U′, forwarded aliases were freed early and forwarding joins leaked.
#[path = "helpers/mod.rs"]
mod helpers;
use helpers::marginal::{Child, MarginalPair};

const IMPORT: &str =
    "(import [primitives [Pure add-i64 eq-i64 vec-len vec-push vec-set vec-get]])\n";
fn child(defs: &str, mode: &str) -> Child {
    let program = format!("{IMPORT}{defs}");
    let child = match mode {
        "repl" => Child::repl(&format!(
            "{}\n(main)\n",
            program.lines().collect::<Vec<_>>().join("\n")
        )),
        "link" => Child::new(&program).link_then_run(),
        "run" => Child::new(&program),
        _ => unreachable!(),
    };
    child.env("CRANELISP_RC_DEC_CHECK", "1")
}
fn check(label: &str, control: &str, subject: &str, expected: i32, mode: &str) {
    let pair = MarginalPair::new(label, child(control, mode), child(subject, mode)).measure();
    eprintln!("{mode}: {}", pair.report());
    for half in [pair.control(), pair.subject()] {
        if mode == "repl" {
            assert_eq!(
                half.exit_code(),
                Some(0),
                "REPL must exit normally: {}",
                half.stderr
            );
            assert!(
                half.stdout
                    .contains(&format!(":primitives/Int {expected}\n")),
                "expected full REPL result {expected}: {}",
                half.stdout
            );
        } else {
            assert_eq!(
                half.exit_code(),
                Some(expected),
                "computed value: {}",
                half.stderr
            );
        }
    }
    pair.assert_balanced(label);
}
fn tail(arg: &str) -> String {
    format!(
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (go (add-i64 n -1) (vec-push q 1) {arg})])))\n(defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))\n"
    )
}
const OWNED: &str = "(let [t (match p [b b]) u (vec-push [] 0)] alias)";

// spec: spec/12-runtime.md §12.3.1 — U-1: a forwarded alias stays live.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_tail_self_call found=S122 owner=/dev fixed=S123/3bdf398e
#[test]
fn tail_heap_free_alias_run() {
    check(
        "U-1 heap_free",
        &tail(OWNED),
        &tail("(let [t (match p [b b])] alias)"),
        3,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-1: a forwarded alias stays live.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_tail_self_call found=S122 owner=/dev fixed=S123/3bdf398e
#[test]
fn tail_shadowed_alias_run() {
    check(
        "U-1 shadowed",
        &tail(OWNED),
        &tail("(let [t (match p [alias alias])] alias)"),
        3,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-1 owned-binder control.
#[test]
fn tail_owned_binder_control_run() {
    check("U-1 owned control", &tail(OWNED), &tail(OWNED), 3, "run");
}

// spec: spec/12-runtime.md §12.3.1 — U-2: a forwarding join releases once.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::value_provenance_with_calls found=S122 owner=/dev fixed=S123/3bdf398e
#[test]
fn forwarding_match_balances_run() {
    check(
        "U-2 match",
        "(defn f [] (match [1 2] [r r]))\n(defn main [] (Pure (vec-len (f))))",
        "(defn f [] (vec-len (match [1 2] [r r])))\n(defn main [] (Pure (f)))",
        2,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-2: a forwarding join releases once.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::value_provenance_with_calls found=S122 owner=/dev fixed=S123/3bdf398e
#[test]
fn forwarding_let_balances_run() {
    check(
        "U-2 let",
        "(defn f [] (let [r [1 2]] r))\n(defn main [] (Pure (vec-len (f))))",
        "(defn f [] (vec-len (let [r [1 2]] r)))\n(defn main [] (Pure (f)))",
        2,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-2: a forwarding join releases once.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler found=S122 owner=/dev fixed=S123/3bdf398e
// ACT-1028 leaked at the checkpoint; U′ removed the per-shape counting paths.
#[test]
fn forwarding_set_balances_run() {
    check(
        "U-2 set",
        "(defn f [v] (vec-set v 0 5))\n(defn main [] (Pure (vec-len (f (vec-push [] 1)))))",
        "(defn f [v] (let [w (vec-set v 0 5)] w))\n(defn main [] (Pure (vec-len (f (vec-push [] 1)))))",
        1,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-1: a forwarded alias stays live.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_tail_self_call found=S122 owner=/dev fixed=S123/3bdf398e
#[test]
fn tail_heap_free_alias_link() {
    check(
        "U-1 heap_free",
        &tail(OWNED),
        &tail("(let [t (match p [b b])] alias)"),
        3,
        "link",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-1: a forwarded alias stays live.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_tail_self_call found=S122 owner=/dev fixed=S123/3bdf398e
#[test]
fn tail_shadowed_alias_link() {
    check(
        "U-1 shadowed",
        &tail(OWNED),
        &tail("(let [t (match p [alias alias])] alias)"),
        3,
        "link",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-1 owned-binder control.
#[test]
fn tail_owned_binder_control_link() {
    check("U-1 owned control", &tail(OWNED), &tail(OWNED), 3, "link");
}

// spec: spec/12-runtime.md §12.3.1 — U-2: a forwarding join releases once.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::value_provenance_with_calls found=S122 owner=/dev fixed=S123/3bdf398e
#[test]
fn forwarding_match_balances_link() {
    check(
        "U-2 match",
        "(defn f [] (match [1 2] [r r]))\n(defn main [] (Pure (vec-len (f))))",
        "(defn f [] (vec-len (match [1 2] [r r])))\n(defn main [] (Pure (f)))",
        2,
        "link",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-2: a forwarding join releases once.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::value_provenance_with_calls found=S122 owner=/dev fixed=S123/3bdf398e
#[test]
fn forwarding_let_balances_link() {
    check(
        "U-2 let",
        "(defn f [] (let [r [1 2]] r))\n(defn main [] (Pure (vec-len (f))))",
        "(defn f [] (vec-len (let [r [1 2]] r)))\n(defn main [] (Pure (f)))",
        2,
        "link",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-2: a forwarding join releases once.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler found=S122 owner=/dev fixed=S123/3bdf398e
// ACT-1028 leaked at the checkpoint; U′ removed the per-shape counting paths.
#[test]
fn forwarding_set_balances_link() {
    check(
        "U-2 set",
        "(defn f [v] (vec-set v 0 5))\n(defn main [] (Pure (vec-len (f (vec-push [] 1)))))",
        "(defn f [v] (let [w (vec-set v 0 5)] w))\n(defn main [] (Pure (vec-len (f (vec-push [] 1)))))",
        1,
        "link",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-1: a forwarded alias stays live.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_tail_self_call found=S122 owner=/dev fixed=S123/3bdf398e
#[test]
fn tail_heap_free_alias_repl() {
    check(
        "U-1 heap_free",
        &tail(OWNED),
        &tail("(let [t (match p [b b])] alias)"),
        3,
        "repl",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-1: a forwarded alias stays live.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_tail_self_call found=S122 owner=/dev fixed=S123/3bdf398e
#[test]
fn tail_shadowed_alias_repl() {
    check(
        "U-1 shadowed",
        &tail(OWNED),
        &tail("(let [t (match p [alias alias])] alias)"),
        3,
        "repl",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-1 owned-binder control.
#[test]
fn tail_owned_binder_control_repl() {
    check("U-1 owned control", &tail(OWNED), &tail(OWNED), 3, "repl");
}

// spec: spec/12-runtime.md §12.3.1 — U-2: a forwarding join releases once.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::value_provenance_with_calls found=S122 owner=/dev fixed=S123/3bdf398e
#[test]
fn forwarding_match_balances_repl() {
    check(
        "U-2 match",
        "(defn f [] (match [1 2] [r r]))\n(defn main [] (Pure (vec-len (f))))",
        "(defn f [] (vec-len (match [1 2] [r r])))\n(defn main [] (Pure (f)))",
        2,
        "repl",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-2: a forwarding join releases once.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::value_provenance_with_calls found=S122 owner=/dev fixed=S123/3bdf398e
#[test]
fn forwarding_let_balances_repl() {
    check(
        "U-2 let",
        "(defn f [] (let [r [1 2]] r))\n(defn main [] (Pure (vec-len (f))))",
        "(defn f [] (vec-len (let [r [1 2]] r)))\n(defn main [] (Pure (f)))",
        2,
        "repl",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-2: a forwarding join releases once.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler found=S122 owner=/dev fixed=S123/3bdf398e
// ACT-1028 leaked at the checkpoint; U′ removed the per-shape counting paths.
#[test]
fn forwarding_set_balances_repl() {
    check(
        "U-2 set",
        "(defn f [v] (vec-set v 0 5))\n(defn main [] (Pure (vec-len (f (vec-push [] 1)))))",
        "(defn f [v] (let [w (vec-set v 0 5)] w))\n(defn main [] (Pure (vec-len (f (vec-push [] 1)))))",
        1,
        "repl",
    );
}

fn loop_program(update: &str, wrapper: &str, shared: bool, push: bool, n: usize) -> String {
    if shared {
        format!(
            "{wrapper}\n(defn go [n v keep] (if (eq-i64 n 0) (add-i64 (vec-len v) (vec-len keep)) (go (add-i64 n -1) {update} keep)))\n(defn main [] (Pure (let [a (vec-push [] 0)] (go {n} a a))))\n"
        )
    } else {
        let init = if push && wrapper.is_empty() {
            "[]"
        } else {
            "(vec-push [] 0)"
        };
        format!(
            "{wrapper}\n(defn go [n v] (if (eq-i64 n 0) (vec-len v) (go (add-i64 n -1) {update})))\n(defn main [] (Pure (go {n} {init})))\n"
        )
    }
}
fn in_place(label: &str, update: &str, wrapper: &str, shared: bool, push: bool) {
    // The first iteration is excluded by a one-iteration control.
    let pair = MarginalPair::new(
        label,
        child(&loop_program(update, wrapper, shared, push, 1), "run"),
        child(&loop_program(update, wrapper, shared, push, 1000), "run"),
    )
    .measure();
    eprintln!("{}", pair.report());
    let field = |stderr: &str, key: &str| -> i64 {
        stderr
            .lines()
            .find(|l| l.starts_with("[RC_STATS]"))
            .unwrap()
            .split_whitespace()
            .find_map(|s| s.strip_prefix(key))
            .unwrap()
            .parse()
            .unwrap()
    };
    let hits =
        field(&pair.subject().stderr, "reuse_hit=") - field(&pair.control().stderr, "reuse_hit=");
    let misses =
        field(&pair.subject().stderr, "reuse_miss=") - field(&pair.control().stderr, "reuse_miss=");
    eprintln!("{label}: iterations 2..1000: hit={hits} miss={misses}");
    assert_eq!(
        pair.control().exit_code(),
        Some(if shared {
            2
        } else if push && !wrapper.is_empty() {
            2
        } else {
            1
        })
    );
    assert_eq!(
        pair.subject().exit_code(),
        Some(if push {
            (1000 + i32::from(!wrapper.is_empty())) % 256
        } else if shared {
            2
        } else {
            1
        })
    );
    pair.assert_balanced(label);
    assert_eq!(
        hits, 999,
        "{label}: every update after the first must be in place (reuse_hit delta)"
    );
    assert_eq!(misses, 0, "{label}: no dynamic copies after the first");
}

// spec: spec/12-runtime.md §12.3.1 — U-5; design/backend/uniform-counting.md §2 U1.
#[test]
fn in_place_d1_after_first_iteration() {
    in_place("D1", "(vec-set v 0 n)", "", false, false);
}

// spec: spec/12-runtime.md §12.3.1 — U-5; design/backend/uniform-counting.md §2 U1.
#[test]
fn in_place_d2_after_first_iteration() {
    in_place("D2", "(vec-set v 0 n)", "", true, false);
}

// spec: spec/12-runtime.md §12.3.1 — U-5; design/backend/uniform-counting.md §2 U1.
#[test]
fn in_place_d4_after_first_iteration() {
    in_place("D4", "(vec-push v n)", "", false, true);
}

// spec: spec/12-runtime.md §12.3.1 — U-5; design/backend/uniform-counting.md §2 U1.
#[test]
fn in_place_l1_after_first_iteration() {
    in_place(
        "L1",
        "(myconj v n)",
        "(defn myconj [v x] (vec-push v x))",
        false,
        true,
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-5; design/backend/uniform-counting.md §2 U1.
#[test]
fn in_place_l3_after_first_iteration() {
    in_place(
        "L3",
        "(myassoc v 0 n)",
        "(defn myassoc [v i x] (vec-set v i x))",
        false,
        false,
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 r1, independently observed control.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_r1_control() {
    check(
        "U-3 r1 control",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (let [k (match p [b (vec-len b)])] (go (add-i64 n -1) (vec-push q k) alias))])))\n(defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (let [k (match p [b (vec-len b)])] (go (add-i64 n -1) (vec-push q k) alias))])))\n(defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))",
        3,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 r1, independently observed subject.
// At f5822487 this stopped with USE-AFTER-FREE.
// defect: class=binder-name-underkey locus=crates/cranelisp-backend/src/heap.rs::register_alias found=S123 owner=/dev fixed=S123/3bdf398e
// U′ deleted the name-keyed alias-map seam; read compiler/ownership_plan.rs today.
#[test]
fn lead_r1_subject() {
    check(
        "U-3 r1 subject",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (let [k (match p [b (vec-len b)])] (go (add-i64 n -1) (vec-push q k) alias))])))\n(defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (let [k (match p [alias (vec-len alias)])] (go (add-i64 n -1) (vec-push q k) alias))])))\n(defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))",
        3,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 l2, independently observed control.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_l2_control() {
    check(
        "U-3 l2 control",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (go (add-i64 n -1) (vec-push q 1) alias)])))\n(defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (go (add-i64 n -1) (vec-push q 1) alias)])))\n(defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))",
        3,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 l2, independently observed subject.
// At f5822487 this stopped with USE-AFTER-FREE.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_tail_self_call found=S123 owner=/dev fixed=S123/3bdf398e
// The historical locus was provisional; the armed stop established the fault.
#[test]
fn lead_l2_subject() {
    check(
        "U-3 l2 subject",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (go (add-i64 n -1) (vec-push q 1) alias)])))\n(defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (go (add-i64 n -1) (vec-push q 1) (if (eq-i64 n 1) alias alias))])))\n(defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))",
        3,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 l6, independently observed control.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_l6_control() {
    check(
        "U-3 l6 control",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (go (add-i64 n -1) (vec-push q 1) (let [k 1 u (vec-push [] 0)] alias))])))\n(defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (go (add-i64 n -1) (vec-push q 1) (let [k 1 u (vec-push [] 0)] alias))])))\n(defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))",
        3,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 l6, independently observed subject.
// At f5822487 this stopped with USE-AFTER-FREE.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_tail_self_call found=S123 owner=/dev fixed=S123/3bdf398e
// The historical locus was provisional; the armed stop established the fault.
#[test]
fn lead_l6_subject() {
    check(
        "U-3 l6 subject",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (go (add-i64 n -1) (vec-push q 1) (let [k 1 u (vec-push [] 0)] alias))])))\n(defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (go (add-i64 n -1) (vec-push q 1) (let [k 1] alias))])))\n(defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))",
        3,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 l5, independently observed control.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_l5_control() {
    check(
        "U-3 l5 control",
        "(deftype Flag Off On)\n(defn go [n v] (if (eq-i64 n 0) (vec-len v) (go (add-i64 n -1) v)))\n(defn main [] (Pure (go 3 [7])))",
        "(deftype Flag Off On)\n(defn go [n v] (if (eq-i64 n 0) (vec-len v) (go (add-i64 n -1) v)))\n(defn main [] (Pure (go 3 [7])))",
        1,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 l5, independently observed subject.
// At f5822487 this stopped with STALE RC DEC.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_tail_self_call found=S123 owner=/dev fixed=S123/3bdf398e
// The historical locus was provisional; the armed stop established the fault.
#[test]
fn lead_l5_subject() {
    check(
        "U-3 l5 subject",
        "(deftype Flag Off On)\n(defn go [n v] (if (eq-i64 n 0) (vec-len v) (go (add-i64 n -1) v)))\n(defn main [] (Pure (go 3 [7])))",
        "(deftype Flag Off On)\n(defn go [n v] (if (eq-i64 n 0) (vec-len v) (go (add-i64 n -1) (match Off [Off v On v]))))\n(defn main [] (Pure (go 3 [7])))",
        1,
        "run",
    );
}

fn l4_tail(q_arg: &str) -> String {
    format!(
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (go (add-i64 n -1) p {q_arg})))\n(defn main [] (Pure (go 3 [7] [8])))"
    )
}

// spec: spec/12-runtime.md §12.3.1 — U-3 L4, independently observed direct control.
// Checkpoint face: balanced at f5822487 plus W2 work.
#[test]
fn lead_l4_control() {
    check(
        "U-3 L4 direct control",
        &l4_tail("q"),
        &l4_tail("q"),
        2,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 L4: duplicate tail arguments retain both references.
// At f5822487 plus the initial W2 work this stopped with STALE RC DEC.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_tail_self_call found=S123 owner=/dev fixed=S123/3bdf398e
#[test]
fn lead_l4_direct_subject() {
    check(
        "U-3 L4 direct subject",
        &l4_tail("q"),
        &l4_tail("p"),
        2,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 L4, independently observed branch control.
// Checkpoint face: balanced at f5822487 plus W2 work.
#[test]
fn lead_l4_branch_control() {
    let control = l4_tail("(if (eq-i64 n 1) q q)");
    check("U-3 L4 branch control", &control, &control, 2, "run");
}

// spec: spec/12-runtime.md §12.3.1 — U-3 L4: a branch forwards a live tail argument.
// At f5822487 plus the initial W2 work this stopped with STALE RC DEC.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_tail_self_call found=S123 owner=/dev fixed=S123/3bdf398e
#[test]
fn lead_l4_branch_subject() {
    check(
        "U-3 L4 branch subject",
        &l4_tail("(if (eq-i64 n 1) q q)"),
        &l4_tail("(if (eq-i64 n 1) p q)"),
        2,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 l7_let, independently observed control.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_l7_let_control() {
    check(
        "U-3 l7_let control",
        "(defn go [n p] (if (eq-i64 n 0) (vec-len p) (go (add-i64 n -1) (vec-push p 1))))\n(defn main [] (Pure (go 3 [7])))",
        "(defn go [n p] (if (eq-i64 n 0) (vec-len p) (go (add-i64 n -1) (vec-push p 1))))\n(defn main [] (Pure (go 3 [7])))",
        4,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 l7_let, independently observed subject.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_l7_let_subject() {
    check(
        "U-3 l7_let subject",
        "(defn go [n p] (if (eq-i64 n 0) (vec-len p) (go (add-i64 n -1) (vec-push p 1))))\n(defn main [] (Pure (go 3 [7])))",
        "(defn go [n p] (if (eq-i64 n 0) (vec-len p) (let [v p] (go (add-i64 n -1) (vec-push v 1)))))\n(defn main [] (Pure (go 3 [7])))",
        4,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 l7_branch, independently observed control.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_l7_branch_control() {
    check(
        "U-3 l7_branch control",
        "(defn go [n p] (if (eq-i64 n 0) (vec-len p) (go (add-i64 n -1) (vec-push p 1))))\n(defn main [] (Pure (go 3 [7])))",
        "(defn go [n p] (if (eq-i64 n 0) (vec-len p) (go (add-i64 n -1) (vec-push p 1))))\n(defn main [] (Pure (go 3 [7])))",
        4,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 l7_branch, independently observed subject.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_l7_branch_subject() {
    check(
        "U-3 l7_branch subject",
        "(defn go [n p] (if (eq-i64 n 0) (vec-len p) (go (add-i64 n -1) (vec-push p 1))))\n(defn main [] (Pure (go 3 [7])))",
        "(defn go [n p] (if (eq-i64 n 0) (vec-len p) (go (add-i64 n -1) (if (eq-i64 n 1) (vec-push p 1) (vec-push p 1)))))\n(defn main [] (Pure (go 3 [7])))",
        4,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 l9, independently observed control.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_l9_control() {
    check(
        "U-3 l9 control",
        "(defn f [v] (vec-push v 3))\n(defn main [] (Pure (vec-len (f [7 8 9]))))",
        "(defn f [v] (vec-push v 3))\n(defn main [] (Pure (vec-len (f [7 8 9]))))",
        4,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 l9, independently observed subject.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_l9_subject() {
    check(
        "U-3 l9 subject",
        "(defn f [v] (vec-push v 3))\n(defn main [] (Pure (vec-len (f [7 8 9]))))",
        "(defn f [v] (vec-push v (vec-len v)))\n(defn main [] (Pure (vec-len (f [7 8 9]))))",
        4,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 l10, independently observed control.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_l10_control() {
    check(
        "U-3 l10 control",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (go (add-i64 n -1) (vec-push q 1) alias)])))\n(defn main [] (Pure (go 3 [7] [9])))",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (go (add-i64 n -1) (vec-push q 1) alias)])))\n(defn main [] (Pure (go 3 [7] [9])))",
        3,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 l10, independently observed subject.
// At f5822487 this stopped with USE-AFTER-FREE.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_tail_self_call found=S123 owner=/dev fixed=S123/3bdf398e
// The historical locus was provisional; the armed stop established the fault.
#[test]
fn lead_l10_subject() {
    check(
        "U-3 l10 subject",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match q [alias (go (add-i64 n -1) (vec-push q 1) alias)])))\n(defn main [] (Pure (go 3 [7] [9])))",
        "(defn go [n p q] (if (eq-i64 n 0) (add-i64 (vec-len p) (vec-len q)) (match (if (eq-i64 n 1) q q) [alias (go (add-i64 n -1) (vec-push q 1) alias)])))\n(defn main [] (Pure (go 3 [7] [9])))",
        3,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 consume_if, independently observed control.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_consume_if_control() {
    check(
        "U-3 consume_if control",
        "(defn f [n v] (vec-len v))\n(defn main [] (Pure (f 0 [7 8])))",
        "(defn f [n v] (vec-len v))\n(defn main [] (Pure (f 0 [7 8])))",
        2,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 consume_if, independently observed subject.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_consume_if_subject() {
    check(
        "U-3 consume_if subject",
        "(defn f [n v] (vec-len v))\n(defn main [] (Pure (f 0 [7 8])))",
        "(defn f [n v] (vec-len (if (eq-i64 n 0) v v)))\n(defn main [] (Pure (f 0 [7 8])))",
        2,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 consume_let, independently observed control.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_consume_let_control() {
    check(
        "U-3 consume_let control",
        "(defn f [n v] (vec-len v))\n(defn main [] (Pure (f 0 [7 8])))",
        "(defn f [n v] (vec-len v))\n(defn main [] (Pure (f 0 [7 8])))",
        2,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 consume_let, independently observed subject.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_consume_let_subject() {
    check(
        "U-3 consume_let subject",
        "(defn f [n v] (vec-len v))\n(defn main [] (Pure (f 0 [7 8])))",
        "(defn f [n v] (vec-len (let [a v] a)))\n(defn main [] (Pure (f 0 [7 8])))",
        2,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 consume_match, independently observed control.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_consume_match_control() {
    check(
        "U-3 consume_match control",
        "(defn f [n v] (vec-len v))\n(defn main [] (Pure (f 0 [7 8])))",
        "(defn f [n v] (vec-len v))\n(defn main [] (Pure (f 0 [7 8])))",
        2,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 consume_match, independently observed subject.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_consume_match_subject() {
    check(
        "U-3 consume_match subject",
        "(defn f [n v] (vec-len v))\n(defn main [] (Pure (f 0 [7 8])))",
        "(defn f [n v] (vec-len (match v [a a])))\n(defn main [] (Pure (f 0 [7 8])))",
        2,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 shadowed_root, independently observed control.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_shadowed_root_control() {
    check(
        "U-3 shadowed_root control",
        "(defn f [p q] (let [n (match q [view (vec-len view)])] (add-i64 n (vec-len p))))\n(defn main [] (Pure (f [7] [8 9])))",
        "(defn f [p q] (let [n (match q [view (vec-len view)])] (add-i64 n (vec-len p))))\n(defn main [] (Pure (f [7] [8 9])))",
        3,
        "run",
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-3 shadowed_root, independently observed subject.
// Checkpoint face: balanced at f5822487.
#[test]
fn lead_shadowed_root_subject() {
    check(
        "U-3 shadowed_root subject",
        "(defn f [p q] (let [n (match q [view (vec-len view)])] (add-i64 n (vec-len p))))\n(defn main [] (Pure (f [7] [8 9])))",
        "(defn f [p q] (let [n (match q [p (vec-len p)])] (add-i64 n (vec-len p))))\n(defn main [] (Pure (f [7] [8 9])))",
        3,
        "run",
    );
}

fn ordered_or_wrapped(label: &str, defs: &str, body: &str, expected: i32) {
    for moves_off in [false, true] {
        let program = |body: &str| {
            format!(
                "(import [primitives [*]])\n{defs}\n(defn work [] {body})\n(defn main [] (work))\n"
            )
        };
        let control = program(&format!("(Pure {expected})"));
        let subject = program(body);
        let armed = |program: &str| {
            let c = Child::new(program).env("CRANELISP_RC_DEC_CHECK", "1");
            if moves_off {
                c.env("CRANELISP_NO_OWNERSHIP", "1")
            } else {
                c
            }
        };
        let label = format!("{label}, moves_off={moves_off}");
        let m = MarginalPair::new(&label, armed(&control), armed(&subject)).measure();
        eprintln!("{}", m.report());
        for half in [m.control(), m.subject()] {
            assert_eq!(
                half.exit_code(),
                Some(expected),
                "{}\n{}",
                m.report(),
                half.stderr
            );
        }
        m.assert_balanced(&label);
    }
}

// spec: design/backend/uniform-counting.md §3.2 — U-15 builtin Apply operands.
#[test]
fn operand_order_apply_duplicates_before_moving() {
    ordered_or_wrapped(
        "U-15 Apply",
        "",
        "(Pure (let [v [1 2 3]] (add-i64 (vec-len v) (vec-len v))))",
        6,
    );
}

// spec: design/backend/uniform-counting.md §3.2 — U-15 closure-call operands.
#[test]
fn operand_order_closure_call_duplicates_before_moving() {
    ordered_or_wrapped(
        "U-15 closure call",
        "(defn call [f v] (f (vec-len v) v))",
        "(Pure (call (fn [n xs] (add-i64 n (vec-len xs))) [1 2 3]))",
        6,
    );
}

// spec: design/backend/uniform-counting.md §3.2 — U-15 tail self-call operands.
#[test]
fn operand_order_tail_call_duplicates_before_moving() {
    ordered_or_wrapped(
        "U-15 tail call",
        "(defn go [n acc v] (if (eq-i64 n 0) (add-i64 acc (vec-len v)) (go (add-i64 n -1) (add-i64 acc (vec-len v)) v)))",
        "(Pure (go 4 0 [1 2 3]))",
        15,
    );
}

// spec: design/backend/uniform-counting.md §3.2 — U-15 Vec element operands.
#[test]
fn operand_order_vec_literal_duplicates_before_moving() {
    ordered_or_wrapped(
        "U-15 Vec literal",
        "",
        "(Pure (let [v [1 2 3] both [v v]] (add-i64 (vec-len (vec-get both 0)) (vec-len (vec-get both 1)))))",
        6,
    );
}

// spec: design/backend/uniform-counting.md §3.2 — U-15 constructor field operands.
#[test]
fn operand_order_constructor_duplicates_before_moving() {
    ordered_or_wrapped(
        "U-15 constructor",
        "(deftype Both [:(Vec Int) left :(Vec Int) right])",
        "(Pure (let [v [1 2 3]] (match (Both v v) [(Both a b) (add-i64 (vec-len a) (vec-len b))])))",
        6,
    );
}

// spec: design/backend/uniform-counting.md §3.2 — U-15 binding operand before continuation capture.
#[test]
fn operand_order_par_binding_duplicates_before_continuation_capture() {
    ordered_or_wrapped(
        "U-15 ParBind",
        "(platform test-capture)\n(import [platform.test-capture [commutative-sleep-ms commutative-noop]])",
        "(let [v [1 2 3]] (bind (commutative-sleep-ms (vec-len v)) (fn [a] (bind (commutative-noop) (fn [b] (Pure (add-i64 (add-i64 a b) (vec-len v))))))))",
        6,
    );
}

// spec: design/backend/uniform-counting.md §3.3 — U-16 curried capture survives two calls.
#[test]
fn wrapper_curried_heap_capture_survives_two_calls() {
    ordered_or_wrapped(
        "U-16 curried heap capture",
        "(defn f [v n] (add-i64 (vec-len v) n))",
        "(Pure (let [g (f [1 2])] (add-i64 (g 1) (g 2))))",
        7,
    );
}

// spec: design/backend/uniform-counting.md §3.3 — U-16 curried closure-value target.
#[test]
fn wrapper_curried_closure_value_forwards_capture() {
    ordered_or_wrapped(
        "U-16 curried closure target",
        "(defn curry [:(Fn [(Vec Int) Int] Int) f v] (f v))",
        "(Pure (let [bias [9] f (fn [v n] (add-i64 (vec-len bias) (add-i64 (vec-len v) n))) g (curry f [1 2])] (add-i64 (g 1) (g 2))))",
        9,
    );
}

// spec: design/backend/uniform-counting.md §3.3 — U-16 function value consumes heap argument.
#[test]
fn wrapper_function_value_consumes_heap_argument() {
    ordered_or_wrapped(
        "U-16 function value",
        "(defn ap [f x] (f x))",
        "(Pure (ap vec-len [1 2 3]))",
        3,
    );
}

// spec: design/backend/uniform-counting.md §3.3 — U-16 constructor value forwards heap field.
#[test]
fn wrapper_constructor_value_forwards_heap_field() {
    ordered_or_wrapped(
        "U-16 constructor value",
        "(deftype Box [:(Vec Int) items])\n(defn ap [f x] (f x))",
        "(Pure (match (ap Box [1 2 3]) [(Box xs) (vec-len xs)]))",
        3,
    );
}

// spec: design/backend/uniform-counting.md §3.3 — U-16 single-parameter trait method value.
#[test]
fn wrapper_trait_method_value_consumes_heap_argument() {
    ordered_or_wrapped(
        "U-16 trait method value",
        "(deftrait Sizeable (size [a] Int))\n(impl Sizeable String (defn size [s] (str-len s)))\n(defn ap [f x] (f x))",
        "(Pure (ap size (str-concat \"ab\" \"cde\")))",
        5,
    );
}
