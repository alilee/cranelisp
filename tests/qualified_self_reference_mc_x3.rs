// qualified_self_reference_mc_x3.rs — MC-X3 (S113, FIXME 0655).
//
// USER RULING (2026-07-19, TB-25 resolved-identity): a qualified own-module
// self-reference (`user/qloop` inside module `user`) is LEGAL — another spelling of
// the local binding. The dual-path audit (§3.5) found ONE resolver with a
// structural blind spot on the qualified leg; the fix normalizes the spelling at
// the ONE Var entry (a current-module qualifier IS the bare name), so all three
// modes collapse to the bare twin's behavior. The fix has LANDED: the three cells
// below (batch / REPL-fresh / REPL-redefine), originally ruling-agnostic
// no-codegen-leak pins, are now GREEN accept fences (MC-X3d — the §2.7 backend
// "carrier-absent = unreachable for well-typed" annotation is TRUE again). The
// `// defect:` line stays as the greppable record (past-tense). MC-X3a/b add the
// per-mode qualified≡bare accept twins + the absent-member uniform-diagnostic neg;
// MC-X5 pins the multi-sig self-qualified self-call still failing at the infer_apply
// raw-name gate. Free-standing (no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn has_codegen_leak(c: &str) -> bool {
    c.contains("undefined function") || c.contains("codegen error")
}

// Mode 1 — batch `--run`. The qualified self-reference is caught at the module
// graph (`circular dependency detected`) BEFORE codegen — a clean reject, no
// codegen leak. Ruling-agnostic invariant holds.
// spec: spec/08-modules.md §8.6.6 — qualified references; a self-module qualified
// reference must not leak a codegen error.
#[test]
fn qualified_own_module_self_ref_batch_no_codegen_leak() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(defn qloop [x] 0)\n\
             (defn qloop [x] (if true 0 (user/qloop 5)))\n\
             (defn main [] (Pure (qloop 1)))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !has_codegen_leak(&c),
        "[batch] a qualified own-module self-reference MUST NOT leak a codegen \
         error — it is caught at the module graph; got:\n{c}"
    );
}

// Mode 2 — REPL, fresh self-referencing defn. Caught at typecheck (`module 'user'
// has no member 'qloop'`) — a clean reject, no codegen leak.
// spec: spec/08-modules.md §8.6.6 — qualified references (REPL fresh).
#[test]
fn qualified_own_module_self_ref_repl_fresh_no_codegen_leak() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(defn qloop [x] (if true 0 (user/qloop 5)))\n")
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !has_codegen_leak(&c),
        "[repl-fresh] a qualified own-module self-reference MUST NOT leak a codegen \
         error — it is caught at typecheck; got:\n{c}"
    );
}

// Mode 3 — REPL, REDEFINE. The second defn typechecks (the pipeline reaches
// codegen) then fails hard: `codegen error … undefined function: user/qloop`. This
// is the RED — a well-typed program reaching a hard codegen error (the carrier was
// never recorded for `user/qloop` although typecheck resolved it). Flip: /dev
// (typecheck) records the carrier OR rejects check-side, uniformly across modes.
// spec: spec/08-modules.md §8.6.6 — qualified references (REPL redefine).
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck/src/checker.rs::record_reference_target (qualified leg silently drops the recording failure the typing path tolerated; well-typed form → codegen `undefined function: user/qloop`) found=S113 owner=/dev
#[test]
fn qualified_own_module_self_ref_repl_redefine_no_codegen_leak() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn qloop [x] 0)\n\
             (defn qloop [x] (if true 0 (user/qloop 5)))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !has_codegen_leak(&c),
        "[repl-redefine] a qualified own-module self-reference in a REDEFINITION \
         MUST NOT reach a hard codegen error on a well-typed program — typecheck \
         must record the carrier OR reject check-side (P25 check-gate); got:\n{c}"
    );
}

// ---- MC-X3a — qualified own-module reference ≡ bare twin (ACCEPT, born-green) ----

// The fresh self-recursive cell: `user/qloop` inside `qloop`'s own definition is
// legal recursion (≡ bare `qloop`). Both spellings run identically. `(qloop 3)` = 42.
// spec: spec/08-modules.md §8.6.6 — a current-module-qualified reference is the bare
// name (TB-25 resolved-identity).
#[test]
fn qualified_self_recursive_equals_bare_twin() {
    let prog = |call: &str| {
        format!(
            "(defn qloop [x] (if (eq-i64 x 0) 42 ({call} (add-i64 x -1))))\n\
             (defn main [] (Pure (qloop 3)))\n"
        )
    };
    let run = |src: &str| {
        Cranelisp::new()
            .with_prelude(PreludeVariant::PrimitivesOnly)
            .run("user.cl")
            .user(src)
            .output()
            .status
            .code()
    };
    let qualified = run(&prog("user/qloop"));
    let bare = run(&prog("qloop"));
    assert_eq!(
        qualified, bare,
        "the qualified self-recursive call `user/qloop` MUST behave identically to \
         the bare `qloop` (§8.6.6 resolved-identity); qualified={qualified:?} bare={bare:?}"
    );
    assert_eq!(qualified, Some(42), "both MUST run to 42; got {qualified:?}");
}

// The REPL face of the qualified≡bare twin.
// spec: spec/08-modules.md §8.6.6 — qualified own-module ref (REPL).
#[test]
fn qualified_self_ref_repl_equals_bare() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(defn q [x] (if (eq-i64 x 0) 42 (user/q (add-i64 x -1))))\n(q 3)\n")
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains(":primitives/Int 42") && !has_codegen_leak(&c),
        "[repl] `(q 3)` with a qualified self-recursive `user/q` MUST run to 42; got:\n{c}"
    );
}

// ---- MC-X3b — absent own-module member: uniform "no member" diagnostic (neg) ----

// A qualified reference to a genuinely-ABSENT own-module member is a UNIFORM
// resolution error in batch AND REPL-fresh — never a circular-dependency reject,
// never a codegen leak (mode-uniformity, AG-2 extract-and-compare). Post-fix the
// qualifier normalizes to the bare name, so the diagnostic uniformly names the
// absent member (`nosuch`) as an undefined variable — the same across modes.
// spec: spec/08-modules.md §8.6.6 — an absent own-module member is a uniform
// resolution error across modes.
#[test]
fn qualified_absent_own_member_uniform_diagnostic_neg() {
    // batch
    let batch = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn f [] (user/nosuch 5))\n(defn main [] (Pure 0))\n")
        .output();
    let bc = format!("{}{}", batch.stdout, batch.stderr);
    // REPL-fresh
    let repl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(defn f [] (user/nosuch 5))\n")
        .output();
    let rc = format!("{}{}", repl.stdout, repl.stderr);
    for (mode, c) in [("batch", &bc), ("repl-fresh", &rc)] {
        assert!(
            c.contains("nosuch") && !c.contains("circular") && !has_codegen_leak(c),
            "[{mode}] an absent own-module member `user/nosuch` MUST be a uniform \
             resolution error naming `nosuch` — never a circular-dependency reject, \
             never a codegen leak; got:\n{c}"
        );
    }
    // Mode-uniformity: both diagnostics name the member the same way.
    assert!(
        bc.contains("undefined variable: nosuch") == rc.contains("undefined variable: nosuch"),
        "batch and REPL-fresh MUST agree on the absent-member diagnostic \
         (AG-2 mode-uniformity).\nbatch:\n{bc}\nrepl-fresh:\n{rc}"
    );
}

// ---- MC-X5 — multi-sig SELF-QUALIFIED self-call at the infer_apply raw-name gate --

// The overload gates at `infer.rs:658/:678` read RAW AST names, so a multi-sig
// SELF-QUALIFIED self-call (`user/msig` inside `msig`) is not normalized at the gate
// — the written-name-identity class (register §3 row 7's sibling) at the overload-
// gate seam. Per the MC-X3 normalization contract, the qualified-spelled self-call
// MUST behave identically to the bare twin (accept + same dispatch). `(msig 3)` = 6.
// RED: today the qualified spelling is rejected at the gate. Bare twin GREEN.
// spec: spec/05-definitions.md §5.1.2 + spec/08-modules.md §8.6.6 — a qualified
// self-call to a multi-sig base is the bare name (dispatches identically).
// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/infer.rs:658/:678 (overload gate reads raw AST name; self-qualified multi-sig self-call not normalized — written-name-identity class) found=S113 owner=/dev
#[test]
fn multi_sig_self_qualified_self_call_equals_bare() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(defn msig\n\
             \x20 ([n]     (user/msig n 0))\n\
             \x20 ([n acc] (if (eq-i64 n 0) acc (msig (add-i64 n -1) (add-i64 acc n)))))\n\
             (defn main [] (Pure (msig 3)))\n",
        )
        .output();
    out.assert_exit(6);
}

// MC-X5 bare twin (GREEN) — the same multi-sig with a BARE self-call in the 1-arg
// entry clause dispatches to 6.
// spec: spec/05-definitions.md §5.1.2 — a bare multi-sig self-call.
#[test]
fn multi_sig_bare_self_call_control_green() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(defn msig\n\
             \x20 ([n]     (msig n 0))\n\
             \x20 ([n acc] (if (eq-i64 n 0) acc (msig (add-i64 n -1) (add-i64 acc n)))))\n\
             (defn main [] (Pure (msig 3)))\n",
        )
        .output()
        .assert_exit(6);
}
