// r1_alias_borrowed_shadow_leak.rs — FIXME 0692 (Important, leak regression in
// f9435b37). W4's R1 alias-binding recognition registers a `Var`-aliasing `let`
// binding as non-owning via `mark_borrowed(name)`. But the backing `borrowed_vars`
// set was fn-lifetime and NAME-keyed — never cleared on scope exit — so a later
// shadow or sibling binding of the SAME name to an OWNED value inherited the
// stale mark and had its scope-dec skipped (a leak).
//
// The mark is a property of a *binder*, not a *name* (Principle 20; the 0632
// name-as-identity class). Fix: scope-stratify the mark (per-frame, resolved
// against the innermost binding). Leak polarity only — the mark never adds a
// dec — but it breaks `allocs == deallocs` on legal name reuse, which is common
// in real code. Free-standing (PrimitivesOnly, no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn run_prims(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(src)
        .env("CRANELISP_RC_STATS", "1")
        .output()
}

fn rc_alloc_dealloc(stderr: &str) -> (i64, i64) {
    let line = stderr
        .lines()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("no [RC_STATS] line:\n{stderr}"));
    let field = |k: &str| -> i64 {
        line.split_whitespace()
            .find_map(|t| t.strip_prefix(k).and_then(|v| v.parse().ok()))
            .unwrap_or_else(|| panic!("no {k} in: {line}"))
    };
    (field("allocs="), field("deallocs="))
}

// Outer `q` aliases the param `v` (marked borrowed by R1). Inner `q` SHADOWS it
// with a fresh OWNED `[7 8 9]` — which must scope-dec normally. The stale outer
// mark made the inner owned `q`'s dec be skipped: allocs=3 deallocs=2 (the fresh
// `[7 8 9]` leaked).
const SHADOW_REUSE: &str = "(defn f [v] (let [q v] (let [q [7 8 9]] (vec-get q 0))))\n\
     (defn main [] (Pure (f [1 2 3])))\n";

// Control: the inner binding renamed `r` (no name collision) — always balanced.
const RENAMED_CONTROL: &str = "(defn f [v] (let [q v] (let [r [7 8 9]] (vec-get r 0))))\n\
     (defn main [] (Pure (f [1 2 3])))\n";

// 0692 pin — the shadow-reuse binding MUST balance: the inner OWNED `q` is a
// distinct binder from the outer borrowed `q` and carries its own scope-dec.
// spec: spec/12-runtime.md §12.3.1 — a heap value MUST be freed when no longer
// reachable; a fresh owned binding's scope-dec is not suppressed by a
// name-colliding outer alias.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs (fn-lifetime name-keyed borrowed_vars — an R1 alias mark on an outer binding leaked a later owned binding of the same name) found=S114 owner=/dev
#[test]
fn shadow_reuse_owned_binding_does_not_leak() {
    let out = run_prims(SHADOW_REUSE);
    let (allocs, deallocs) = rc_alloc_dealloc(&out.stderr);
    assert_eq!(
        allocs, deallocs,
        "the inner OWNED `q` (shadowing the outer borrowed alias `q`) MUST \
         scope-dec — the fresh [7 8 9] must not leak: allocs={allocs} \
         deallocs={deallocs}.\nstderr:\n{}",
        out.stderr
    );
}

// 0692 CONTROL (GREEN) — with the inner binding renamed `r` there is no name
// collision, so the binding balanced even before the fix. The twin that pins the
// name-reuse (not the let-nesting) as the defect's locus.
// spec: spec/12-runtime.md §12.3.1 — a distinctly-named owned binding is freed
// at scope exit.
#[test]
fn renamed_inner_binding_balances_green() {
    let out = run_prims(RENAMED_CONTROL);
    let (allocs, deallocs) = rc_alloc_dealloc(&out.stderr);
    assert_eq!(
        allocs, deallocs,
        "the renamed control MUST balance: allocs={allocs} deallocs={deallocs}.\n\
         stderr:\n{}",
        out.stderr
    );
}
