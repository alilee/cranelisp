//! S100 Phase-3 `/qa` triage — value-use of the vec query family calls through
//! NULL GOT slots (spine `design/arch/ownership-inference.md` §3.1/§9 triage item).
//!
//! ## Verdict: REAL DEFECT (verified 2026-07-02, binary `target/debug/cranelisp`)
//!
//! `vec-get` / `vec-set` / `vec-push` are registered in the static primitives
//! table with allocated-but-NULL GOT slots — no extern body exists for them
//! (`crates/cranelisp-primitives/src/lib.rs::insert_vec_query_entries`, rustdoc
//! at ~:246: "their GOT slots stay null — name resolution is the sole gap these
//! entries close"). At statically-resolved call sites all four are inline-lowered
//! (`vec_codegen.rs`) and work. But when one is used as a VALUE — passed to a
//! user HOF — the backend's fn-as-value path (`fn_as_value.rs::compile_fn_as_value`
//! → `emit_wrapper_call`) synthesizes a wrapper whose body is a GOT-indirect
//! `call_indirect` through the primitive's slot. For `vec-get`/`vec-set`/`vec-push`
//! that slot is NULL → jump to address 0 → **SIGSEGV**, in BOTH `--run` and the
//! REPL (the REPL session process dies). `vec-len` — the one family member with a
//! real extern shim (`vec::vec_len`) — works through the same path (control test
//! below, GREEN).
//!
//! Reduction floor (all verified by hand before authoring): a single user HOF
//! `(defn call-get [f v i] (f v i))` + one vec literal is sufficient; no stdlib,
//! no prelude beyond `(import [primitives [*]])`, no `map` needed. The
//! `emit_wrapper_call` path has an inline-primitive fallback for the AUTO-CURRY
//! shape (`emit_curry_target_call` consults `primitives_inline`) but the plain
//! fn-as-value shape consults nothing — the natural fix location (owning skill:
//! `/backend`; the alternative — real extern bodies in `cranelisp-primitives` —
//! is blocked on element-type erasure, which is exactly why the slots are NULL).
//!
//! Failing-not-ignored per `memory/feedback_failing_not_ignored.md`; ledger entry
//! in `tests/plan/ledger.md` (S100 triage section); plan cross-ref
//! `tests/plan/s100-ownership-verification.md` §7. These flip GREEN when value-use
//! of the vec query family gets a working entry (spine §3.1: "the target design
//! implies every primitive gets a real GOT-backed value entry"). NOTE for the
//! resolver: `/repl`'s self-documenting principle aside, the REPL must never
//! SIGSEGV on valid input — the REPL-mode tests below pin process survival too.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output()
}

// spec: spec/04-expressions.md §4.6.2 — indirect calls: a named function passed
// as an argument is callable through the parameter. `vec-get` is a primitive
// function value per spec/appendix-a-builtins.md §A.3 (Fn [(Vec a) Int] a).
// RED on HEAD: SIGSEGV through the NULL vec-get GOT slot.
#[test]
fn vec_get_as_value_through_hof_returns_element() {
    repl_prims(
        "(defn call-get [f v i] (f v i))\n\
         (call-get vec-get [10 20 30] 1)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 20");
}

// spec: spec/04-expressions.md §4.6.2 — indirect calls (vec-set as a value).
// The result is inspected with a DIRECT (inline-lowered, known-good) vec-get so
// only the value-use of vec-set is under test. RED on HEAD: SIGSEGV.
#[test]
fn vec_set_as_value_through_hof_returns_updated_vec() {
    repl_prims(
        "(defn call-set [f v i x] (f v i x))\n\
         (vec-get (call-set vec-set [10 20 30] 1 99) 1)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 99");
}

// spec: spec/04-expressions.md §4.6.2 — indirect calls (vec-push as a value).
// RED on HEAD: SIGSEGV.
#[test]
fn vec_push_as_value_through_hof_appends() {
    repl_prims(
        "(defn call-push [f v x] (f v x))\n\
         (vec-get (call-push vec-push [10 20] 30) 2)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 30");
}

// spec: spec/04-expressions.md §4.6.2 — indirect calls; mode coverage: the same
// defect is observable under `--run` (crosses REPL/--run modes, so the e2e is
// warranted alongside the REPL shapes per tests/CLAUDE.md §unit-test-per-fix).
// `main` returns `(Pure 20)` ⇒ exit code 20 when fixed. RED on HEAD: SIGSEGV.
#[test]
fn vec_get_as_value_run_mode_returns_element() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [*]])\n\
             (defn call-get [f v i] (f v i))\n\
             (defn main []\n\
             \x20 (Pure (call-get vec-get [10 20 30] 1)))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(20);
}

// spec: spec/04-expressions.md §4.6.2 — indirect calls. CONTROL (GREEN on HEAD):
// `vec-len` is the one vec-query-family member with a populated GOT slot (the
// `vec::vec_len` extern shim), so its value-use works through the identical
// fn-as-value wrapper path. This pins the triage's root-cause boundary: the
// defect is the NULL slots, not the fn-as-value mechanism itself.
#[test]
fn vec_len_as_value_through_hof_returns_length_control() {
    repl_prims(
        "(defn call-len [f v] (f v))\n\
         (call-len vec-len [10 20 30])\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 3");
}
