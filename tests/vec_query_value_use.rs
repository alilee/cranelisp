//! S100 Phase-3 `/qa` triage — value-use of the vec query family calls through
//! NULL GOT slots (spine `design/arch/ownership-inference.md` §3.1/§9 triage item).
//!
//! ## RESOLVED — S101 Wave 3 (2026-07-03): all 7 guards GREEN
//!
//! The `/dev`(cranelisp-backend) fix (S101 sprint item 1, per
//! `design/backend/ownership-codegen.md` §12.7) cured the class at BOTH seams:
//! the fn-as-value wrapper now inline-lowers the vec query family via shared
//! emission cores (one source for static/wrapper/curry paths, per-site elem
//! heap-category recovery), and the auto-curry path's unknown-builtin Import
//! arm covers the family too (the distinct exit-101 `can't resolve symbol`
//! signature). The 4 S100 guards + 3 Wave-1 cat-3 guards below flipped GREEN;
//! the `vec-len` control stayed green throughout. They remain permanently as
//! regression guards — never deleted, never weakened (qa plan §7.1 step 2).
//! Ledger resolution records: `tests/plan/ledger.md` §"Sprint 100 Phase-3
//! triage" + §"Sprint 101 Wave-1 cat-3 sweep". Residual on the SAME new
//! paths: the COW copy-branch leak — `tests/vec_cow_value_use_leak.rs`
//! (FIXME 0474, intentional RED). The "RED on HEAD" notes on the tests below
//! are the historical draft-time polarity, kept as the triage narrative.
//!
//! ## Original triage verdict: REAL DEFECT (verified 2026-07-02, binary `target/debug/cranelisp`)
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

// =============================================================================
// S101 Wave-1 cat-3 sweep extension — the same NULL-slot class in THREE more
// use positions (tests/plan/s101-coverage-postmortem.md §3; ledger §"Sprint
// 101 Wave-1 cat-3 sweep"). Probed 2026-07-03 on HEAD 0b0e234:
//   - curried partial `(vec-get v)`  → Rust panic `can't resolve symbol
//     vec-get` in cranelift-jit backend.rs:345 (exit 101) — the auto-curry
//     wrapper's `primitives_inline` fallback does NOT cover the vec family
//     (confirming the /design(backend) §12.7 suspicion; it dies EARLIER than
//     the fn-as-value path, at JIT symbol resolution).
//   - returned from a fn             → SIGSEGV (NULL slot), like the HOF shape.
//   - stored in a container (ADT)    → SIGSEGV (NULL slot).
// Same root cause, same owner (/backend, sprint item 1), same flip protocol
// (qa plan §7.1). vec-set/vec-push curried share the exit-101 signature
// (probed, recorded in the post-mortem; one guard per position suffices —
// the family boundary is already pinned by the HOF trio + vec-len control).
// =============================================================================

// spec: spec/04-expressions.md §4.6.2 — auto-currying applies to primitive
// function values too: a partial application of vec-get is callable. RED on
// HEAD: Rust panic `can't resolve symbol vec-get` (exit 101) when the curry
// wrapper is JIT-compiled.
#[test]
fn vec_get_curried_partial_applies() {
    repl_prims(
        "(defn use1 [g] (g 1))\n\
         (use1 (vec-get [10 20 30]))\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 20");
}

// spec: spec/04-expressions.md §4.6.2 — a primitive returned from a function
// is callable at the call site. RED on HEAD: SIGSEGV through the NULL slot.
#[test]
fn vec_get_returned_from_fn_applies() {
    repl_prims(
        "(defn pick [] vec-get)\n\
         ((pick) [10 20 30] 1)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 20");
}

// spec: spec/04-expressions.md §4.6.2 — a primitive stored in an ADT field
// and projected back out is callable. RED on HEAD: SIGSEGV through the NULL
// slot. (Control: the same shape with `add-i64` works — cat-3 sweep probe
// `adt_stored_fn`, GREEN.)
#[test]
fn vec_get_stored_in_adt_field_applies() {
    repl_prims(
        "(deftype VHolder (VHolder [:(Fn [(Vec Int) Int] Int) vop]))\n\
         (match (VHolder vec-get) [(VHolder f) (f [10 20 30] 1)])\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 20");
}

// =============================================================================
// FIXME 0475 drain (S101 Wave 5) — RE-ANCHORED S102 (FIXME 0514/0515). These
// were "prelude names stay shadowable" pins asserting `(defn vec-get …)` is
// ACCEPTED and shadows the prelude-provided `vec-get`. The user's no-exception
// ruling (2026-07-04; /spec `a953de0`) REVERSES that: the prelude is just an
// implicit `(import [prelude [*]])`, so a module-local definition over a
// prelude-provided name (`vec-get` reaches here via `primitives-only.cl`'s
// `(export [primitives [*]])`) is the SAME compile-time error as over an
// explicit import (spec/08-modules.md §8.6.4/§8.8.1) — NO exception. The pins
// below are FLIPPED to expect REJECTION. RED against the current impl
// (`e1fe4a8`, prelude/outer-scope arm unimplemented); flip GREEN when FIXME
// 0514's prelude arm lands. Ledger: `tests/plan/ledger.md` §"Sprint 102
// name-shadowing matrix (FIXME 0514)". (The resolver's "user fn shadows
// vec-get" arm is now unreachable via a prelude-provided vec-get; a user that
// wants its OWN `vec-get` must suppress/not-load the prelude name, §8.8.3.)
// =============================================================================

// spec: spec/08-modules.md §8.6.4/§8.8.1 — a module-local definition over the
// PRELUDE-PROVIDED `vec-get` is a compile-time error (def-over-name-in-scope);
// the prelude carries no exemption. RED signal (S102 re-anchor, FIXME 0514).
#[test]
fn user_fn_over_prelude_vec_get_is_rejected() {
    let out = repl_prims(
        "(defn vec-get [v i] 42)\n\
         (vec-get [10 20 30] 1)\n",
    );
    let lower = format!("{}\n{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        lower.contains("conflict") || lower.contains("ambiguous"),
        "def-over-prelude `vec-get` MUST emit a §8.6.4 collision diagnostic;\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    // The rejected def has no effect: neither the user body (42) nor a
    // silently-shadowed result appears as a resolved value.
    assert!(
        !out.stdout.contains(":primitives/Int 42"),
        "the rejected def MUST have no effect (found user-body 42);\nstdout:\n{}",
        out.stdout
    );
}

// spec: spec/08-modules.md §8.6.4/§8.8.1 — the same def-over-prelude rejection
// holds regardless of value-position use downstream: the colliding definition
// is rejected before any HOF dispatch. RED signal (S102 re-anchor, FIXME 0514).
#[test]
fn user_fn_over_prelude_vec_get_rejected_even_with_value_use() {
    let out = repl_prims(
        "(defn vec-get [v i] 42)\n\
         (defn call-get [f v i] (f v i))\n\
         (call-get vec-get [10 20 30] 1)\n",
    );
    let lower = format!("{}\n{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        lower.contains("conflict") || lower.contains("ambiguous"),
        "def-over-prelude `vec-get` MUST be rejected before value-use;\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    assert!(
        !out.stdout.contains(":primitives/Int 42"),
        "the rejected def MUST have no effect (found user-body 42);\nstdout:\n{}",
        out.stdout
    );
}

// =============================================================================
// FIXME 0483 (S101 Phase 6a, /examples) — the NEXT boundary past the S101 fix:
// a vec NULL-slot-trio primitive used as a value through the SAME polymorphic
// HOF at TWO monomorphic instantiations SIGBUSes (exit 135), both `--run` and
// REPL. One wrapper-backed instantiation per HOF is fine (the guards above,
// GREEN since Wave 3); the crash needs ≥2 — either the same op at two element
// types or two different trio ops through one HOF. Signature smells like a
// wrapper-name/slot collision across monomorphisations (hypothesis, per the
// FIXME). Green-control matrix verified 2026-07-03 (this /qa batch): per-op
// HOFs / same-op-same-type ×2 / vec-get + user fn / `vec-len` at two element
// types — all PASS; the two-instantiation control below pins the boundary.
// Resolver: /backend — the same `fn_as_value.rs` seam as the S101 fix, per
// `design/backend/ownership-codegen.md` §12.7. Failing-not-ignored; ledger
// entry: tests/plan/ledger.md §"Sprint 101 Phase 6a/6b defect set".
// =============================================================================

// spec: spec/04-expressions.md §4.6.2 — indirect calls: the same generic HOF
// receiving vec-get as its fn argument at TWO element-type instantiations
// (Vec Int → Int, Vec String → String). Want 20 + str-len "yy" = 22.
// RED on HEAD (FIXME 0483): SIGBUS, exit 135, REPL process dies.
#[test]
fn vec_get_as_value_two_instantiations_of_one_hof_repl() {
    repl_prims(
        "(defn apply2 [f v i] (f v i))\n\
         (add-i64 (apply2 vec-get [10 20 30] 1) (str-len (apply2 vec-get [\"x\" \"yy\"] 1)))\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 22");
}

// spec: spec/04-expressions.md §4.6.2 — the same two-instantiation shape is
// mode-crossing: `--run` also SIGBUSes (exit 135). Want exit 22.
// RED on HEAD (FIXME 0483).
#[test]
fn vec_get_as_value_two_instantiations_of_one_hof_run_mode() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [*]])\n\
             (defn apply2 [f v i] (f v i))\n\
             (defn main []\n\
             \x20 (let [a (apply2 vec-get [10 20 30] 1)\n\
             \x20       s (apply2 vec-get [\"x\" \"yy\"] 1)]\n\
             \x20   (Pure (add-i64 a (str-len s)))))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(22);
}

// spec: spec/04-expressions.md §4.6.2 — second crashing shape: two DIFFERENT
// trio ops (vec-get + vec-push) through ONE generic HOF, each at a single
// instantiation. Want 20 + vec-len [10 20 99] = 23. RED on HEAD (FIXME 0483):
// SIGBUS, exit 135.
#[test]
fn vec_get_and_vec_push_as_values_through_one_hof_run_mode() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [*]])\n\
             (defn apply2 [f v i] (f v i))\n\
             (defn main []\n\
             \x20 (let [a (apply2 vec-get [10 20 30] 1)\n\
             \x20       v3 (apply2 vec-push [10 20] 99)]\n\
             \x20   (Pure (add-i64 a (vec-len v3)))))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(23);
}

// spec: spec/04-expressions.md §4.6.2 — CONTROL (GREEN on HEAD): the
// populated-slot family member `vec-len` through the SAME HOF at two element
// types works, pinning the 0483 boundary to the NULL-slot trio × ≥2
// instantiations, not the multi-instantiation wrapper mechanism itself.
#[test]
fn vec_len_as_value_two_instantiations_of_one_hof_control() {
    repl_prims(
        "(defn apply1 [f v] (f v))\n\
         (add-i64 (apply1 vec-len [10 20 30]) (apply1 vec-len [\"x\" \"yy\"]))\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 5");
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
