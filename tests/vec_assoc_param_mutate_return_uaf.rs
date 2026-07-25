//! Repro — `vec-set`/`vec-push` on a Vec **parameter** that is then RETURNED to
//! the caller and consumed yields a freed-heap read (garbage value) / heap
//! corruption. Surfaced by `/stdlib` during S109 W1 exercising
//! `collections.vec.test/test-assoc-sets` (`(assert-eq 99 (get (assoc [1 2 3] 1
//! 99) 1))`); stash-confirmed PRE-EXISTING (fails identically on the unchanged
//! tree, independent of the S109 `mod-` change). Out of the S109 theme — this
//! RED carries across sprint close as a committed regression guard.
//!
//! ## Reduction (bottomed at a 2-line free-standing shape)
//!
//! The stdlib `assoc`/`get` are ordinary wrappers over the primitives
//! (`(defn assoc [v :Int i x] (vec-set v i x))`, `(defn get [v :Int i] (vec-get
//! v i))`). Stripped to primitives (no stdlib, per root `CLAUDE.md`
//! §Stdlib-separation), the defect is a single user function that calls an
//! IN-PLACE vec op (`vec-set` / `vec-push`) on its Vec parameter and returns the
//! result; the caller then reads an element of the returned Vec:
//!
//! ```text
//! (defn assoc [v i x] (vec-set v i x))
//! (vec-get (assoc [1 2 3] 1 99) 1)          ; expected :primitives/Int 99
//! ```
//!
//! ## Discriminator (what is and is NOT load-bearing)
//!
//! - An **identity** function that returns its Vec param unchanged
//!   (`(defn idv [v] v)` then `(vec-get (idv [1 2 3]) 1)`) is CORRECT (2) — so
//!   "a Vec through a user-fn param" alone is fine.
//! - `vec-set`/`vec-push` on a **local literal** (no param:
//!   `(defn f [] (vec-set [1 2 3] 1 99))`) is CORRECT (99) — so the in-place op
//!   alone is fine.
//! - The bug is the COMBINATION: an in-place `vec-set`/`vec-push` on a Vec that
//!   arrived as a **parameter**, RETURNED to the caller and consumed.
//! - The `:Int` annotation and the `get` wrapper are NOT load-bearing (dropped).
//!
//! ## Mechanism (RC trace, `CRANELISP_RC_TRACE=1`)
//!
//! The Vec backing is allocated once (`alloc rc=1`) and freed once
//! (`free rc=0`) — but the free happens BEFORE the caller's `vec-get` consumes
//! it: a **premature free**. `--run` returns a nondeterministic garbage exit
//! code (freed-heap read, truncated mod 256); the REPL prints the full garbage
//! i64; `--link` deterministically ABORTS (SIGABRT, glibc heap-header integrity
//! trip — the marshaling/heap-corruption signature of `tests/CLAUDE.md`
//! §"Diagnostic env vars").
//!
//! defect: class=rc-miscount locus=crates/cranelisp-backend (premature free of a Vec returned from a user fn whose param it aliases — the in-place vec-set/vec-push op releases the backing before the caller's use; manifests as UAF/garbage + --link SIGABRT) found=S109 owner=/backend
//!
//! Attribution is evidenced (RC-trace premature free → backend RC codegen for
//! the param-aliased-return Vec) but candidate — `/qa` re-attributes if backend
//! triage disputes; the `uaf` manifestation is noted for completeness. Sibling
//! of `tests/vec_cow_value_use_leak.rs` (the COW copy-branch LEAK) but the
//! OPPOSITE polarity: this is an under-count (premature free), not a leak.
//!
//! Failing-not-ignored: the durable record + regression guard; flips GREEN when
//! `/backend` fixes the RC discipline. `--run`'s exit code is truncated (mod
//! 256) so a specific-exit assertion there would be non-deterministic — the two
//! reliable deterministic surfaces are the REPL (full value) and `--link` (the
//! deterministic abort), covered below.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant, run_through_all_modes};

const ASSOC_PARAM_RETURN: &str = "(defn assoc [v i x] (vec-set v i x))\n";

/// Parse the integer rendered by the last `:primitives/Int N` line.
fn last_int_value(stdout: &str) -> i64 {
    let line = stdout
        .lines()
        .rev()
        .find(|l| l.contains(":primitives/Int"))
        .unwrap_or_else(|| panic!("no `:primitives/Int` value line in:\n{stdout}"));
    line.rsplit(":primitives/Int ")
        .next()
        .and_then(|tail| tail.trim().split_whitespace().next())
        .and_then(|tok| tok.parse::<i64>().ok())
        .unwrap_or_else(|| panic!("could not parse the Int value from line: {line:?}"))
}

// spec: spec/12-runtime.md §12.1 — value representation & reference counting: a
// Vec value returned from a function (after an in-place `vec-set` on its
// parameter) MUST remain live for the caller's use. `(vec-get (assoc [1 2 3] 1
// 99) 1)` MUST yield 99; today it reads freed heap and returns garbage (RED).
#[test]
fn vec_set_on_param_returned_and_consumed_repl_yields_correct_value() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(&format!(
            "{ASSOC_PARAM_RETURN}(vec-get (assoc [1 2 3] 1 99) 1)\n"
        ))
        .output();
    let n = last_int_value(&out.stdout);
    assert_eq!(
        n, 99,
        "vec-set on a Vec PARAM, returned and consumed by the caller, MUST yield \
         99 (assoc semantics); got garbage {n} — the returned Vec's backing is \
         freed before `vec-get` reads it (rc-miscount premature-free). \
         stdout=\n{}",
        out.stdout
    );
}

// spec: spec/12-runtime.md §12.1 — the same shape under `--link`: the linked
// binary MUST run to a clean exit (`main` returns `(Pure 99)` → exit 99). Today
// the premature free corrupts the heap and the binary deterministically ABORTS
// (SIGABRT) — the `--link` face of the same defect. A mode divergence in symptom
// (REPL garbage value vs `--link` crash) is itself part of the record.
#[test]
fn vec_set_on_param_returned_link_does_not_corrupt_heap() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(&format!(
            "{ASSOC_PARAM_RETURN}(defn main [] (Pure (vec-get (assoc [1 2 3] 1 99) 1)))\n"
        ))
        .output()
        .assert_exit(99);
}

// =============================================================================
// SIBLING SHAPES — the S111 carry trigger (let-wrapped + match-arm)
//
// The direct-body shape above was FIXED at S110 W2 (a backend recognizer,
// `return_cow_source_in_scope`). The W2 review (finding R-W2-1,
// `sprints/SPRINT.md` §"/review (W2)") probed that fix and found it NARROW: two
// 2-line siblings of the same `vec-set`-on-a-param-then-returned shape still
// UAF, identically to VA-1/VA-2, because the fix compensates at exactly ONE body
// shape while the REAL leg — the enclosing fn's ownership SUMMARY — still
// declares a false `result == Fresh` for the COW primitive.
//
// Mechanism (evidenced, both siblings GREEN under `CRANELISP_NO_OWNERSHIP=1`):
// the COW primitives (`vec-set`/`vec-push`) carry no reachable ownership
// summary, so typecheck defaults a summary-less callee's result to
// `ResultMode::Fresh` (the `Fresh`-on-absence default at
// `crates/cranelisp-typecheck/src/ownership/transfer.rs:590`). A `Fresh` result
// claim is FALSE on the rc==1 in-place COW arm (the result dynamically IS
// param 0's own reference). The backend B3.2 return-protect elision consumes
// that false `Fresh`, elides `protect_return_value`, and `pop_scope_with_cleanup`
// decs `v` — freeing the returned alias before the caller's `vec-get` reads it.
//
// Root cause RULED by `/arch`: `design/arch/ownership-inference.md` §3.7 — the
// cure is `ResultMode::MayAliasOf(k)` + truthful COW declarations +
// prelude-fallback-aware ownership envs. CARRIED to S111 as ONE coordinated
// change-set; these two sibling repros are the failing-not-ignored TRIGGER +
// regression guard (per the failing-test rule, no numbered FIXME — the test is
// the record). `/qa` matrix gap tracked at FIXME 0623.
//
// Faces mirror the direct-shape pair: REPL (full garbage i64) + `--link` (the
// deterministic `corrupted double-linked list` SIGABRT). `--run` is omitted for
// the same reason as VA-1/VA-2 — its exit code is truncated mod 256, so a
// specific-exit assertion there is non-deterministic.
//
// Both siblings flip GREEN when the S111 `MayAliasOf` summary fix lands.
// =============================================================================

// Sibling 1 — the COW op is bound in a `let` and the binding returned:
// `(defn f [v i x] (let [r (vec-set v i x)] r))`. `r` aliases the in-place
// result; scope-exit decs `v` and frees the returned alias.
const LET_WRAPPED_PARAM_RETURN: &str = "(defn f [v i x] (let [r (vec-set v i x)] r))\n";

// Sibling 2 — the COW op is the body of a single match arm:
// `(defn m [v i x] (match i [_ (vec-set v i x)]))`. The arm's value is the
// in-place alias returned from the fn.
const MATCH_ARM_PARAM_RETURN: &str = "(defn m [v i x] (match i [_ (vec-set v i x)]))\n";

// spec: spec/12-runtime.md §12.1 — value representation & reference counting:
// the let-bound Vec result (after an in-place `vec-set` on the parameter) MUST
// remain live for the caller's use. `(vec-get (f [1 2 3] 1 99) 1)` MUST yield
// 99; today the return-protect elision (fed by the false-Fresh summary) frees
// the returned alias and `vec-get` reads freed heap → garbage (RED).
// defect: class=rc-miscount locus=crates/cranelisp-typecheck/src/ownership/transfer.rs:590 found=S110 owner=/dev
#[test]
fn vec_set_let_wrapped_param_returned_and_consumed_repl_yields_correct_value() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(&format!(
            "{LET_WRAPPED_PARAM_RETURN}(vec-get (f [1 2 3] 1 99) 1)\n"
        ))
        .output();
    let n = last_int_value(&out.stdout);
    assert_eq!(
        n, 99,
        "vec-set on a Vec PARAM, let-bound and returned, consumed by the caller, \
         MUST yield 99 (assoc semantics); got garbage {n} — the returned Vec's \
         backing is freed before `vec-get` reads it. The enclosing fn's ownership \
         summary declares a false `result == Fresh` for the COW primitive \
         (transfer.rs:590 Fresh-on-absence), so the B3.2 return-protect elision \
         frees the returned alias at scope exit (ownership-inference.md §3.7; \
         S111 carry). stdout=\n{}",
        out.stdout
    );
}

// spec: spec/12-runtime.md §12.1 — the let-wrapped shape under `--link`: the
// linked binary MUST run to a clean exit (`main` returns `(Pure 99)` → exit 99).
// Today the premature free corrupts the heap and the binary deterministically
// ABORTS (`corrupted double-linked list`, SIGABRT) — the `--link` face of the
// same S111-carried defect.
// defect: class=rc-miscount locus=crates/cranelisp-typecheck/src/ownership/transfer.rs:590 found=S110 owner=/dev
#[test]
fn vec_set_let_wrapped_param_returned_link_does_not_corrupt_heap() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(&format!(
            "{LET_WRAPPED_PARAM_RETURN}(defn main [] (Pure (vec-get (f [1 2 3] 1 99) 1)))\n"
        ))
        .output()
        .assert_exit(99);
}

// spec: spec/12-runtime.md §12.1 — value representation & reference counting:
// the match-arm Vec result (after an in-place `vec-set` on the parameter) MUST
// remain live for the caller's use. `(vec-get (m [1 2 3] 1 99) 1)` MUST yield
// 99; today the return-protect elision frees the returned alias and `vec-get`
// reads freed heap → garbage (RED).
// defect: class=rc-miscount locus=crates/cranelisp-typecheck/src/ownership/transfer.rs:590 found=S110 owner=/dev
#[test]
fn vec_set_match_arm_param_returned_and_consumed_repl_yields_correct_value() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(&format!(
            "{MATCH_ARM_PARAM_RETURN}(vec-get (m [1 2 3] 1 99) 1)\n"
        ))
        .output();
    let n = last_int_value(&out.stdout);
    assert_eq!(
        n, 99,
        "vec-set on a Vec PARAM inside a match arm, returned and consumed by the \
         caller, MUST yield 99 (assoc semantics); got garbage {n} — the returned \
         Vec's backing is freed before `vec-get` reads it. Same false-`Fresh` \
         ownership-summary root as the let-wrapped sibling \
         (ownership-inference.md §3.7; S111 carry). stdout=\n{}",
        out.stdout
    );
}

// spec: spec/12-runtime.md §12.1 — the match-arm shape under `--link`: the
// linked binary MUST run to a clean exit (`main` returns `(Pure 99)` → exit 99).
// Today the premature free deterministically ABORTS (`corrupted double-linked
// list`, SIGABRT) — the `--link` face of the same S111-carried defect.
// defect: class=rc-miscount locus=crates/cranelisp-typecheck/src/ownership/transfer.rs:590 found=S110 owner=/dev
#[test]
fn vec_set_match_arm_param_returned_link_does_not_corrupt_heap() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(&format!(
            "{MATCH_ARM_PARAM_RETURN}(defn main [] (Pure (vec-get (m [1 2 3] 1 99) 1)))\n"
        ))
        .output()
        .assert_exit(99);
}

// =============================================================================
// S111 §A.2 — the body-shape × branch × face MATRIX (new cells CW-5..CW-11).
//
// The COW-in-return-position invariant must hold UNIFORMLY across the
// body-shape family (`ownership-inference.md` §3.7; the standing
// coverage-by-definition-variants category). The direct-body cell is fixed
// (S110) and the let/match cells RED above; these pin the remaining
// load-bearing cells (if-branch, chained, vec-push op-uniformity) + the
// GREEN safe controls (chained, lambda-captured) + the copy-branch negatives
// (shared source: correct value AND source preserved). All flip at the ONE
// schema-20 §3.7 change-set (CS-5). `// spec: spec/12-runtime.md §12.1`.
// =============================================================================

// CW-5 — if-branch × rc==1 × all modes. FINDING (verified against HEAD
// 2026-07-17, S111 Phase-5): the if-branch shape is ALREADY GREEN — the S110
// `return_cow_source_in_scope` recognizer covers a COW op in an if-branch
// return position (unlike let/match, which it misses — CW-1..4/CW-7/CW-10).
// So this is a GREEN CONTROL documenting the recognizer's coverage boundary
// (if-branch: yes; let/match/chained: no); it must STAY green through the §3.7
// change-set (CS-5), which subsumes all shapes uniformly.
// spec: spec/12-runtime.md §12.1 — value representation & reference counting.
#[test]
fn vec_set_if_branch_param_returned_yields_correct_value() {
    run_through_all_modes(
        "(defn f [v i x] (if (lt-i64 i 0) v (vec-set v i x)))\n\
         (defn main [] (Pure (vec-get (f [1 2 3] 1 99) 1)))\n",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(99);
}

// CW-6 — chained COW × rc==1 × all modes. FINDING (verified against HEAD
// 2026-07-17, S111 Phase-5): CONTRARY to the plan's "probed SAFE at W2", the
// chained shape is RED — the inner `(vec-push v 4)` mutates the param `v` in
// place and returns an alias that the outer `(vec-push … 5)` consumes; the S110
// recognizer only matches a return whose DIRECT source is a param, not a nested
// COW, so `g`'s false-`Fresh` summary elides the return protect → UAF (observed
// garbage 14/104 under `--run`; `corrupted double-linked list` under `--link`).
// `[1 2 3]` push 4 push 5 = `[1 2 3 4 5]`; index 4 = 5. RED at HEAD; flips GREEN
// at the §3.7 MayAliasOf change-set (CS-5), which covers all shapes uniformly.
// spec: spec/12-runtime.md §12.1 — value representation & reference counting.
// defect: class=rc-miscount locus=crates/cranelisp-typecheck/src/ownership/transfer.rs:590 found=S110 owner=/dev
#[test]
fn vec_push_chained_cow_returns_correct_vec() {
    run_through_all_modes(
        "(defn g [v] (vec-push (vec-push v 4) 5))\n\
         (defn main [] (Pure (vec-get (g [1 2 3]) 4)))\n",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(5);
}

// CW-7 — vec-push × let-wrapped × REPL + `--link` (op-uniformity twin of
// CW-1/CW-2). The SECOND truthful-COW primitive (`vec-push`) must not grow its
// own codepath: the let-wrapped-return shape UAFs identically to `vec-set`
// because the same false-`Fresh` summary elides the return protect. `[1 2 3]`
// push 99 → index 3 = 99.
const LET_WRAPPED_PUSH_RETURN: &str = "(defn fp [v x] (let [r (vec-push v x)] r))\n";

// NOTE (S111 Phase-5): the REPL face of the vec-push let-wrapped UAF is
// OMITTED deliberately. Unlike `vec-set` (CW-1/CW-3, whose REPL garbage
// manifests reliably in the harness), the `vec-push` grow-branch allocates a
// fresh backing, so the freed slot is NOT reliably reused before the caller's
// `vec-get` reads it — the REPL read returns intact `99` (a timing-dependent
// FALSE GREEN, forbidden per `tests/CLAUDE.md` §"Forbidden dispositions").
// The deterministic guard is the `--link` face below (glibc heap-integrity
// abort). Op-uniformity with `vec-set` is thereby proven without a flaky test.

// spec: spec/12-runtime.md §12.1 — the vec-push let-wrapped shape under `--link`.
// defect: class=rc-miscount locus=crates/cranelisp-typecheck/src/ownership/transfer.rs:590 found=S110 owner=/dev
#[test]
fn vec_push_let_wrapped_param_returned_link_does_not_corrupt_heap() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(&format!(
            "{LET_WRAPPED_PUSH_RETURN}(defn main [] (Pure (vec-get (fp [1 2 3] 99) 3)))\n"
        ))
        .output()
        .assert_exit(99);
}

// CW-8 — shared-source (rc>1) × let-wrapped × REPL (copy-branch negative).
// The source `v` is read AFTER the COW, so rc>1 at the check → the copy branch
// runs → COW value semantics MUST hold: the result reads the WRITTEN element
// (r[0]=9) AND the source still reads its ORIGINAL element (v[0]=1) → 9+1=10.
// This is the "wrong thing absent" negative — a fix that over-shares the copy
// (source mutated) shows v[0]=9 → 18, or a UAF shows garbage. GREEN today;
// must stay GREEN through the §3.7 fix.
// spec: spec/12-runtime.md §12.1 — value representation & reference counting.
#[test]
fn vec_set_let_wrapped_shared_source_copies_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn use1 [v] (let [r (vec-set v 0 9)] (add-i64 (vec-get r 0) (vec-get v 0))))\n\
             (use1 [1 2 3])\n",
        )
        .output();
    let n = last_int_value(&out.stdout);
    assert_eq!(
        n, 10,
        "shared-source let-wrapped COW MUST copy: result element 9 + source \
         ORIGINAL element 1 = 10; got {n} (18 ⇒ source wrongly mutated; garbage \
         ⇒ UAF). stdout=\n{}",
        out.stdout
    );
}

// CW-9 — shared-source (rc>1) × match-arm × REPL (copy-branch negative; twin
// of CW-8 across the match-arm body shape).
// spec: spec/12-runtime.md §12.1 — value representation & reference counting.
#[test]
fn vec_set_match_arm_shared_source_copies_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn use1m [v] (add-i64 (vec-get (match 0 [_ (vec-set v 0 9)]) 0) (vec-get v 0)))\n\
             (use1m [1 2 3])\n",
        )
        .output();
    let n = last_int_value(&out.stdout);
    assert_eq!(
        n, 10,
        "shared-source match-arm COW MUST copy: result 9 + source ORIGINAL 1 = \
         10; got {n}. stdout=\n{}",
        out.stdout
    );
}

// CW-10 — the `--run` (+ cached) face of the RED let-wrapped shape. The
// committed CW-1/CW-2 pair covers only REPL + `--link`; the §A.2 matrix names
// three faces. `run_through_all_modes` adds `--run` fresh/cached and the REPL
// cached path. RED at HEAD (the `--link` legs SIGABRT → observed None); flips
// GREEN at the §3.7 change-set.
// spec: spec/12-runtime.md §12.1 — value representation & reference counting.
// defect: class=rc-miscount locus=crates/cranelisp-typecheck/src/ownership/transfer.rs:590 found=S110 owner=/dev
#[test]
fn vec_set_let_wrapped_param_returned_all_modes_yield_correct_value() {
    run_through_all_modes(
        "(defn f [v i x] (let [r (vec-set v i x)] r))\n\
         (defn main [] (Pure (vec-get (f [1 2 3] 1 99) 1)))\n",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(99);
}

// CW-11 — lambda-captured source (GREEN control; probed SAFE at the W2
// review). The returned closure CAPTURES `v` (the capture holds a reference),
// so at the `vec-set` the source is rc>1 → the copy branch runs → no premature
// free. `((mk [1 2 3]) 1 99)` writes index 1 → 99. Must stay GREEN through the
// fix (a widening that treats the captured source as uniquely-owned would
// re-open the free).
// spec: spec/12-runtime.md §12.1 — value representation & reference counting.
#[test]
fn vec_set_lambda_captured_source_safe() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn mk [v] (fn [i x] (vec-set v i x)))\n\
             (vec-get ((mk [1 2 3]) 1 99) 1)\n",
        )
        .output();
    let n = last_int_value(&out.stdout);
    assert_eq!(
        n, 99,
        "lambda-captured source COW is SAFE (captured ⇒ rc>1 ⇒ copy branch): \
         MUST yield 99; got {n}. stdout=\n{}",
        out.stdout
    );
}
