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

use helpers::e2e::{Cranelisp, PreludeVariant};

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
        .stdin(&format!("{ASSOC_PARAM_RETURN}(vec-get (assoc [1 2 3] 1 99) 1)\n"))
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
