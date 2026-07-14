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
