//! Repro — the FALSE-`Fresh` provenance-laundering RESIDUAL class (S111 CS-5
//! adversarial `/review`; `design/arch/fixmes/0641-false-fresh-container-element-and-capture-provenance-residual.md`).
//!
//! ## What CS-5 closed, and what it did NOT
//!
//! The S111 CS-5 centrepiece (`ownership-inference.md` §3.7, `e99535e4`) made the
//! vec-set/vec-push COW facts truthful+reachable and closed the
//! `vec_assoc_param_mutate_return_uaf` family (direct/let/match body shapes). Its
//! adversarial review then found the SAME false-`Fresh` → protect-elided → UAF
//! class survives via a mechanism §3.7 + the 0623 body-shape matrix do NOT cover:
//! the interprocedural ownership WALK drops alias provenance at container
//! construction/projection and at capture. All four vectors below are
//! PRE-EXISTING (byte-stable across CS-5, NOT regressions) and memory-unsafe.
//!
//! ## Mechanism (per FIXME 0641, `CRANELISP_OWNERSHIP_TRACE=1`)
//!
//! The walk builds a `VecLit` with origin `Fresh` (the literal container IS
//! fresh) but LOSES that an ELEMENT origin reaches a param; a projection-out
//! (`vec-get`'s `ProjectionOf(0)`) then roots at the fresh container → the body
//! origin resolves `Fresh` → `origin_to_result_mode` publishes `Fresh` →
//! `return_is_fresh_by_summary` (`crates/cranelisp-backend/src/compiler/fn_compiler.rs:1736`)
//! elides `protect_return_value` → scope-exit `dec` frees the returned alias
//! before the caller reads it. Capture (I-1) and fresh-container-holding-a-
//! COW-aliased-element (I-2) are the same family one axis over.
//!
//! ## Determinism handling (per `tests/CLAUDE.md` §"Forbidden dispositions" —
//! no flaky, no garbage-value assertion)
//!
//! For EVERY vector the DETERMINISTIC signal pinned is the `--link` face: the
//! default-compiled binary deterministically ABORTS (`corrupted double-linked
//! list`, glibc heap-header integrity trip → SIGABRT, exit code None). Each
//! `--link` test asserts the CORRECT clean exit (`main` returns `(Pure N)` →
//! exit N); the SIGABRT (code None ≠ N) is a reliable RED that flips GREEN when
//! the fix lands. Verified deterministic 6/6 runs per vector (S111 Phase-5).
//!
//! The REPL face asserts the CORRECT value (which currently fails): the freed-
//! heap read returns a large pointer-shaped word, never the small correct value
//! (verified 5+ runs/vector) — a reliable RED, NOT a garbage-value assertion.
//! The `--run` face is OMITTED for every vector: its exit code is a garbage word
//! truncated mod 256 (observed spread e.g. B-1 137/85/128, B-2 208/100/255) —
//! nondeterministic, so no `--run` assertion is committed (narrated only).
//!
//! ## Toggle-off (`CRANELISP_NO_OWNERSHIP=1`, the R7 differential oracle)
//!
//! - B-1 is CURED toggle-off (clean exit 2) — a PURE false-`Fresh` provenance
//!   defect; flips GREEN on the FIXME-0641 ownership increment alone.
//! - B-2/I-1/I-2 also FAIL toggle-off (B-2 keeps the SIGABRT; I-1/I-2 return a
//!   garbage exit) — an accounting/backend factor INDEPENDENT of the ownership
//!   analysis rides alongside the provenance miss (FIXME 0641: B-2 names a 2nd
//!   stacked crash needing `/qa` attribution + a backend fix; I-2 is explicitly
//!   "garbage both toggle states"). These flip GREEN when BOTH the ownership
//!   increment AND the accompanying accounting/backend fix land — the repros are
//!   the durable record + trigger for the whole class regardless.
//!
//! Per the failing-test rule (root `CLAUDE.md` §"Usability Findings and
//! Defects"): these committed failing-not-ignored repros ARE the record + the
//! trigger; no numbered FIXME accompanies them. The design EXTENSION (add the
//! container-element/capture provenance axis to the §15 model + the 0623 matrix
//! + correct the CS-5 rustdoc over-claim) is tracked separately in FIXME 0641.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

/// Parse the integer rendered by the last `:primitives/Int N` REPL line.
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

// =============================================================================
// B-1 — container-element provenance laundering (the clearest; PRIORITY).
//
// `(defn f [v] (vec-get [v] 0))` returns its own param `v` — but VIA a fresh
// container `[v]` projected at index 0. No COW op is needed: the walk builds
// `VecLit [v]` origin `Fresh`, loses that element 0 reaches param `v`, so the
// `ProjectionOf(0)` roots at the fresh container → false `result=Fresh` → the
// returned alias (`v`) is freed at f's scope exit. `(vec-get (f [1 2 3]) 1)` is
// element 1 of `[1 2 3]` = 2. Toggle-off CURES it (clean 2): pure false-`Fresh`.
// =============================================================================

const B1_F: &str = "(defn f [v] (vec-get [v] 0))\n";

// spec: spec/12-runtime.md §12.1 — value representation & reference counting: a
// param returned via a fresh-container projection MUST remain live for the
// caller. `(vec-get (f [1 2 3]) 1)` MUST yield 2; today the false-`Fresh`
// summary frees the returned alias and `vec-get` reads freed heap → a
// pointer-shaped garbage word (RED).
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/transfer.rs::VecLit-element-store-ProjectionOf-composition found=S111 owner=/dev
#[test]
fn container_element_provenance_returned_param_repl_yields_correct_value() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(&format!("{B1_F}(vec-get (f [1 2 3]) 1)\n"))
        .output();
    let n = last_int_value(&out.stdout);
    assert_eq!(
        n, 2,
        "a param returned via a fresh-container projection `(vec-get [v] 0)` MUST \
         stay live: `(vec-get (f [1 2 3]) 1)` MUST yield 2; got a pointer-shaped \
         garbage word {n} — the ownership walk drops the element's provenance at \
         `VecLit` construction, publishes a false `result=Fresh`, and the return \
         protect is elided so the alias is freed before the caller reads it \
         (FIXME 0641 B-1). stdout=\n{}",
        out.stdout
    );
}

// spec: spec/12-runtime.md §12.1 — the `--link` face (the DETERMINISTIC signal):
// the linked binary MUST run to a clean exit (`main` returns `(Pure 2)` → exit
// 2). Today the premature free corrupts the heap and the binary
// deterministically ABORTS (`corrupted double-linked list`, SIGABRT; 6/6 runs).
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/transfer.rs::VecLit-element-store-ProjectionOf-composition found=S111 owner=/dev
#[test]
fn container_element_provenance_returned_param_link_does_not_corrupt_heap() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(&format!(
            "{B1_F}(defn main [] (Pure (vec-get (f [1 2 3]) 1)))\n"
        ))
        .output()
        .assert_exit(2);
}

// =============================================================================
// B-2 — match-scrutinee var-pattern publishes an UNCONDITIONAL claim from a
// CONDITIONAL (COW `MayParam`) origin.
//
// `(defn f [v] (match (vec-set v 1 99) [r r]))`: a var-pattern binds the whole
// COW scrutinee, yet the walk publishes UNCONDITIONAL `ProjectionOf(0)` (§3.7
// reservation clause violated one level up from `origin_to_result_mode`).
// `(vec-set [1 2 3] 1 99)` = `[1 99 3]`; `(vec-get (f [1 2 3]) 1)` = 99.
//
// NOTE: a SECOND, ownership-INDEPENDENT crash is stacked under this scrutinee/COW
// shape — it fails toggle-off too (`--link` keeps the SIGABRT; `--run` stays
// garbage). Per FIXME 0641 that stacked crash needs `/qa` attribution + a backend
// fix; this repro flips GREEN only when BOTH land. Deterministic face: `--link`.
// =============================================================================

const B2_F: &str = "(defn f [v] (match (vec-set v 1 99) [r r]))\n";

// spec: spec/12-runtime.md §12.1 — a match-var-bound COW result MUST stay live
// for the caller. `(vec-get (f [1 2 3]) 1)` MUST yield 99; today the
// unconditional `ProjectionOf(0)` claim (+ the stacked backend crash) yields a
// pointer-shaped garbage word (RED).
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/transfer.rs::match-var-pattern-unconditional-ProjectionOf found=S111 owner=/dev
#[test]
fn match_scrutinee_cow_var_pattern_repl_yields_correct_value() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(&format!("{B2_F}(vec-get (f [1 2 3]) 1)\n"))
        .output();
    let n = last_int_value(&out.stdout);
    assert_eq!(
        n, 99,
        "a match-var-bound COW result MUST stay live: `(vec-get (f [1 2 3]) 1)` \
         MUST yield 99; got garbage {n} — the walk publishes an UNCONDITIONAL \
         `ProjectionOf(0)` from a conditional COW origin, and a stacked \
         ownership-independent backend crash rides alongside (FIXME 0641 B-2). \
         stdout=\n{}",
        out.stdout
    );
}

// spec: spec/12-runtime.md §12.1 — the `--link` face (the DETERMINISTIC signal):
// `main` returns `(Pure 99)` → exit 99. Today the shape deterministically ABORTS
// (`corrupted double-linked list`, SIGABRT; 6/6 runs, INCLUDING toggle-off — the
// stacked backend crash).
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/transfer.rs::match-var-pattern-unconditional-ProjectionOf found=S111 owner=/dev
#[test]
fn match_scrutinee_cow_var_pattern_link_does_not_corrupt_heap() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(&format!(
            "{B2_F}(defn main [] (Pure (vec-get (f [1 2 3]) 1)))\n"
        ))
        .output()
        .assert_exit(99);
}

// =============================================================================
// I-1 — capture of a let-bound param alias.
//
// `(defn mk [v] (let [r v] (fn [] (vec-get r 1))))`: the returned closure
// captures `r`, a let-bound alias of param `v`. Capturing the param DIRECTLY is
// correct; the let-bound alias launders capture-accounting so the backing is
// freed once `mk` returns, and the later closure call reads freed heap.
// `((mk [1 2 3]))` reads `(vec-get [1 2 3] 1)` = 2. Fails toggle-off too
// (independent capture-accounting factor); deterministic face: `--link`.
//
// RE-ATTRIBUTION (FIXME 0669 verdict, /qa 2026-07-20; s114-test-plan §1): this
// capture face JOINS the 0668 backend consume-seam family. It crashes under
// `CRANELISP_NO_OWNERSHIP=1` too, and post-R14 toggle-off consults no
// `transfer.rs` fact — a crash that survives analysis-off cannot be owned by the
// analysis. Structurally it is cell G's let-bind alias (`(let [r v] …)` binds a
// `Var` to a `Var` without counting; both scope-dec) with CLOSURE CAPTURE as the
// consume position instead of the vec-lit store — an enumerated position in the
// 0668 consume-position × operand-provenance contract. The `// defect:` locus
// below is re-pointed to the backend consume seam; the flip trigger is the 0668
// consume-contract /dev change-set (Track B). Track A makes NO transfer.rs
// capture-provenance change this sprint. Re-attribution rider: if the analysis-ON
// face survives the backend fix while G/F/B flip, a residual typecheck provenance
// face re-attributes to typecheck THEN (backend fix = the discriminating
// experiment).
// =============================================================================

const I1_MK: &str = "(defn mk [v] (let [r v] (fn [] (vec-get r 1))))\n";

// spec: spec/12-runtime.md §12.1 — a closure capturing a let-bound param alias
// MUST keep the backing live past the defining fn's return. `((mk [1 2 3]))`
// MUST yield 2; today the capture-accounting laundering frees the backing and
// the closure call reads freed heap → a pointer-shaped garbage word (RED).
// defect: class=uaf locus=crates/cranelisp-backend let-bind-alias / closure-capture consume seam (FIXME 0668; 0669 re-attribution) found=S111 owner=/dev
#[test]
fn capture_let_bound_param_alias_repl_yields_correct_value() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(&format!("{I1_MK}((mk [1 2 3]))\n"))
        .output();
    let n = last_int_value(&out.stdout);
    assert_eq!(
        n, 2,
        "a closure capturing a let-bound param alias MUST keep the backing live: \
         `((mk [1 2 3]))` MUST yield 2; got garbage {n} — the let-bound alias \
         launders capture-accounting so the backing is freed once `mk` returns \
         (FIXME 0641 I-1). stdout=\n{}",
        out.stdout
    );
}

// spec: spec/12-runtime.md §12.1 — the `--link` face (the DETERMINISTIC signal):
// `main` returns `(Pure 2)` → exit 2. Today the shape deterministically ABORTS
// (`corrupted double-linked list`, SIGABRT; 6/6 runs).
// defect: class=uaf locus=crates/cranelisp-backend let-bind-alias / closure-capture consume seam (FIXME 0668; 0669 re-attribution) found=S111 owner=/dev
#[test]
fn capture_let_bound_param_alias_link_does_not_corrupt_heap() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(&format!("{I1_MK}(defn main [] (Pure ((mk [1 2 3]))))\n"))
        .output()
        .assert_exit(2);
}

// =============================================================================
// I-2 — fresh container holding a COW-aliased element, returned.
//
// `(defn f [v] [(vec-set v 0 9)])`: the fresh container `[...]` holds a COW
// result that aliases param `v`; element-store accounting drops the alias, so
// the returned container's element is freed. `f [1 2 3]` = `[[9 2 3]]`;
// projecting twice `(vec-get (vec-get (f [1 2 3]) 0) 0)` = 9. FIXME 0641: garbage
// BOTH toggle states (element-store accounting, ownership-independent factor);
// deterministic face: `--link`.
// =============================================================================

const I2_F: &str = "(defn f [v] [(vec-set v 0 9)])\n";

// spec: spec/12-runtime.md §12.1 — a fresh container holding a COW-aliased
// element MUST keep that element live for the caller. `(vec-get (vec-get (f [1 2
// 3]) 0) 0)` MUST yield 9; today element-store accounting drops the alias, the
// element is freed, and the projection reads freed heap → a pointer-shaped
// garbage word (RED).
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/transfer.rs::VecLit-element-store-holding-COW-alias found=S111 owner=/dev
#[test]
fn fresh_container_holding_cow_aliased_element_repl_yields_correct_value() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(&format!("{I2_F}(vec-get (vec-get (f [1 2 3]) 0) 0)\n"))
        .output();
    let n = last_int_value(&out.stdout);
    assert_eq!(
        n, 9,
        "a fresh container holding a COW-aliased element MUST keep it live: \
         `(vec-get (vec-get (f [1 2 3]) 0) 0)` MUST yield 9; got garbage {n} — \
         element-store accounting drops the alias so the returned container's \
         element is freed (FIXME 0641 I-2). stdout=\n{}",
        out.stdout
    );
}

// spec: spec/12-runtime.md §12.1 — the `--link` face (the DETERMINISTIC signal):
// `main` returns `(Pure 9)` → exit 9. Today the shape deterministically ABORTS
// (`corrupted double-linked list`, SIGABRT; 6/6 runs).
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/transfer.rs::VecLit-element-store-holding-COW-alias found=S111 owner=/dev
#[test]
fn fresh_container_holding_cow_aliased_element_link_does_not_corrupt_heap() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(&format!(
            "{I2_F}(defn main [] (Pure (vec-get (vec-get (f [1 2 3]) 0) 0)))\n"
        ))
        .output()
        .assert_exit(9);
}
