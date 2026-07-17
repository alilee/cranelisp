// multi_arity_clause_param_51_2.rs — §5.1.2 clause-param independence repro
// matrix (Sprint 111 Phase 5).
//
// Covers `spec/05-definitions.md §5.1.2` — "Each variant is type-checked
// independently. … each variant MUST carry its own annotations wherever
// inference cannot pin its parameters from that variant's own body. A variant
// whose parameters stay polymorphic after checking its own body is an
// ambiguous-type compile-time error."
//
// This file is the durable record for two coupled facts:
//
//   1. GREEN regression guards (rp4, rp2) — CS-4.1 CLOSED the B-1 memory-safety
//      wrong-accept (a clause param acquiring its sibling's concrete types via a
//      delegating self-call / body ascription). These two vectors REJECT today;
//      the guards fail if that fix ever regresses. Before this file there was NO
//      guard on the two closed vectors (`grep rp2|rp4 tests/` was empty).
//
//   2. RED defect guards (rp15, rp19, lf1, lf2) — BLOCKER B-2, still OPEN. A
//      LEAF-body clause (bare `Var` or a literal body) escapes the §5.1.2
//      param-pinned scan entirely: `find_ambiguous_value_position` verdicts only
//      CHILD positions (`for_each_child_expr`), so a clause whose whole body is a
//      leaf has no child to scan and the unpinned param is never caught. These
//      defns WRONG-ACCEPT today (publish a scheme with free-var params); §5.1.2
//      requires rejection. The guards assert rejection, so they are RED now and
//      flip GREEN when CS-4.2 (the direct-param-verdict structural fix, /dev
//      typecheck) lands. CS-4.2 is CARRIED (coupled to the pending I-C normative
//      ruling on whether multi-arity clause-param polymorphism is legal); these
//      failing tests are the record + trigger — no numbered FIXME.
//
// REPL/`--run` divergence note (per tests/CLAUDE.md): the DEFN-level wrong-accept
// happens in ALL modes (lf1/lf2 accept under `--run` too). The memory-UNSAFE
// wrong-type READ is REPL-cross-batch-only — under `--run` the single shared
// substitution pins the delegating call's param types, so the read is rejected
// there (itself a REPL/`--run` divergence). The primary RED signal pinned below
// is therefore the deterministic all-mode DEFN wrong-accept; the deterministic
// cross-batch read is captured where the garbage value is stable (rp19's
// Int-read-as-String → `<invalid:N>`) and only narrated where it is a
// nondeterministic heap pointer (rp15's String-read-as-Int).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// A defn that the REPL accepts and publishes ends its echo with `; defn`; a
// rejected defn prints `Error:` instead and never publishes. `; defn` present
// therefore means "accepted" — the deterministic, message-wording-independent
// accept marker used by every should-reject guard below.
fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output()
}

fn run_prims(user: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(user)
        .output()
}

// =============================================================================
// GREEN regression guards — B-1 (CLOSED by CS-4.1). These REJECT today; they
// guard against regression of the clause-param-acquires-sibling-types fix.
// =============================================================================

// rp4 — the ORIGINAL B-1 vector: a clause returns its own param (`p`) but binds
// a delegating self-call `(rp4 p rot 0)` in a `let`; before CS-4.1 the drain
// let `p`/`rot` acquire the 3-arg sibling's `:Int` types through that call, then
// published a scheme claiming genericity over the Int-specialised body —
// `(rp4 "x" "y")` returned a String heap pointer typed Int. CS-4.1 reverted the
// AP-1 acceptance term; §5.1.2 clause independence now rejects the unpinned `p`.
// spec: spec/05-definitions.md §5.1.2 — per-clause independent type-checking.
// defect: class=wrong-accept locus=crates/cranelisp-typecheck/src/program/finalize.rs found=S111 owner=/dev
#[test]
fn rp4_delegating_let_body_multi_arity_param_not_pinned_rejected() {
    let out = repl_prims(
        "(defn rp4 ([:a p :a rot] (let [q (rp4 p rot 0)] p)) \
                   ([:Int p :Int rot :Int idx] idx))\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("; defn"),
        "rp4's 2-arg clause leaves `:a p`/`:a rot` unpinned — the delegating \
         self-call MUST NOT back-flow the 3-arg sibling's `:Int` types (§5.1.2 \
         clause independence). It MUST be REJECTED, not accepted/published \
         (B-1, closed by CS-4.1; this guards regression); got:\n{c}"
    );
    assert!(
        c.contains("not pinned") && c.contains("5.1.2") && c.contains("rp4"),
        "rp4 rejection MUST name the unpinned param and cite §5.1.2 clause \
         independence; got:\n{c}"
    );
}

// rp2 — the SECOND B-1 vector CS-4.1 closed: a body TYPE ASCRIPTION `:a (rp2 …)`
// unifies the self-call's return var with a PARAM var, so the benign-overload
// exemption used to spare it → same memory-unsafe accept. CS-4.1 subtracts each
// clause's own param-type free vars from the benign set. Rejects today.
// spec: spec/05-definitions.md §5.1.2 — per-clause independent type-checking.
// defect: class=wrong-accept locus=crates/cranelisp-typecheck/src/program/finalize.rs found=S111 owner=/dev
#[test]
fn rp2_body_ascription_self_call_multi_arity_param_not_pinned_rejected() {
    let out = repl_prims(
        "(defn rp2 ([:a p :a rot] :a (rp2 p rot 0)) \
                   ([:Int p :Int rot :Int idx] idx))\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("; defn"),
        "rp2's `:a`-ascribed body over a delegating self-call MUST NOT let the \
         clause params acquire the sibling's `:Int` types (§5.1.2). It MUST be \
         REJECTED (B-1 vector 2, closed by CS-4.1); got:\n{c}"
    );
    assert!(
        c.contains("ambiguous") && c.contains("arity clause") && c.contains("rp2"),
        "rp2 rejection MUST flag the unpinned polymorphic value in the arity \
         clause; got:\n{c}"
    );
}

// =============================================================================
// RED defect guards — B-2 (OPEN, LATENT/pre-existing, predates CS-4). A LEAF
// body escapes the §5.1.2 child-position scan → param never pinned → wrong-
// accept. Assert rejection; RED today, flip GREEN when CS-4.2 lands.
// =============================================================================

// rp15 (forward) — the B-2 exemplar. The FIRST clause `([:a p :a rot] p)` is a
// leaf body (bare `Var p`): no child expr, so `find_ambiguous_value_position`
// never scans it and the unpinned `:a p`/`:a rot` sail through. The defn
// WRONG-ACCEPTS, publishing `(Fn [a a] primitives/Int)` — free-var params.
// §5.1.2 requires rejection.
//
// Memory-safety (REPL cross-batch, narrated — value is a nondeterministic heap
// pointer, so it is NOT asserted per tests/CLAUDE.md no-flaky rule): with the
// `(a,a)` params persisted, a later-batch `(rp15 "x" "y")` matches and returns
// the String pointer `p` typed `:primitives/Int` — a memory-unsafe wrong-type
// read. Under `--run` (single batch) the delegating sibling's shared subst pins
// the params, so the read is rejected there (REPL/`--run` divergence). The
// deterministic all-mode signal pinned here is the DEFN wrong-accept itself.
// spec: spec/05-definitions.md §5.1.2 — per-clause independent type-checking.
// defect: class=wrong-accept locus=crates/cranelisp-typecheck/src/program/finalize.rs found=S111 owner=/dev
#[test]
fn rp15_leaf_body_var_clause_escapes_param_scan_defn_accepted_should_reject() {
    // REPL transcript: define, then cross-batch call with String args. The
    // load-bearing assertion is the deterministic DEFN accept marker.
    let out = repl_prims(
        "(defn rp15 ([:a p :a rot] p) ([:Int p :Int rot :Int idx] (rp15 p rot)))\n\
         (rp15 \"x\" \"y\")\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("; defn"),
        "rp15's leaf-body clause `([:a p :a rot] p)` leaves `p`/`rot` unpinned \
         but escapes the §5.1.2 child-position scan (B-2). The defn MUST be \
         REJECTED, not accepted with a `(Fn [a a] …)` free-var-param scheme — \
         that scheme lets a later-batch `(rp15 \"x\" \"y\")` read a String \
         pointer as `:primitives/Int` (memory-unsafe wrong-type read); got:\n{c}"
    );
}

// rp19 (reverse mirror) — the SAME leaf-body escape with a concrete `:String`
// sibling delegating INTO the leaf clause. The wrong-type read direction flips:
// `(rp19 1 2)` reads the Int `1` as a String pointer → address 0x1 →
// `<invalid:1>`, which (unlike rp15's heap pointer) is DETERMINISTIC. So this
// guard pins BOTH facets deterministically: the DEFN wrong-accept AND the
// downstream memory-unsafe read.
// spec: spec/05-definitions.md §5.1.2 — per-clause independent type-checking.
// defect: class=wrong-accept locus=crates/cranelisp-typecheck/src/program/finalize.rs found=S111 owner=/dev
#[test]
fn rp19_mirror_int_read_as_string_cross_batch_should_reject() {
    let out = repl_prims(
        "(defn rp19 ([:a p :a rot] p) ([:String p :String rot :String idx] (rp19 p rot)))\n\
         (rp19 1 2)\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    // Facet 1 (DEFN, deterministic, all-mode): the wrong-accept itself.
    assert!(
        !c.contains("; defn"),
        "rp19's leaf-body clause `([:a p :a rot] p)` leaves params unpinned and \
         escapes the §5.1.2 scan (B-2 mirror). The defn MUST be REJECTED, not \
         accepted with a `(Fn [a a] primitives/String)` free-var-param scheme; \
         got:\n{c}"
    );
    // Facet 2 (READ, deterministic): with `(a,a)` params persisted, the
    // cross-batch `(rp19 1 2)` reads Int `1` as a String pointer → `<invalid:1>`.
    // When the defn is correctly rejected this read cannot occur.
    assert!(
        !c.contains("<invalid"),
        "rp19's wrong-accept lets a later-batch `(rp19 1 2)` read the Int `1` as \
         a String pointer (`<invalid:1>`) — a memory-unsafe wrong-type read. \
         §5.1.2 MUST reject the defn so this read never happens; got:\n{c}"
    );
}

// lf1 — the MINIMAL leaf-body escape (single clause), UNUSED `:a` param, literal
// body. Memory-CONSISTENT (`p` is never read, so no wrong-type read is possible)
// but still a §5.1.2 violation: written in the multi-signature clause form
// `([:a p] 42)`, the clause param `p` stays a free type var after checking its
// own body. §5.1.2 requires the param be pinned REGARDLESS of read-safety, so
// this MUST be rejected. All-mode wrong-accept (REPL publishes `(Fn [a] Int)`;
// `--run` computes the body → exit 42).
// spec: spec/05-definitions.md §5.1.2 — per-clause independent type-checking.
// defect: class=wrong-accept locus=crates/cranelisp-typecheck/src/program/finalize.rs found=S111 owner=/dev
#[test]
fn lf1_leaf_literal_body_unused_free_var_param_should_reject() {
    // REPL facet.
    let out = repl_prims("(defn lf1 ([:a p] 42))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("; defn"),
        "lf1 `([:a p] 42)` leaves the clause param `:a p` a free type var after \
         checking its (literal, leaf) body — §5.1.2 requires it be pinned even \
         though the memory read is consistent (`p` is unused). MUST be REJECTED, \
         not accepted as `(Fn [a] primitives/Int)`; got:\n{c}"
    );
    // All-mode facet: `--run` accepts and COMPUTES the body → exit 42. Correct
    // §5.1.2 rejection is a compile error → main never runs → not exit 42.
    let run = run_prims("(defn lf1 ([:a p] 42))\n(defn main [] (Pure (lf1 7)))\n");
    assert!(
        run.status.code() != Some(42),
        "lf1 wrong-accepts under `--run` too (all modes): it computes `(lf1 7)` \
         = 42 and exits 42 instead of failing §5.1.2 at compile time; got exit \
         {:?}:\n{}{}",
        run.status.code(),
        run.stdout,
        run.stderr
    );
}

// lf2 — leaf-body escape, single clause, body RETURNS the param (`p`). This is
// the memory-CONSISTENT shape at the far end of the family: ret var ≡ param var,
// so at any call site the return is pinned to the argument type — no wrong-type
// read is ever produced (contrast rp15/rp19). It is STILL a §5.1.2 violation:
// checked in isolation the clause param `:a p` stays a free type var, and
// §5.1.2 requires it be pinned regardless of read-safety. MUST be rejected.
// (The pair lf1/lf2 pins the "read-safety is irrelevant to the §5.1.2 verdict"
// boundary: neither is memory-unsafe, both must reject.)
// spec: spec/05-definitions.md §5.1.2 — per-clause independent type-checking.
// defect: class=wrong-accept locus=crates/cranelisp-typecheck/src/program/finalize.rs found=S111 owner=/dev
#[test]
fn lf2_leaf_body_returns_free_var_param_should_reject() {
    let out = repl_prims("(defn lf2 ([:a p] p))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("; defn"),
        "lf2 `([:a p] p)` leaves the clause param `:a p` a free type var after \
         checking its (bare-Var, leaf) body — §5.1.2 requires it be pinned even \
         though ret ≡ param keeps it memory-consistent. MUST be REJECTED, not \
         accepted as `(Fn [a] a)`; got:\n{c}"
    );
    let run = run_prims("(defn lf2 ([:a p] p))\n(defn main [] (Pure (lf2 7)))\n");
    assert!(
        run.status.code() != Some(7),
        "lf2 wrong-accepts under `--run` too (all modes): it computes `(lf2 7)` \
         = 7 and exits 7 instead of failing §5.1.2 at compile time; got exit \
         {:?}:\n{}{}",
        run.status.code(),
        run.stdout,
        run.stderr
    );
}
