// multi_arity_clause_param_51_2.rs — §5.1.2 multi-signature back-flow ACCEPTING
// suite (Sprint 112 Phase 5, the 0628/I-C wave).
//
// Covers `spec/05-definitions.md §5.1.2` — the SETTLED inference rule (S111
// `c9f05b64`): a multi-signature `defn` is inference-equivalent to its clauses
// written as separate, mutually-recursive top-level functions. A self-call to a
// sibling clause is an ordinary call that pins the caller-clause's parameters
// through the callee clause's signature. Annotations are DESCRIPTIVE (§3.3 — a
// written type variable adds no rigidity); a genuinely-polymorphic clause is
// admissible whenever it does not overlap a same-arity sibling (§5.1.1).
//
// UNWIND note (S112, plan §2): this file previously asserted the DRIFTED §5.1.2
// (clause independence / no back-flow / "cannot stay polymorphic"). Every asset
// below is a CONVERSION of a superseded rejection guard into the accepting test
// the corrected rule demands — never a deletion. The B-1/B-2 history lives in
// git; the "memory-safety saga" it encoded dissolved (FIXME 0642): the UAF was
// an artifact of the drift + monomorphise-by-sibling, not a real defect. The
// durable memory-safety observables (a wrong-TYPE call is a clean type error,
// never a heap-ptr-as-Int read / `<invalid:` leak) are PRESERVED — now
// guaranteed by the type error at the call site rather than a definition reject.
//
// Stage-1 state (QA-first, before leg (a) lands): the back-flow rows are RED
// (HEAD still rejects the un-annotated delegating clauses with the pre-drain
// "each arity clause is type-checked independently (§5.1.2)" scan); they flip
// GREEN when leg (a) removes the independence block. MS-2 (plain poly+concrete)
// is already GREEN at HEAD (see its note).

#[path = "helpers/mod.rs"]
mod helpers;

use std::time::Duration;

use helpers::e2e::{run_through_all_modes, Cranelisp, PreludeVariant};

// A defn the REPL accepts and publishes ends its echo with `; defn`; a rejected
// defn prints `Error:` instead and never publishes. `; defn` present therefore
// means "accepted" — the deterministic, message-wording-independent accept
// marker used throughout.
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

// The 0642 anchor program, verbatim (spec §5.1.2 worked example). The 2-arg
// clause's delegating self-call `(rp4 p rot 0)` pins `p, rot : Int` through the
// 3-arg sibling (whose `add-i64` fixes it to `(Fn [Int Int Int] Int)`); the
// 2-arg clause returns `p`, so `(rp4 3 4)` = 3 and the clause is `(Fn [Int Int]
// Int)`.
const RP4: &str = "(defn rp4 ([p rot] (let [q (rp4 p rot 0)] p)) \
                             ([p rot idx] (add-i64 p (add-i64 rot idx))))";

// =============================================================================
// MS-1 / MS-1b / MS-2 / MS-4 — the leg-(a) anchors (plan §1).
// =============================================================================

// MS-1 — the rp4 anchor: un-annotated delegating self-call compiles + runs; the
// 2-arg clause's TYPE is `(Fn [Int Int] Int)` (back-flow pinned, not
// re-generalized — the load-bearing TYPE assertion). RED at HEAD (rejected with
// the pre-drain independence scan); GREEN at leg (a).
// spec: spec/05-definitions.md §5.1.2 — inference-equivalent to separate
// mutually-recursive functions (back-flow through the sibling self-call).
#[test]
fn rp4_unannotated_backflow_accepted_and_runs() {
    // Run facet ×3 (REPL + --run + --link): the 2-arg clause returns `p`, so
    // `(rp4 3 4)` = 3. Mode-equivalent exit/value across all six permutations.
    run_through_all_modes(
        &format!("{RP4}\n(defn main [] (Pure (rp4 3 4)))\n"),
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(3);

    // TYPE facet (load-bearing, REPL): `/sig rp4` shows the 2-arg clause pinned
    // to `(Fn [Int Int] Int)` — back-flow pinned it, it was NOT re-generalized.
    let out = repl_prims(&format!("{RP4}\n/sig rp4\n"));
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("; defn") && !c.contains("ambiguous"),
        "rp4 MUST be ACCEPTED per the settled §5.1.2 (the 2-arg clause's \
         delegating `(rp4 p rot 0)` pins `p, rot : Int` through the 3-arg \
         sibling); MUST NOT be an independence/ambiguity reject; got:\n{c}"
    );
    assert!(
        out.stdout.contains("(Fn [primitives/Int primitives/Int] primitives/Int)"),
        "`/sig rp4` MUST show the 2-arg clause as `(Fn [Int Int] Int)` — the \
         back-flow pin, not a re-generalized free-var scheme; got:\n{}",
        out.stdout
    );
}

// MS-1b — [oracle] heap-integrity fence on the flagship new shape: rp4 driven
// K× under `--link` (the sustained-repetition pattern, tests/CLAUDE.md). Assert
// exit 0. RED at HEAD (rp4 rejected ⇒ link fails); GREEN at leg (a). Graduates
// into the S113 oracle lane.
// spec: spec/05-definitions.md §5.1.2 — back-flow-pinned recursion reaches
// codegen; the sustained-repetition heap-integrity guard (tests/CLAUDE.md).
#[test]
fn rp4_link_repeated_dispatch_does_not_corrupt_heap() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(&format!(
            "{RP4}\n\
             (defn drive [:primitives/Int n :primitives/Int acc] \
               (if (eq-i64 n 0) acc (drive (sub-i64 n 1) (add-i64 acc (rp4 n n)))))\n\
             (defn main [] (let [r (drive 1000 0)] (Pure 0)))\n"
        ))
        .timeout(Duration::from_secs(60))
        .output();
    out.assert_exit(0);
}

// MS-2 — poly + concrete non-overlapping multi-sig (the §5.1.2 admissible-poly
// example): `([:a x] x)` alongside `([:Int x :Int y] ...)`. Both clauses
// exercised at two instantiations. NOTE: already GREEN at HEAD (plain
// unconstrained poly clauses were never the rejected-by-construction case — that
// is the CONSTRAINED cell, CP-1); kept as a must-hold acceptance guard so the
// leg-(a) rework does not regress it.
// spec: spec/05-definitions.md §5.1.2 — a genuinely-polymorphic clause is
// admissible when it does not overlap a same-arity sibling.
#[test]
fn poly_clause_nonoverlapping_arity_accepted_both_dispatch() {
    let out = repl_prims(
        "(defn f ([:a x] x) ([:Int x :Int y] (add-i64 x y)))\n\
         (f 5)\n(f \"s\")\n(f 2 3)\n",
    );
    out.assert_stdout_contains_all(&[
        ":primitives/Int 5",      // poly clause at Int
        ":primitives/String \"s\"", // poly clause at String — second instantiation
        ":primitives/Int 5",      // concrete 2-arg clause: 2+3
    ]);
}

// MS-4 — sibling-call type MISMATCH is a plain type error (the durable
// memory-safety negative the dissolved "multi-arity UAF saga" leaves behind):
// rp4 is accepted, then `(rp4 "x" "y")` is a clean String≠Int type error —
// NEVER a wrong-accept and NEVER a `<invalid:`/heap-garbage read. RED at HEAD
// (rp4 rejected up front); pairs with MS-1.
// spec: spec/05-definitions.md §5.1.2 — a wrong-type call against a
// back-flow-pinned clause is an ordinary type error, not memory-unsafe.
#[test]
fn backflow_pinned_param_call_with_wrong_type_rejected_neg() {
    // REPL facet.
    let out = repl_prims(&format!("{RP4}\n(rp4 \"x\" \"y\")\n"));
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("; defn"),
        "rp4 MUST first be ACCEPTED (back-flow pins the 2-arg clause to \
         `(Fn [Int Int] Int)`); got:\n{c}"
    );
    assert!(
        c.to_lowercase().contains("type") && (c.contains("String") || c.contains("string")),
        "`(rp4 \"x\" \"y\")` MUST be a clean String≠Int type error at the call \
         site; got:\n{c}"
    );
    // Memory-safety: the wrong-type call must NEVER produce a heap-ptr-as-Int
    // read (`<invalid:` leak). The type error at the call site guarantees it.
    assert!(
        !c.contains("<invalid"),
        "a wrong-type call MUST be rejected at the type level, NEVER read a \
         String pointer as an Int (`<invalid:`); got:\n{c}"
    );
    // `--run` facet: the same program must be a compile error, not exit-with-value.
    let run = run_prims(&format!("{RP4}\n(defn main [] (Pure (rp4 \"x\" \"y\")))\n"));
    let rc = format!("{}{}", run.stdout, run.stderr);
    assert!(
        !run.status.success() && !rc.contains("<invalid"),
        "under `--run` the wrong-type `(rp4 \"x\" \"y\")` MUST be a clean compile \
         error, never a memory-unsafe run; got exit {:?}:\n{rc}",
        run.status.code()
    );
}

// =============================================================================
// UW-1..UW-6 — the unwind conversions (plan §2). Each was a rejection guard;
// each is now the accepting test the corrected §5.1.2 demands. Preserved facets
// noted per row.
// =============================================================================

// UW-2 — rp2: a body TYPE ASCRIPTION over the delegating self-call. Under the
// corrected rule the self-call return is pinned to `Int` by the 3-arg sibling,
// and the `:Int` ascription is a CHECK (§3.3.3), not an abstraction — it
// compiles and runs. Preserved facet: the body-ascription × self-call shape.
// `(rp2 3 4)` = `(rp2 3 4 0)` = 3+4+0 = 7. RED at HEAD (rejected); GREEN at leg (a).
// spec: spec/05-definitions.md §5.1.2 — back-flow through the delegating
// self-call; the ascription checks the pinned return (§3.3.3).
#[test]
fn rp2_body_ascription_self_call_accepted_and_runs() {
    let out = repl_prims(
        "(defn rp2 ([p rot] :primitives/Int (rp2 p rot 0)) \
                   ([p rot idx] (add-i64 p (add-i64 rot idx))))\n\
         (rp2 3 4)\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("; defn") && !c.contains("ambiguous"),
        "rp2's `:Int`-ascribed delegating self-call MUST be ACCEPTED — the \
         ascription is a CHECK over the back-flow-pinned return (§3.3.3), not an \
         ambiguity; got:\n{c}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 7"),
        "`(rp2 3 4)` = `(rp2 3 4 0)` = 3+4+0 = 7; got:\n{}",
        out.stdout
    );
}

// UW-3 — rp15: a LEAF-body clause `([:a p :a rot] p)` whose params are pinned
// to `Int` by the 3-arg sibling's delegating call `(rp15 p rot)`. Accepts as
// `(Fn [Int Int] Int)`; `(rp15 "x" "y")` is a clean type error. Preserved
// facet: the cross-batch memory-safety observable — no heap-ptr-as-Int read;
// now guaranteed by the call-site type error, its ABSENCE asserted.
// RED at HEAD (rejected up front); GREEN at leg (a).
// spec: spec/05-definitions.md §5.1.2 — leaf-clause params pinned by a sibling's
// delegating self-call.
#[test]
fn rp15_leaf_var_clause_backflow_accepted_wrong_type_call_rejected_neg() {
    let out = repl_prims(
        "(defn rp15 ([:a p :a rot] p) ([:Int p :Int rot :Int idx] (rp15 p rot)))\n\
         (rp15 \"x\" \"y\")\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("; defn") && !c.contains("ambiguous"),
        "rp15's leaf-body clause `([:a p :a rot] p)` is pinned to `(Fn [Int Int] \
         Int)` by the 3-arg sibling's `(rp15 p rot)` call — MUST be ACCEPTED, not \
         an independence reject; got:\n{c}"
    );
    // Memory-safety: with the 2-arg clause pinned to `(Fn [Int Int] Int)`, the
    // String call MUST be a clean type error — NOT a String-pointer-read-as-Int
    // (at HEAD rp15 wrong-accepts as `(Fn [a a] a)`, so `(rp15 "x" "y")` reads a
    // heap pointer as a garbage Int with NO error — the exact memory-unsafe read
    // the type error must replace). This is the load-bearing RED at HEAD.
    assert!(
        c.contains("type") && (c.contains("mismatch") || c.contains("expected")),
        "`(rp15 \"x\" \"y\")` MUST be a clean String≠Int type error at the call \
         site (the back-flow pin makes the wrong-type read impossible), NEVER a \
         silent heap-ptr-as-Int garbage read; got:\n{c}"
    );
    assert!(
        !c.contains("<invalid"),
        "`(rp15 \"x\" \"y\")` MUST NOT surface a `<invalid:` pointer read; got:\n{c}"
    );
}

// UW-4 — rp19 (mirror): the leaf clause is pinned to `String` by a `:String`
// sibling's delegating call. Accepts as `(Fn [String String] String)`;
// `(rp19 1 2)` is a clean type error AND still no `<invalid`. Preserved facet:
// the DETERMINISTIC `<invalid:` negative (an Int read as a String pointer →
// address 0x1 → `<invalid:1>`), asserted verbatim. RED at HEAD; GREEN at leg (a).
// spec: spec/05-definitions.md §5.1.2 — leaf-clause params pinned by a sibling's
// delegating self-call (String direction).
#[test]
fn rp19_mirror_backflow_accepted_wrong_type_call_no_invalid_neg() {
    let out = repl_prims(
        "(defn rp19 ([:a p :a rot] p) ([:String p :String rot :String idx] (rp19 p rot)))\n\
         (rp19 1 2)\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("; defn") && !c.contains("ambiguous"),
        "rp19's leaf clause is pinned to `(Fn [String String] String)` by the \
         3-arg `:String` sibling — MUST be ACCEPTED; got:\n{c}"
    );
    assert!(
        !c.contains("<invalid"),
        "`(rp19 1 2)` MUST be a clean type error (Int≠String), NEVER read the Int \
         `1` as a String pointer (`<invalid:1>`) — the deterministic \
         memory-safety negative the unwind preserves verbatim; got:\n{c}"
    );
}

// UW-5 — lf1: a genuinely-polymorphic single clause `([:a p] 42)` with an
// UNUSED poly param and a literal leaf body. This is exactly the §5.1.2
// admissible-poly example class: a genuinely-poly clause standing alone is a
// valid standalone function, hence admissible. Preserved facet: the unused-param
// + literal-leaf shape; the `--run` exit 42 is now the POSITIVE. RED at HEAD
// (rejected as unpinned); GREEN at leg (a) — but see note: HEAD already
// wrong-ACCEPTS lf1, so the REPL accept facet may already hold; the load-bearing
// flip is that acceptance becomes CORRECT (poly), not a wrong-accept.
// spec: spec/05-definitions.md §5.1.2 — a genuinely-polymorphic clause is
// admissible (§3.11.3 named-poly-definition soundness).
#[test]
fn lf1_leaf_literal_poly_clause_admissible_runs() {
    let out = repl_prims("(defn lf1 ([:a p] 42))\nlf1\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("; defn") && !c.contains("ambiguous"),
        "lf1 `([:a p] 42)` is a genuinely-polymorphic admissible clause \
         (§5.1.2 / §3.11.3) — MUST be ACCEPTED, not an ambiguity reject; got:\n{c}"
    );
    // Positive: `--run` computes the body → exit 42 (the clause is admissible
    // and reaches codegen at a concrete use).
    let run = run_prims("(defn lf1 ([:a p] 42))\n(defn main [] (Pure (lf1 7)))\n");
    assert!(
        run.status.code() == Some(42),
        "`(lf1 7)` = 42 ⇒ `--run` exits 42 (the admissible poly clause \
         monomorphises at the concrete use); got exit {:?}:\n{}{}",
        run.status.code(),
        run.stdout,
        run.stderr
    );
}

// UW-6 — lf2: the leaf-IDENTITY clause `([:a p] p)` — the spec's own admissible
// example `([:a x] x)`. A valid standalone identity function, hence admissible
// in a multi-signature `defn`. Preserved facet: the leaf-identity shape.
// `(lf2 7)` = 7 ⇒ `--run` exit 7. RED at HEAD (rejected as unpinned); GREEN at
// leg (a) — as with UW-5, HEAD wrong-accepts, so the flip is accept-becomes-
// CORRECT-poly.
// spec: spec/05-definitions.md §5.1.2 — the admissible-poly example `([:a x] x)`.
#[test]
fn lf2_leaf_identity_poly_clause_admissible() {
    let out = repl_prims("(defn lf2 ([:a p] p))\nlf2\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("; defn") && !c.contains("ambiguous"),
        "lf2 `([:a p] p)` is the spec's admissible identity example `([:a x] x)` \
         — MUST be ACCEPTED; got:\n{c}"
    );
    let run = run_prims("(defn lf2 ([:a p] p))\n(defn main [] (Pure (lf2 7)))\n");
    assert!(
        run.status.code() == Some(7),
        "`(lf2 7)` = 7 ⇒ `--run` exits 7; got exit {:?}:\n{}{}",
        run.status.code(),
        run.stdout,
        run.stderr
    );
}

// =============================================================================
// B1 / I1 — W2.1 remediation repros (the W2 /review BLOCK). Both are §5.1.2
// equivalence cells that the leg-(a) working tree gets wrong: a ≥2-hop self-call
// delegation chain (B1) and a self-recursive genuinely-poly clause (I1). Both
// are pinned against the standalone-mutually-recursive-functions oracle the
// settled rule names — the multi-signature program MUST behave exactly as its
// equivalent separate functions do.
// =============================================================================

// The 3-clause delegation chain (review's live B1 repro). Clause `[a]` delegates
// to the 2-arg clause `(f3 a 0)`; the 2-arg clause delegates to the 3-arg clause
// `(f3 a b 1)`; the 3-arg leaf `(add-i64 a (add-i64 b c))` pins its params to
// `Int`. The back-flow pins every clause's params up the chain, so
// `(f3 5)` = `(f3 5 0)` = `(f3 5 0 1)` = 5 + (0 + 1) = 6.
const F3: &str = "(defn f3 ([a] (f3 a 0)) ([a b] (f3 a b 1)) \
                            ([a b c] (add-i64 a (add-i64 b c))))";

// B1 — a ≥2-hop self-call delegation chain leaks a dangling `$Var` dispatch to
// codegen. On the leg-(a) working tree the self-call `SigDispatch` is derived
// MID-drain (`resolve_pending_overloads`): when clause 1's self-call to clause 2
// is drained, clause 2's params are still `Var` (clause 2 is pinned only when
// ITS own self-call drains later in the same pass), so clause 1 records clause
// 2's `$Var` template name — which `finalize_multi_sig_variant_types` then
// removes. The dangling `user/f3$Var+Var` dispatch reaches codegen:
//   `resolved_target 'user/f3$Var+Var' … fetched no symbol-table entry`.
// Spec-correct outcome (design §11.3.2 fix shape — derive the self-call
// `SigDispatch` post-drain): compiles clean, `(f3 5)` = 6, the 1-arg clause is
// `(Fn [Int] Int)`. RED until the B1 fix lands.
// spec: spec/05-definitions.md §5.1.2 — inference-equivalent to separate
// mutually-recursive functions; the self-call dispatch resolves to a real entry.
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck/src/program/register.rs::resolve_pending_overloads (self-call SigDispatch derived mid-drain, design §11.3.2) found=S112 owner=/dev
#[test]
fn f3_delegation_chain_backflow_accepted_and_runs() {
    // Run facet ×3 modes (REPL + --run + --link, fresh + cached): the chain
    // resolves to 6 with no dangling `$Var` dispatch reaching codegen. RED at
    // HEAD (the `user/f3$Var+Var` codegen leak fails every mode).
    run_through_all_modes(
        &format!("{F3}\n(defn main [] (Pure (f3 5)))\n"),
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(6);

    // REPL accept + value + no-leak facet.
    let out = repl_prims(&format!("{F3}\n(f3 5)\n"));
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("; defn") && !c.contains("ambiguous"),
        "f3 MUST be ACCEPTED (the delegation chain pins every clause to Int via \
         back-flow, §5.1.2); got:\n{c}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 6"),
        "`(f3 5)` = `(f3 5 0)` = `(f3 5 0 1)` = 5 + (0 + 1) = 6; got:\n{}",
        out.stdout
    );
    // The load-bearing RED: NO dangling `$Var` dispatch may reach codegen — the
    // B1 leak. The self-call dispatch names MUST resolve to real entries.
    assert!(
        !c.contains("$Var") && !c.contains("resolved_target") && !c.contains("codegen error"),
        "f3's ≥2-hop delegation chain MUST NOT leak a dangling `$Var` dispatch \
         (e.g. `user/f3$Var+Var`) to codegen — every self-call `SigDispatch` \
         MUST derive from the finalised post-drain mangle (design §11.3.2); \
         got:\n{c}"
    );

    // TYPE facet (REPL /sig): the 1-arg clause is pinned to `(Fn [Int] Int)` by
    // the back-flow, not re-generalized.
    let sig = repl_prims(&format!("{F3}\n/sig f3\n"));
    assert!(
        sig.stdout.contains("(Fn [primitives/Int] primitives/Int)"),
        "`/sig f3` MUST show the 1-arg clause as `(Fn [Int] Int)` — the back-flow \
         pin through the chain; got:\n{}",
        sig.stdout
    );
}

// B1 oracle fence — the standalone twin: the SAME chain written as three
// separate, mutually-recursive top-level functions compiles fine and runs to 6
// (batch `--run`, where forward references between top-level defns resolve).
// §5.1.2 names this equivalence explicitly: the multi-signature `f3` MUST behave
// identically. This twin is GREEN on the leg-(a) tree — it is the fence that
// isolates B1 to the multi-signature codegen path, not the inference model.
// spec: spec/05-definitions.md §5.1.2 — separate mutually-recursive functions
// are the oracle the multi-signature defn is inference-equivalent to.
#[test]
fn f3_delegation_chain_standalone_twin_compiles_and_runs() {
    let run = run_prims(
        "(defn f3a [a] (f3b a 0))\n\
         (defn f3b [a b] (f3c a b 1))\n\
         (defn f3c [a b c] (add-i64 a (add-i64 b c)))\n\
         (defn main [] (Pure (f3a 5)))\n",
    );
    assert!(
        run.status.code() == Some(6),
        "the three-separate-mutually-recursive-functions twin MUST compile + run \
         to 6 (the §5.1.2 oracle for the multi-signature f3); got exit {:?}:\n{}{}",
        run.status.code(),
        run.stdout,
        run.stderr
    );
}

// I1 — a self-recursive genuinely-polymorphic clause wrong-REJECTS. The 1-arg
// clause `([x] (if true x (g x)))` is an identity function whose (dead) recursive
// branch calls the overloaded base; standing alone it is `(defn g1 [x] (if true
// x (g1 x)))`, which accepts and runs. In the multi-signature `g` the leg-(a)
// mono-recheck sets `current_defn` to the template mangle (`g$Var…`), so the
// inner self-call classifies as EXTERNAL and monomorphises instead of unifying —
// leaving a residual var that wrong-rejects `(g 5)` with an INTERNAL mangle
// leaking into the user-facing diagnostic:
//   `ambiguous type … monomorphised in 'user/g$Var$Int' …`.
// Spec-correct: `g` accepts, `(g 5)` = 5, no internal `$`-mangle in any
// diagnostic (design §11.3.1 caveat (b)). RED until the I1 fix lands.
// spec: spec/05-definitions.md §5.1.2 — a genuinely-polymorphic clause is
// inference-equivalent to the standalone function (which accepts + runs).
// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/program/register.rs::resolve_pending_overloads (mono-recheck current_defn shadows self-call classification, design §11.3.1 caveat (b)) found=S112 owner=/dev
#[test]
fn recursive_poly_clause_accepted_matches_standalone_twin() {
    // Multi-signature half: g accepts, `(g 5)` = 5, no internal mangle leak.
    let out = repl_prims("(defn g ([x] (if true x (g x))) ([a b] a))\n(g 5)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("; defn") && !c.contains("ambiguous"),
        "g's genuinely-poly recursive clause `([x] (if true x (g x)))` is \
         inference-equivalent to the standalone `g1` (which accepts) — MUST be \
         accepted, not wrong-rejected (§5.1.2); got:\n{c}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 5"),
        "`(g 5)` = 5 (the identity clause at Int); got:\n{}",
        out.stdout
    );
    // The internal monomorphisation mangle MUST NOT surface in a user diagnostic
    // (the `user/g$Var$Int` leak). The load-bearing RED.
    assert!(
        !c.contains("$Var") && !c.contains("$Int") && !c.contains("monomorphised in"),
        "no INTERNAL `$`-mangle (e.g. `user/g$Var$Int`) may appear in a \
         user-facing diagnostic; got:\n{c}"
    );

    // Standalone twin fence: g1 accepts and `(g1 5)` = 5 (GREEN on the leg-(a)
    // tree — the equivalence the multi-sig half MUST match).
    let solo = repl_prims("(defn g1 [x] (if true x (g1 x)))\n(g1 5)\n");
    let sc = format!("{}{}", solo.stdout, solo.stderr);
    assert!(
        sc.contains("; defn") && solo.stdout.contains(":primitives/Int 5"),
        "the standalone twin `(defn g1 [x] (if true x (g1 x)))` MUST accept and \
         `(g1 5)` = 5 — the §5.1.2 oracle for g's poly clause; got:\n{sc}"
    );
}

// =============================================================================
// R1 — W2.1 /review residual (Important; design record: monomorphisation.md
// §11.3.4 "The R1 boundary — a KNOWN LIMIT of the as-built gate"). The I1 fix's
// mono-recheck inline gate (§11.3.4) fires ONLY for a same-instantiation
// self-call (same arity, args ≡ the instance's concrete params). A CROSS-ARITY
// sibling self-call from a genuinely-poly template clause is NOT covered: its
// args differ in arity from the instance params, the inline gate skips, the call
// re-defers a pending entry the drain has already taken, and it orphans — the
// same wrong-reject-with-internal-name-leak shape I1 fixed for the same-arity
// case. Natural fix direction (§11.3.4, NOT designed this wave): widen the
// `mono_recheck_self` match set from "this instance" to "the base's post-drain-
// settled overload clauses".
// =============================================================================

// The cross-arity probe (design §11.3.4 verbatim). The 1-arg genuinely-poly
// clause `([:a x] (g2 1 2))` self-calls the 2-arg CONCRETE sibling `(g2 1 2)`;
// the 2-arg clause `([:Int a :Int b] (add-i64 a b))` returns 1+2 = 3. So under
// the §5.1.2 separate-mutually-recursive-functions equivalence `(g2 5)` = 3
// (the 1-arg poly clause delegates to the concrete 2-arg sibling and returns
// its result).
const G2: &str = "(defn g2 ([:a x] (g2 1 2)) ([:Int a :Int b] (add-i64 a b)))";

// R1 — cross-arity sibling self-call from a genuinely-poly template clause
// wrong-REJECTS at the CALL with an internal-mangle leak. The defn `g2` is
// accepted (`; defn`), but `(g2 5)` — which monomorphises the 1-arg poly clause
// at Int — wrong-rejects:
//   `ambiguous type … monomorphised in 'user/g2$Var$Int' (a residual unbound
//    type variable reached a codegen position)`.
// Spec-correct: `g2` accepts, `(g2 5)` = 3 (the 1-arg poly clause delegates to
// the concrete 2-arg sibling), no internal `$`-mangle in any diagnostic. The
// standalone twin (a poly 1-arg fn delegating to a concrete 2-arg fn) accepts
// and runs → 3, the §5.1.2 oracle. RED until the R1 fix lands.
// spec: spec/05-definitions.md §5.1.2 — inference-equivalent to separate
// mutually-recursive functions (the standalone twin accepts + runs).
// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/infer.rs::mono_recheck_self-inline-gate (cross-arity sibling self-call not covered, design §11.3.4 R1 boundary) found=S112 owner=/dev
#[test]
fn cross_arity_sibling_self_call_from_poly_clause_accepted_matches_standalone_twin() {
    // Multi-signature half: g2 accepts, `(g2 5)` = 3, no internal mangle leak.
    let out = repl_prims(&format!("{G2}\n(g2 5)\n"));
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("; defn") && !c.contains("ambiguous"),
        "g2's 1-arg genuinely-poly clause `([:a x] (g2 1 2))` delegating to the \
         concrete 2-arg sibling is inference-equivalent to the standalone twin \
         (which accepts) — MUST be accepted, not wrong-rejected (§5.1.2); got:\n{c}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 3"),
        "`(g2 5)` = `(g2 1 2)` = 1 + 2 = 3 (the poly clause delegates to the \
         concrete 2-arg sibling); got:\n{}",
        out.stdout
    );
    // The internal monomorphisation mangle MUST NOT surface in a user diagnostic
    // (the `user/g2$Var$Int` leak). The load-bearing RED (design §11.3.4).
    assert!(
        !c.contains("$Var") && !c.contains("$Int") && !c.contains("monomorphised in"),
        "no INTERNAL `$`-mangle (e.g. `user/g2$Var$Int`) may appear in a \
         user-facing diagnostic; got:\n{c}"
    );

    // Standalone twin fence: the SAME shape as two separate mutually-recursive
    // top-level functions — a poly 1-arg fn `g2a` delegating to a concrete 2-arg
    // fn `g2b`. This is GREEN today (§5.1.2 oracle); the multi-sig half MUST
    // match it. Its acceptance is what makes g2's rejection a wrong-reject.
    let solo = repl_prims(
        "(defn g2b [:Int a :Int b] (add-i64 a b))\n\
         (defn g2a [:a x] (g2b 1 2))\n\
         (g2a 5)\n",
    );
    let sc = format!("{}{}", solo.stdout, solo.stderr);
    assert!(
        sc.contains("; defn") && solo.stdout.contains(":primitives/Int 3"),
        "the standalone twin `(defn g2a [:a x] (g2b 1 2))` + `(defn g2b [:Int a \
         :Int b] (add-i64 a b))` MUST accept and `(g2a 5)` = 3 — the §5.1.2 \
         oracle for g2's cross-arity poly clause; got:\n{sc}"
    );
}
