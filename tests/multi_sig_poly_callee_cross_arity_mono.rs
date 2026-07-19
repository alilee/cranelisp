// multi_sig_poly_callee_cross_arity_mono.rs — D3 repro (S112 Phase 6b).
//
// A polymorphic callee, invoked from inside a MULTI-SIGNATURE clause body that is
// reached via a CROSS-ARITY self-call, never has its concrete monomorphic
// instance emitted — the call reaches codegen as `undefined function`.
//
//   (defn idpoly [x] x)                               <- genuinely-poly callee
//   (defn build ([n]     (build n 0))                 <- 1-arg clause delegates cross-arity
//                ([n acc] (if (eq-i64 n 0) acc
//                            (build (sub-i64 n 1) (add-i64 acc (idpoly n))))))
//   (build 3)   →   codegen error … undefined function: idpoly
//
// The 2-arg clause's body calls the poly `idpoly` at `Int`; the mono-collect pass
// for the multi-sig clause body never harvests `idpoly$Int`, so the call reaches
// codegen unresolved. Typecheck PASSES — the leak surfaces at the backend.
//
// PRIMITIVE-vs-PRELUDE AXIS (verified S112 Phase 6b): /port's probe used prelude
// `+`/`-`/`=`. Reduced here to primitive ops (`add-i64`/`sub-i64`/`eq-i64`) to
// keep the repro stdlib-free (tests/CLAUDE.md §"Test isolation") — the defect
// STILL FIRES that way. So the trait-method/prelude axis is NOT load-bearing; the
// minimal firing form is this primitive one. The load-bearing axes are: (1) the
// callee is genuinely POLY (`idpoly`), and (2) it is reached from a multi-sig
// clause body entered by a CROSS-ARITY self-call.
//
// DISTINCT from R1 (wrong-reject of a poly clause at the CALL) and R2 (a
// multi-sig-BASE dispatch call loses its resolved_target): here the failing name
// is the POLY CALLEE's mono instance (`idpoly`), never emitted. The concrete
// callee sibling of the carrier-loss family (§11.3.2 mono-harvest for multi-sig
// clause bodies).
//
// VALUE NOTE (S112 Phase 6b surprise): `(build 3)` = 3 + 2 + 1 = 6 (the running
// sum), NOT 3 — the two GREEN fences below both compute 6, confirming the
// intended semantics. (The dispatch brief's "3" was an arithmetic slip.)
//
// ATTRIBUTION: /qa attributes precisely at S113 Phase 1.

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

fn run_prims(user: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(user)
        .output()
}

// The multi-sig `build` whose 2-arg clause calls the poly `idpoly`, reached via
// the 1-arg clause's cross-arity delegating self-call. Stdlib-free (primitive
// ops). `(build 3)` = 3 + 2 + 1 = 6.
const BUILD: &str = "(defn idpoly [x] x)\n\
                     (defn build ([n] (build n 0)) \
                                 ([n acc] (if (eq-i64 n 0) acc \
                                     (build (sub-i64 n 1) (add-i64 acc (idpoly n))))))";

// D3 — the poly callee `idpoly`, invoked from the multi-sig clause body reached
// via the cross-arity self-call, MUST have its `idpoly$Int` mono instance emitted
// — it MUST NOT reach codegen as `undefined function`. `(build 3)` = 6. RED until
// the mono-harvest covers multi-sig clause bodies.
// spec: spec/05-definitions.md §5.1.2 — a multi-signature `defn` is
// inference-equivalent to its clauses as separate mutually-recursive functions;
// a poly callee reached from a clause body monomorphises just as it does there.
// defect: class=carrier-loss locus=typecheck mono-collect for multi-sig clause bodies (poly-callee instance `idpoly$Int` never harvested from a clause reached cross-arity; §11.3.2 sibling of R2) found=S112 owner=/dev
#[test]
fn multi_sig_poly_callee_reached_cross_arity_emits_mono_instance() {
    // REPL facet: `(build 3)` = 6, no `undefined function` leak.
    let out = repl_prims(&format!("{BUILD}\n(build 3)\n"));
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("undefined function") && !c.contains("codegen error"),
        "the poly callee `idpoly` reached from `build`'s multi-sig clause body \
         MUST have its `idpoly$Int` mono instance emitted — it MUST NOT reach \
         codegen as `undefined function` (§5.1.2 clause-body mono harvest); got:\n{c}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 6"),
        "`(build 3)` = 3 + 2 + 1 = 6 (the poly `idpoly` is identity); got:\n{}",
        out.stdout
    );

    // `--run` facet: same program computes 6 ⇒ exit 6.
    let run = run_prims(&format!(
        "{BUILD}\n(import [primitives [Pure]])\n(defn main [] (Pure (build 3)))\n"
    ));
    let rc = format!("{}{}", run.stdout, run.stderr);
    assert!(
        !rc.contains("undefined function"),
        "under `--run` the poly callee `idpoly$Int` MUST be emitted — no \
         `undefined function` leak; got:\n{rc}"
    );
    assert!(
        run.status.code() == Some(6),
        "`(build 3)` = 6 ⇒ `--run` exits 6; got exit {:?}:\n{rc}",
        run.status.code()
    );
}

// GREEN fence 1 — the two-single-arity-defn twin: `build` written as two separate
// mutually-recursive top-level functions calling the same poly `idpoly`. This is
// the §5.1.2 oracle the multi-sig form is inference-equivalent to; GREEN on HEAD
// (exit 6). It isolates the MULTI-SIG clause-body harvest as D3's load-bearing
// element — the identical poly-callee-from-a-cross-arity-delegation shape works
// when the clauses are separate defns.
// spec: spec/05-definitions.md §5.1.2 — separate mutually-recursive functions are
// the oracle for the multi-signature form; a poly callee monomorphises there.
#[test]
fn poly_callee_cross_arity_two_single_defns_twin_runs_green_fence() {
    let run = run_prims(
        "(import [primitives [Pure]])\n\
         (defn idpoly [x] x)\n\
         (defn build1 [n] (build2 n 0))\n\
         (defn build2 [n acc] (if (eq-i64 n 0) acc \
             (build2 (sub-i64 n 1) (add-i64 acc (idpoly n)))))\n\
         (defn main [] (Pure (build1 3)))\n",
    );
    assert!(
        run.status.code() == Some(6),
        "the two-single-arity-defn twin (`build1`/`build2` calling poly `idpoly`) \
         MUST compile + run to 6 — the §5.1.2 oracle isolating the multi-sig \
         clause-body harvest as D3's load-bearing element; got exit {:?}:\n{}{}",
        run.status.code(),
        run.stdout,
        run.stderr
    );
}

// GREEN fence 2 — the SAME multi-sig `build` shape but with NO poly callee: the
// 2-arg clause sums `n` directly (`(add-i64 acc n)`) instead of `(idpoly n)`.
// Pure-Int multi-sig cross-arity delegation with a concrete body works (exit 6),
// isolating the POLY CALLEE as the other load-bearing element of D3.
// spec: spec/05-definitions.md §5.1.2 — a multi-signature cross-arity delegation
// with a fully-concrete clause body reaches codegen cleanly.
#[test]
fn multi_sig_cross_arity_no_poly_callee_runs_green_fence() {
    let run = run_prims(
        "(import [primitives [Pure]])\n\
         (defn build ([n] (build n 0)) \
                     ([n acc] (if (eq-i64 n 0) acc \
                         (build (sub-i64 n 1) (add-i64 acc n)))))\n\
         (defn main [] (Pure (build 3)))\n",
    );
    assert!(
        run.status.code() == Some(6),
        "the same multi-sig cross-arity `build` with NO poly callee (`(add-i64 \
         acc n)`) MUST run to 6 — isolating the poly callee as D3's other \
         load-bearing element; got exit {:?}:\n{}{}",
        run.status.code(),
        run.stdout,
        run.stderr
    );
}
