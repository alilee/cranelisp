// multi_sig_base_mono_carrier_loss.rs — R2 cross-crate repro (S112 W4).
//
// A call to a MULTI-SIGNATURE base from inside a body that gets MONOMORPHISED
// loses its `resolved_target` carrier: the multi-sig-dispatch instance
// (`h$Int`) reaches codegen with no carrier, and the backend keyed-consumer
// hard-fails —
//   `codegen error … call to 'h$Int' reached codegen with no resolved_target
//    carrier (S110 W1 keyed read; backend-keyed-consumer.md §1.2)`.
//
// PRE-EXISTING, NOT leg-(a): surfaced as the W2.1 /review R2 residual on the
// leg-(a) change-set (`b5fa3f14`), and the /review record states it fails
// identically pre-leg-(a) — leg (a) neither introduced nor widened it. The
// caller `ga` here is a plain SINGLE-signature genuinely-poly fn (not a
// multi-sig clause), so the defect is NOT in the leg-(a) multi-sig-clause
// caller machinery; it is in the multi-sig-BASE-callee dispatch carrier reached
// from any monomorphised body. The control below (single-sig `h`) is GREEN,
// isolating the multi-sig base as the load-bearing element.
//
// ISOLATION (tests/CLAUDE.md §"Isolating Cross-Crate Failures"): the error is
// EMITTED at codegen (backend), but the missing datum — the `resolved_target`
// carrier for the multi-sig-base dispatch call `(h 1)` inside the monomorphised
// `ga$Int` body — is a typecheck→backend keyed carrier the PRODUCER (typecheck)
// must write and the backend keyed-consumer reads. As far as the repro shows
// the carrier is never produced for a multi-sig-base call inside a mono harvest,
// so the backend's keyed read misses. Likely producer-side (typecheck), but
// full attribution is /qa's — see the `// defect:` line. Reduced minimally:
// `h` MUST be multi-sig (single-sig `h` is GREEN, the control) and `ga` MUST be
// genuinely-poly (a concrete caller does not monomorphise and keeps the
// carrier). The 1-arg clause of `h` is CONCRETE (`(add-i64 x 1)`): with a poly
// 1-arg clause the residual var bubbles up to `ga`'s ambiguity gate FIRST and
// masks the carrier-loss codegen path.

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

// The multi-sig base. The 1-arg clause `([x] (add-i64 x 1))` is concrete
// `(Fn [Int] Int)`; the 2-arg clause is present only to make `h` a multi-sig
// base (so its dispatch carries a `resolved_target`). `(h 1)` = 2.
const H_MULTI: &str = "(defn h ([x] (add-i64 x 1)) ([a b] a))";

// R2 — a multi-sig-base call inside a monomorphised body loses its
// `resolved_target` carrier. `ga` is a genuinely-poly single-sig fn (param `x`
// unused → `(Fn [a] Int)`); `(ga 5)` monomorphises `ga$Int`, and inside that
// harvest the multi-sig-base call `(h 1)` → `h$Int` reaches codegen with no
// carrier. Spec-correct: `(ga 5)` = 2. RED until the carrier-loss is fixed.
//
// ATTRIBUTION (/qa ruling 1, 2026-07-18): PRODUCER-side, owner /dev(typecheck).
// The backend keyed-consumer is a LOUD miss working as designed (no soft
// fallback — the soft-fallback arm is the named S110-3 REJECT criterion), so
// the backend surfacing the error does NOT make it the owner. The producer
// obligation: `resolved_target` is never written for a multi-sig-BASE dispatch
// call inside a MONOMORPHISED instance body (`ga$Int` is minted at pass-4
// instantiation, after the carrier-writing pass; nobody re-derives call
// resolutions for the minted body). Fix shape is P26-constrained: derive the
// instance body's carriers ON DEMAND from settled post-drain state at mint time
// (the §11.3.2 six-carrier single-sourcing seam), never patch-after-record.
//
// MODE-UNIFORMITY (ruling 1, folded here per /qa): the REPL-vs-`--run`
// gate-order divergence is ONE root, ONE row — a FACE of the same carrier miss
// (which downstream diagnostic surfaces first). The FIXING change-set MUST
// extend this flip with an AG-2-class mode-uniformity assertion (REPL ≡ --run ≡
// --link on the diagnostic core); a second RED for the same root would
// double-count. If any divergence SURVIVES the carrier fix, it earns its own
// row + attribution then.
// spec: spec/05-definitions.md §5.1.2 — multi-signature dispatch; a resolved
// dispatch target reaches codegen (the §11.6 resolved_targets carrier).
// defect: class=carrier-loss locus=multi-sig-base dispatch resolved_target carrier (produced typecheck-side, backend-keyed-consumer.md §1.2) found=S112 owner=/dev
#[test]
fn multi_sig_base_call_in_monomorphised_body_keeps_resolved_target() {
    let out = repl_prims(&format!("{H_MULTI}\n(defn ga [:a x] (h 1))\n(ga 5)\n"));
    let c = format!("{}{}", out.stdout, out.stderr);
    // The load-bearing RED: the multi-sig-base call `(h 1)` inside `ga$Int` MUST
    // reach codegen WITH its resolved_target carrier — never leak the
    // `no resolved_target carrier` codegen failure.
    assert!(
        !c.contains("resolved_target carrier") && !c.contains("no resolved_target"),
        "the multi-sig-base call `(h 1)` inside the monomorphised `ga$Int` body \
         MUST keep its resolved_target carrier — it MUST NOT reach codegen with \
         `no resolved_target carrier`; got:\n{c}"
    );
    // Positive: `(ga 5)` = 2 (h(1) = 1+1 = 2; ga's unused poly param is dropped).
    assert!(
        out.stdout.contains(":primitives/Int 2"),
        "`(ga 5)` = `(h 1)` = 1 + 1 = 2 (ga's poly param `x` is unused); got:\n{}",
        out.stdout
    );
}

// Control fence: with `h` SINGLE-signature the identical `ga` monomorphises
// cleanly and `(ga 5)` = 2 — GREEN today. This isolates the MULTI-SIG base as
// the load-bearing element of R2 (the carrier only exists, and is only lost,
// for a multi-sig dispatch). If this ever goes RED the defect has widened past
// the multi-sig-base carrier.
// spec: spec/05-definitions.md §5.1.2 — a single-sig base call inside a
// monomorphised body is an ordinary call (no multi-sig dispatch carrier).
#[test]
fn single_sig_base_call_in_monomorphised_body_is_green_control() {
    let out = repl_prims(
        "(defn h1 [x] (add-i64 x 1))\n\
         (defn ga [:a x] (h1 1))\n\
         (ga 5)\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("resolved_target") && out.stdout.contains(":primitives/Int 2"),
        "with a SINGLE-sig base `h1`, `(ga 5)` = 2 with no carrier error (the \
         control isolating the multi-sig base as R2's load-bearing element); \
         got:\n{c}"
    );
}
