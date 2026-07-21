// impl_redefinition_dispatch.rs — re-`impl` hot-reload in a live REPL session.
//
// The semantics are SETTLED: spec/05-definitions.md §5.4.5 [S115] rules that
// re-entering an `impl` for a (trait, target-type) pair that already has an
// implementation **replaces** it — subsequent dispatch uses the NEW method
// bodies, exactly as re-entering a `defn` hot-reloads a function — and that an
// implementation MUST NOT silently ignore a re-`impl`.
//
// History: these cells were born as ONE polarity-safe pin (S114, `/repl`
// Phase-6b probe) written while the semantics were an open user question — it
// passed if EITHER the new impl dispatched OR a not-replaced notice appeared.
// The ruling landed (§5.4.5 [S115]) and the fixes landed with it (S115 W6
// `src/worker.rs::derive_codegen_batch` enrolls the impl's mangled method `Def`s
// into the forced batch; S115 W6b widens that enrollment to the trait-wide
// prefix). Per FIXME 0790 the disjunction is now RETIRED: a disjunctive pin also
// passes a regression back to silent-ignore, which is precisely the behaviour
// §5.4.5's last sentence names as a defect.
//
// Every cell here is multi-turn REPL by necessity — "the previous impl in a live
// session" has no `--run` or `--link` expression.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn repl(transcript: &str) -> String {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(transcript)
        .output();
    format!("{}{}", out.stdout, out.stderr)
}

fn count(haystack: &str, needle: &str) -> usize {
    haystack.matches(needle).count()
}

// The ruled branch (FIXME 0790 sharpening of the S114 polarity-safe pin): after a
// same-type re-`impl`, dispatch MUST use the NEW body — and MUST keep doing so on
// a THIRD re-impl, so hot-reload is not a one-shot. The stale-value count is
// asserted exactly (12 appears once, from the pre-re-impl dispatch only): the
// disjunctive predecessor would have passed a silent-ignore regression, and a
// bare `contains("7")` would pass even if the old body still dispatched.
// spec: spec/05-definitions.md §5.4.5 — Implementation Semantics (redefinition is
// hot-reload; an implementation MUST NOT silently ignore a re-`impl`).
// defect: class=silent-accept locus=src/worker.rs::derive_codegen_batch found=S114 owner=/dev
#[test]
fn reimpl_same_type_hot_reloads_dispatch() {
    let out = repl(
        "(deftype Box (Bx [:Int v]))\n\
         (deftrait Sizeable (size [x] Int))\n\
         (impl Sizeable Box (defn size [x] 12))\n\
         (size (Bx 0))\n\
         (impl Sizeable Box (defn size [x] 7))\n\
         (size (Bx 0))\n\
         (impl Sizeable Box (defn size [x] 99))\n\
         (size (Bx 0))\n",
    );
    assert!(
        out.contains(":primitives/Int 7"),
        "the FIRST re-impl MUST hot-reload dispatch to 7 (§5.4.5); got:\n{out}"
    );
    assert!(
        out.contains(":primitives/Int 99"),
        "a THIRD `impl` MUST also take — hot-reload is not a one-shot; got:\n{out}"
    );
    assert_eq!(
        count(&out, ":primitives/Int 12"),
        1,
        "the original body (12) MUST dispatch exactly ONCE — before the re-impl. \
         A second occurrence means the re-impl was silently ignored and the FIRST \
         implementation is still dispatching (§5.4.5's named defect); got:\n{out}"
    );
}

// 0791 — the explicit→DEFAULT revert. A re-`impl` that OMITS a method the prior
// impl overrode MUST fall back to the trait's DEFAULT body (§5.4.5 "replaces the
// previous implementation" + §7.1.5 default synthesis), not keep dispatching the
// stale override. Before the S115 W6b fix the W6 enrollment iterated
// `impl_.methods` — the methods the NEW impl explicitly provides — so an omitted
// method was never enrolled and `weight` kept answering the stale 55.
//
// Read this cell with the one below it: the REVERSE direction (default → explicit
// override) worked even while this was broken, which is what localised the fault.
// spec: spec/05-definitions.md §5.4.5 — Implementation Semantics (a re-`impl`
// REPLACES the previous implementation; an omitted method reverts to the default).
// defect: class=silent-accept locus=src/worker.rs::derive_codegen_batch — per-method `{trait}.{method}$` enrollment could not reach a method the re-impl omits; widened to the trait-wide `{trait}.` prefix found=S115 owner=/dev
#[test]
fn reimpl_omitting_a_method_reverts_it_to_the_trait_default() {
    let out = repl(
        "(deftype Box (Bx [:Int v]))\n\
         (deftrait Sizeable (size [x] Int) (weight [x] Int 100))\n\
         (impl Sizeable Box (defn size [x] 12) (defn weight [x] 55))\n\
         (weight (Bx 0))\n\
         (impl Sizeable Box (defn size [x] 7))\n\
         (weight (Bx 0))\n\
         (size (Bx 0))\n",
    );
    assert!(
        out.contains(":primitives/Int 100"),
        "after a re-impl that OMITS `weight`, dispatch MUST revert to the trait \
         DEFAULT (100) — the prior impl's override does not survive a replacement \
         that does not provide it (§5.4.5); got:\n{out}"
    );
    assert_eq!(
        count(&out, ":primitives/Int 55"),
        1,
        "the stale override (55) MUST dispatch exactly ONCE — before the re-impl. \
         A second occurrence is the 0791 defect: the omitted method was never \
         re-enrolled and the stale override survived the replacement; got:\n{out}"
    );
    assert!(
        out.contains(":primitives/Int 7"),
        "the method the re-impl DOES provide must still hot-reload (7) — the \
         default-revert fix must not cost the explicit→explicit case; got:\n{out}"
    );
}

// The full CYCLE — default → override → default — in one session. Neither
// direction is a special case of the other: the first transition adds a mangled
// method `Def` where a synthesized default stood, the second removes one and must
// re-stage the default. Pinning the cycle (rather than each leg in its own
// session) is what catches an enrollment that is correct once and then latches.
// spec: spec/05-definitions.md §5.4.5 — Implementation Semantics (redefinition is
// hot-reload, in both directions, repeatedly).
// defect: class=silent-accept locus=src/worker.rs::derive_codegen_batch found=S115 owner=/dev
#[test]
fn reimpl_default_then_override_then_default_cycles() {
    let out = repl(
        "(deftype Box (Bx [:Int v]))\n\
         (deftrait Sizeable (size [x] Int) (weight [x] Int 100))\n\
         (impl Sizeable Box (defn size [x] 1))\n\
         (weight (Bx 0))\n\
         (impl Sizeable Box (defn size [x] 2) (defn weight [x] 55))\n\
         (weight (Bx 0))\n\
         (impl Sizeable Box (defn size [x] 3))\n\
         (weight (Bx 0))\n\
         (size (Bx 0))\n",
    );
    assert_eq!(
        count(&out, ":primitives/Int 100"),
        2,
        "the trait default (100) MUST dispatch TWICE — once before the override is \
         introduced and once after it is dropped again. One occurrence means a leg \
         of the cycle latched (either the override never took, or it survived the \
         revert); got:\n{out}"
    );
    assert_eq!(
        count(&out, ":primitives/Int 55"),
        1,
        "the override (55) MUST dispatch exactly once — while it is the live impl; \
         got:\n{out}"
    );
    assert!(
        out.contains(":primitives/Int 3"),
        "`size` must be on its THIRD body by the end of the cycle; got:\n{out}"
    );
}

// NEGATIVE (FIXME 0790 half 2) — a re-`impl` whose body changes the method's TYPE
// is REJECTED at the conformance seam. §5.4.5: the re-`impl` carries the same-type
// constraint, so a non-conforming re-`impl` "is rejected exactly as any other
// non-conforming impl". Three things must hold together, and the third is the one
// a lone error-message assertion would miss: nothing is staged, so the PRIOR impl
// keeps dispatching.
// spec: spec/05-definitions.md §5.4.5 — Implementation Semantics (a re-`impl` whose
// methods do not type-check against the trait signature is rejected).
#[test]
fn reimpl_neg_type_changing_body_rejected_and_prior_impl_keeps_dispatching() {
    let out = repl(
        "(deftype Box (Bx [:Int v]))\n\
         (deftrait Sizeable (size [x] Int))\n\
         (impl Sizeable Box (defn size [x] 12))\n\
         (size (Bx 0))\n\
         (impl Sizeable Box (defn size [x] \"hi\"))\n\
         (size (Bx 0))\n",
    );
    assert!(
        out.contains("type mismatch"),
        "a re-impl whose body changes the method's type MUST be rejected at the \
         conformance seam, not silently confirmed (§5.4.5); got:\n{out}"
    );
    assert!(
        out.contains("primitives/String"),
        "the rejection MUST name the conflicting type so the user can see WHICH \
         conformance failed; got:\n{out}"
    );
    assert_eq!(
        count(&out, ":primitives/Int 12"),
        2,
        "the PRIOR impl MUST keep dispatching (12) after the rejected re-impl — a \
         rejected re-impl stages nothing, so both dispatches answer 12. Fewer than \
         two means the failed re-impl damaged the live implementation; got:\n{out}"
    );
    assert!(
        !out.contains(":primitives/String"),
        "the rejected body MUST NOT dispatch — no `:primitives/String` result may \
         appear; got:\n{out}"
    );
}
