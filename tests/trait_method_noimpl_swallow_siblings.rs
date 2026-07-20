// trait_method_noimpl_swallow_siblings.rs — F-D2-11 / F-D2-12 (S114 W3 disposition,
// s114-test-plan §3.8; the two surviving `try_resolve_trait_method` no-impl swallow
// siblings from the W2 review Important-3).
//
// Both sites repeat the exact shape whose CALL-position instance was the F-D2-10
// root cause (the W2 settlement re-attempt SWALLOWED the located no-impl `Err` via
// `if let Ok(Some(..))`). Same `try_resolve_trait_method`, same discarded `Err`:
//
//   P1 — infer.rs::resolve_value_position_trait_methods (~1274): a trait method used
//        as a first-class VALUE (let-binding / HOF arg) whose concrete types have NO
//        impl. The located no-impl `Err` is dropped and the Var falls through to the
//        primitive-name fallback.
//   P2 — program/mono_collect.rs::resolve_auto_curry re-attempt (~768): a partially
//        applied trait method whose late-pinned types have no impl.
//
// PROBE OUTCOMES (verified /testing 2026-07-20, ×3 modes):
//   P1 — DEMONSTRATED (stronger than the plan anticipated): the value-position path
//        does NOT merely name the method over the trait — it WRONG-ACCEPTS. `=` on a
//        no-`Eq`-impl ADT silently resolves to the primitive `eq` fallback and
//        returns `false`, while the DIRECT call correctly rejects with a located
//        error naming `Eq`. → F-D2-11 RED cells authored (CA-1 standard: a located
//        typecheck-family error naming the OWNING trait, uniform ×3 modes).
//   P2 — CONFORMANT for every reachable shape (fully-applied, HOF-arg, returned,
//        let-value, container): all produce the correct located `Eq` no-impl error.
//        → F-D2-12 authored as a BORN-GREEN fence; the SW-1 sweep records the site as
//        justified-benign WITH this fence as evidence. See the P2 note below for the
//        one shape (a GENERIC partial) that reaches mono_collect's late-pinning — it
//        is broken WHOLESALE at codegen (fails for the impl-PRESENT control too), a
//        SEPARATE defect that cannot isolate this swallow (reported to /qa).
//
// F-D2-11 flips with the W7 /dev(typecheck) rider (behind MS-P7, ahead of 0590).
// Free-standing except the TestStandard prelude (which supplies the `Eq` trait +
// its Int/Float/Bool/String impls — `Widget` has NONE, by construction).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// A no-`Eq`-impl ADT (TestStandard's `Eq` covers Int/Float/Bool/String only).
const WIDGET: &str = "(deftype Widget [:Int w])\n";

fn run(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .run("user.cl")
        .user(src)
        .output()
}

fn link(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .link("user.cl")
        .user(src)
        .output()
}

fn repl(stdin: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin(stdin)
        .output()
}

// True iff the output carries the located no-impl diagnostic naming the OWNING
// trait `Eq` (the CA-1 / §7.11.2(c) standard).
fn names_eq_no_impl(out: &helpers::e2e::CrOutput) -> bool {
    let c = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    c.contains("no impl of trait") && c.contains("eq")
}

// ---- F-D2-11 — P1 value-position no-impl WRONG-ACCEPT (RED ×3 modes) -------------

// `(let [eq =] (eq (Widget 1) (Widget 2)))` binds the trait method `=` as a VALUE
// then applies it to two `Widget`s, which have NO `Eq` impl. Per §7.11.2(c) this
// MUST be a located typecheck error naming the owning trait `Eq`.
//
// RED at HEAD: `resolve_value_position_trait_methods` swallows the located no-impl
// `Err` (`if let Ok(Some(..))`), the Var keeps no resolution, and it falls through
// to the primitive `eq` fallback — the program compiles clean and returns `false`
// (a WRONG-ACCEPT; `(if (f) 7 8)` → exit 8). GREEN twin: the DIRECT call below,
// which rejects correctly with the same fault. Failing-not-ignored.
// spec: spec/07-traits.md §7.11.2 — a no-impl dispatch is a located error naming the owning trait.
// defect: class=wrong-accept locus=crates/cranelisp-typecheck/src/infer.rs:1274 resolve_value_position_trait_methods swallows the located no-impl Err (if let Ok(Some(..))) then wrong-accepts via the primitive-name fallback found=S114 owner=/dev
#[test]
fn value_position_trait_method_no_impl_wrong_accepts_neg() {
    let src = format!(
        "{WIDGET}(defn f [] (let [eq =] (eq (Widget 1) (Widget 2))))\n\
         (defn main [] (Pure (if (f) 7 8)))\n"
    );
    let out = run(&src);
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        names_eq_no_impl(&out),
        "`=` in VALUE position applied to two no-`Eq`-impl `Widget`s MUST be a \
         located error naming the owning trait `Eq` (§7.11.2(c)) — today the \
         value-position swallow drops the no-impl `Err` and WRONG-ACCEPTS via the \
         primitive `eq` fallback (returns false, exit {:?}); got:\n{c}",
        out.status.code()
    );
}

// P1 — REPL mode face. `(let [eq =] (eq (Widget 1) (Widget 2)))` at the REPL.
// RED at HEAD: echoes `:primitives/Bool false` (the wrong-accept) instead of a
// located `Eq` no-impl error. Mode-uniformity guard for the value-position swallow.
// spec: spec/07-traits.md §7.11.2 — no-impl dispatch is a located error (REPL face).
// defect: class=wrong-accept locus=crates/cranelisp-typecheck/src/infer.rs:1274 value-position no-impl swallow (REPL face) found=S114 owner=/dev
#[test]
fn value_position_trait_method_no_impl_wrong_accepts_repl_neg() {
    let out = repl(&format!("{WIDGET}(let [eq =] (eq (Widget 1) (Widget 2)))\n"));
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        names_eq_no_impl(&out),
        "at the REPL, `=` in value position on two no-`Eq`-impl `Widget`s MUST \
         report a located `Eq` no-impl error — today it echoes `:primitives/Bool \
         false` (wrong-accept via the primitive fallback); got:\n{c}"
    );
}

// P1 — `--link` mode face. Linking the value-position program MUST fail with the
// located `Eq` no-impl error. RED at HEAD: it links clean (wrong-accept), no error.
// spec: spec/07-traits.md §7.11.2 — no-impl dispatch is a located error (`--link`).
// defect: class=wrong-accept locus=crates/cranelisp-typecheck/src/infer.rs:1274 value-position no-impl swallow (--link face) found=S114 owner=/dev
#[test]
fn value_position_trait_method_no_impl_wrong_accepts_link_neg() {
    let src = format!(
        "{WIDGET}(defn f [] (let [eq =] (eq (Widget 1) (Widget 2))))\n\
         (defn main [] (Pure (if (f) 7 8)))\n"
    );
    let out = link(&src);
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        names_eq_no_impl(&out),
        "`--link` of the value-position no-impl program MUST fail with a located \
         `Eq` no-impl error — today it links clean (wrong-accept); got:\n{c}"
    );
}

// P1 GREEN twin — the DIRECT call (the isolating control). `(= (Widget 1) (Widget
// 2))` at the SAME no-impl fault, but in CALL position — which resolves through the
// (W2-fixed) call path that PROPAGATES the located no-impl `Err`. Correctly rejects
// with `no impl of trait prelude/Eq for type user/Widget`. GREEN today; must stay
// green. The contrast with the RED cells isolates the VALUE position (not no-impl
// detection generally) as the swallow seam.
// spec: spec/07-traits.md §7.11.2 — a direct no-impl call is a located error naming the trait.
#[test]
fn direct_call_trait_method_no_impl_rejects_naming_trait_green() {
    let out = run(&format!(
        "{WIDGET}(defn main [] (Pure (if (= (Widget 1) (Widget 2)) 7 8)))\n"
    ));
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        names_eq_no_impl(&out),
        "a DIRECT call `(= (Widget 1) (Widget 2))` on a no-`Eq`-impl ADT MUST reject \
         with a located error naming the owning trait `Eq` (the call path propagates \
         the no-impl Err — the isolating green twin for the value-position RED); \
         got:\n{c}"
    );
}

// ---- F-D2-12 — P2 auto-curry no-impl (BORN-GREEN fence — probe found CONFORMANT) --

// `((= (Widget 1)) (Widget 2))` — the trait method `=` PARTIALLY applied then
// completed, on two no-`Eq`-impl `Widget`s. Per §7.11.2(c) this MUST be a located
// error naming `Eq`. PROBE RESULT: already CONFORMANT — the auto-curry typing path
// in `infer.rs` resolves/rejects the concrete types before mono_collect's re-attempt
// is reached, so the located `Eq` error IS produced. Pinned as a born-green fence
// (§3.8: a conformant swallow closes as justified-benign ONLY with a fence as
// evidence); it must stay green through the W7 rider.
//
// NOTE (/testing, verified 2026-07-20 — reported to /qa): the ONLY shape that
// reaches the mono_collect.rs:768 late-pinning swallow — a GENERIC partial `(defn g
// [x] (= x))` instantiated at `Widget` — is broken WHOLESALE at codegen
// ("fn-as-value wrapper for '=' reached codegen with no GOT-slot carrier"), and it
// fails identically for the impl-PRESENT `Int` control. That is a SEPARATE
// carrier-loss defect, not this swallow, and cannot isolate P2 — so P2 has no
// demonstrable e2e gap and stays a fence.
// spec: spec/07-traits.md §7.11.2 — an auto-curried no-impl application is a located
// error naming the owning trait.
#[test]
fn auto_curry_trait_method_no_impl_rejects_naming_trait_green() {
    let out = run(&format!(
        "{WIDGET}(defn main [] (Pure (if ((= (Widget 1)) (Widget 2)) 7 8)))\n"
    ));
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        names_eq_no_impl(&out),
        "an auto-curried `((= (Widget 1)) (Widget 2))` on a no-`Eq`-impl ADT MUST \
         reject with a located error naming `Eq` — this ALREADY holds (the \
         mono_collect swallow is unreachable for this shape); fence, must stay \
         green; got:\n{c}"
    );
}

// P2 — REPL mode face of the auto-curry fence. GREEN today (conformant); must stay
// green. Pairs the `--run` fence so a W7 change that regresses only one mode is
// caught.
// spec: spec/07-traits.md §7.11.2 — auto-curried no-impl is a located error (REPL).
#[test]
fn auto_curry_trait_method_no_impl_rejects_naming_trait_repl_green() {
    let out = repl(&format!("{WIDGET}((= (Widget 1)) (Widget 2))\n"));
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        names_eq_no_impl(&out),
        "at the REPL, `((= (Widget 1)) (Widget 2))` on a no-`Eq`-impl ADT MUST \
         report a located `Eq` no-impl error (conformant fence); got:\n{c}"
    );
}

// P2 — `--link` mode face of the auto-curry fence. Linking MUST fail with the
// located `Eq` no-impl error. GREEN today; must stay green.
// spec: spec/07-traits.md §7.11.2 — auto-curried no-impl is a located error (`--link`).
#[test]
fn auto_curry_trait_method_no_impl_rejects_naming_trait_link_green() {
    let out = link(&format!(
        "{WIDGET}(defn main [] (Pure (if ((= (Widget 1)) (Widget 2)) 7 8)))\n"
    ));
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        names_eq_no_impl(&out),
        "`--link` of the auto-curried no-impl program MUST fail with a located `Eq` \
         no-impl error (conformant fence); got:\n{c}"
    );
}
