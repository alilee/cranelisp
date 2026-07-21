//! `program/mono_collect.rs` sub-topic — multi-sig dispatch through the mono
//! engine: the D3/MC-X4 settlement-harvest windows, template-clause
//! instantiation, and the self-call/back-flow legs
//! (`design/typecheck/monomorphisation.md` §11.3/§11.8).

use super::*;



// §11.8.3 leg D3 — a poly callee (`idpoly`) reached ONLY from a MULTI-SIG
// clause body MUST have its concrete mono instance minted. Pre-fix the
// multi-sig defn was filtered out of the mono-collect (`collect_single_sig_defns`
// drops it; `Defn::body()` panics on it), so `idpoly$Int` was never harvested
// and the call reached codegen as `undefined function`. The `MultiSig` harvest
// family scans the clause bodies post-Phase-A.
#[test]
fn multi_sig_clause_body_poly_callee_monomorphised_d3() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn idpoly [x] x)\n\
         (defn build ([n] (build n 0)) \
                     ([n acc] (if (eq-i64 n 0) acc \
                         (build (sub-i64 n 1) (add-i64 acc (idpoly n))))))",
    );
    assert!(
        !symbol_names_containing(&tc, "idpoly$").is_empty(),
        "`idpoly`'s Int mono instance MUST be minted from `build`'s multi-sig \
         clause body (leg D3); current-module symbols: {:?}",
        symbol_names_containing(&tc, "idpoly"),
    );
}

// MC-X4 (S114 W3) — the SINGLE-SIG consumer face of the settlement harvest. A
// poly callee (`mycount : (Vec a) -> Int`) consuming a MULTI-SIG fn's bare
// `(Vec Int)` return MUST have its ground mono instance `mycount$…` minted. The
// consumer's call `(mycount (build 3))` lives in a SINGLE-sig body (`top`), so
// the pre-drain single-sig pass-4 saw its arg — the multi-sig call's result —
// as a residual `Var` (settled only in the drain) and SKIPPED it. The
// post-settlement single-sig re-harvest (finalize.rs, P26) re-derives the arg
// through the settled subst → concrete → mints. Fail-on-revert: without the
// re-harvest no `mycount$` instance is minted (the e2e leak is at codegen —
// typecheck accepts — so this asserts the MINT, not a reject).
#[test]
fn single_sig_consumer_of_multi_sig_return_monomorphised_mc_x4() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn mycount [v] (vec-len v))\n\
         (defn build ([n] (build n [0])) \
                     ([n acc] (if (eq-i64 n 0) acc \
                         (build (add-i64 n -1) (vec-push acc n)))))\n\
         (defn top [] (mycount (build 3)))",
    );
    assert!(
        !symbol_names_containing(&tc, "mycount$").is_empty(),
        "the poly consumer `mycount` of the multi-sig `build`'s `(Vec Int)` \
         return MUST have its ground mono instance minted at the settlement \
         re-harvest (MC-X4); current-module symbols: {:?}",
        symbol_names_containing(&tc, "mycount"),
    );
}

// MC-X4b (S114 W3) — the untyped-ADT-field face (same root as MC-X4). A `Box`
// with an UNTYPED field, built by a multi-sig `build` and consumed by a poly
// `unwrap`, grounds its field to `Int` only post-drain; the consumer's `unwrap`
// instance must mint at the settlement re-harvest. Fail-on-revert: no `unwrap$`
// instance minted (codegen `undefined function` in e2e).
#[test]
fn untyped_adt_field_consumer_of_multi_sig_return_monomorphised_mc_x4b() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(deftype Box (MkBox [v]))\n\
         (defn unwrap [b] (match b [(MkBox v) v]))\n\
         (defn build ([n] (build n (MkBox 0))) \
                     ([n b] (if (eq-i64 n 0) b \
                         (build (add-i64 n -1) (MkBox (add-i64 n 40))))))\n\
         (defn top [] (unwrap (build 3)))",
    );
    assert!(
        !symbol_names_containing(&tc, "unwrap$").is_empty(),
        "the poly consumer `unwrap` over the untyped `Box` field from a \
         multi-sig return MUST have its ground mono instance minted at the \
         settlement re-harvest (MC-X4b); current-module symbols: {:?}",
        symbol_names_containing(&tc, "unwrap"),
    );
}

// MC-X5 (S114 W3) — the overload gate keys on the RAW callee name, so a
// current-module-qualified multi-sig SELF-call (`(test/msig …)` inside module
// `test`) missed `state.overloads` (keyed bare) and wrong-rejected. The gate
// now normalizes the self-qualified spelling to the bare identity (§8.6.6 /
// 0655) before the dispatch lookups. `check_src` panics on the wrong-reject, so
// a clean return IS the assertion (fail-on-revert: the qualified self-call
// rejects).
#[test]
fn self_qualified_multi_sig_self_call_normalizes_at_overload_gate_mc_x5() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn msig ([n] (test/msig n 0)) \
                    ([n acc] (if (eq-i64 n 0) acc \
                        (msig (add-i64 n -1) (add-i64 acc n)))))\n\
         (defn top [] (msig 3))",
    );
    // The dispatch path was taken (not a fallthrough): `msig`'s concrete clause
    // variants are mangled + registered. The qualified self-call inside msig's
    // clause body resolved to the same bare `msig` overload as the bare twin.
    assert!(
        !symbol_names_containing(&tc, "msig$").is_empty(),
        "the self-qualified multi-sig self-call MUST normalize to the bare \
         identity and dispatch through the overload machinery (MC-X5) — \
         `msig$…` clause variants registered; current-module symbols: {:?}",
        symbol_names_containing(&tc, "msig"),
    );
    // No doubled-qualifier `test/msig` spelling leaked into any registered name.
    assert!(
        symbol_names_containing(&tc, "test/msig").is_empty(),
        "no `test/msig` doubled-qualifier mangle may leak from the normalized \
         self-call; got: {:?}",
        symbol_names_containing(&tc, "test/msig"),
    );
}

// PS-SH1 (S114 W3) — the value-position mirror of Ruling 5. A `let` shadows a
// multi-sig base `h` with a local closure and uses the shadowed name in VALUE
// position (HOF arg). The value-gate MUST consult local scope first and resolve
// to the LOCAL closure, NOT wrong-reject "multi-sig function 'h' cannot be used
// as a value". `check_src` panics on the wrong-reject → clean return is the
// assertion (fail-on-revert: the value-ref rejects).
#[test]
fn let_shadowed_multi_sig_base_value_ref_resolves_to_local_ps_sh1() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn h ([x] (add-i64 x 1)) ([a b] a))\n\
         (defn use-hof [f] (f 5))\n\
         (defn g [] (let [h (fn [y] 100)] (use-hof h)))",
    );
}

// PS-SH1 control — an UNSHADOWED multi-sig base used as a bare value STILL
// rejects (the local-scope-first gate must not weaken the base reject). Guards
// against the fix over-reaching into an accept of `h`-as-value.
#[test]
fn unshadowed_multi_sig_base_as_value_still_rejects_ps_sh1_control() {
    let mut tc = tc_with_prims();
    let sexps = cranelisp_frontend::parse(
        "(defn h ([x] (add-i64 x 1)) ([a b] a))\n\
         (defn use-hof [f] (f 5))\n\
         (defn g [] (use-hof h))",
    )
    .expect("parse");
    let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
    let err = tc.check_program_self(&program);
    assert!(
        err.is_err(),
        "an UNSHADOWED multi-sig base `h` used as a bare value MUST still \
         reject (the PS-SH1 local-scope-first gate must not accept the base \
         itself as a value)"
    );
}

// §11.8.3 leg R2 — a call to a MULTI-SIG BASE (`h`) inside a monomorphised
// body (`ga$Int`) MUST get its `resolved_target` carrier. Pre-fix the inner
// scans handled only constrained self-recursion and pure-parametric hops —
// never an overloaded-base dispatch — so `(h 1)` reached codegen with no
// carrier (`class=carrier-loss`). `resolve_inner_multi_sig_dispatch` writes it.
#[test]
fn multi_sig_base_dispatch_in_mono_body_carrier_r2() {
    let mut tc = tc_with_prims();
    // `(add-i64 (h 1) 0)` pins `(h 1)`'s node to Int (so a single-cluster
    // batch mono of `ga$Int` settles cleanly), while `(h 1)` is still a
    // multi-sig-BASE dispatch inside the monomorphised body — the exact
    // carrier R2 must write.
    check_src(
        &mut tc,
        "(defn h ([x] (add-i64 x 1)) ([a b] a))\n\
         (defn ga [:a x] (add-i64 (h 1) 0))\n\
         (defn use-ga [] (ga 5))",
    );
    let view = mono_instance_view_containing(&tc, "ga$");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    // The `(h 1)` dispatch inside `ga$Int` carries its resolved_target at the
    // APPLY span (SigDispatch), naming the concrete clause `h$Int` — not absent
    // (the carrier-loss shape the backend keyed read would hard-fail on).
    let has_h_dispatch = targets.iter().any(|(l, fq)| {
        l == "@apply"
            && matches!(fq, Some(fq) if fq.symbol.as_ref().contains("h$"))
    });
    assert!(
        has_h_dispatch,
        "the multi-sig-base call `(h 1)` inside the monomorphised `ga$Int` body \
         MUST carry a resolved_target to the concrete clause `h$Int` at its \
         Apply span (leg R2); collected: {targets:?}"
    );
}

// §11.8.3 leg R2 — W2a /review Important 1a (TEMPLATE-select). A multi-sig
// dispatch inside a mono body that selects a genuinely-POLY clause (`(h 1 2)`
// → the `([a b] a)` `$Var+Var` template) MUST monomorphise that clause to a
// CONCRETE instance and dispatch to it — never write the slot-less `$Var+Var`
// TEMPLATE mangle into the frozen view (pre-fix `undefined function:
// h$Var+Var`). The scoped drain gives R2 the full concrete/template
// bifurcation. `check_src` panics on the residual/undefined path.
#[test]
fn multi_sig_dispatch_template_clause_monomorphised_r2a() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn h ([x] (add-i64 x 1)) ([a b] a))\n\
         (defn ga [:a x] (add-i64 (h 1 2) 0))\n\
         (defn use-ga [] (ga 5))",
    );
    // The `([a b] a)` template clause, selected by `(h 1 2)`, was instantiated
    // at Int (a `h$Var+Var$…` concrete mono instance exists) — proving R2 did
    // NOT freeze the slot-less `$Var+Var` template mangle into the view.
    assert!(
        !symbol_names_containing(&tc, "h$Var+Var$").is_empty(),
        "the poly 2-arg clause selected by `(h 1 2)` MUST be monomorphised to a \
         concrete instance (leg R2, Important 1a) — never dispatched to the \
         slot-less `$Var+Var` template; symbols: {:?}",
        symbol_names_containing(&tc, "h$Var+Var"),
    );
}

// §11.8.3 leg R2 — W2a /review Important 1b (post-drain drop). A poly fn
// (`poly2`) reached ONLY from a MULTI-SIG clause body is monomorphised in the
// D3 harvest, which runs AFTER the single top-level drain. Its inner multi-sig
// dispatch `(h2 1)` defers a pending that the top-level drain has already
// taken — pre-fix it was DROPPED, leaving `(h2 1)` a residual unbound var →
// misleading residual-var wrong-reject. The scoped drain inside
// `recheck_body_for_mono` resolves it in-place. `check_src` panics on the
// residual wrong-reject, so a clean return IS the assertion.
#[test]
fn multi_sig_dispatch_in_d3_harvested_body_drained_r2b() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn h2 ([x] (add-i64 x 1)) ([a b] a))\n\
         (defn poly2 [p] (let [q (h2 1)] p))\n\
         (defn build3 ([n] (build3 n 0)) ([n acc] (poly2 acc)))\n\
         (defn use-build3 [] (build3 3))",
    );
    // poly2 was monomorphised from build3's clause body AND its inner `(h2 1)`
    // dispatch drained (the instance minted cleanly, no residual var).
    assert!(
        !symbol_names_containing(&tc, "poly2$").is_empty(),
        "poly2 reached from build3's multi-sig clause body MUST monomorphise \
         cleanly with its inner `(h2 1)` dispatch drained in-recheck (leg R2, \
         Important 1b); symbols: {:?}",
        symbol_names_containing(&tc, "poly2"),
    );
}

// W2a /review Important 2 (P24 mirror in `verify_constraints`). A constrained
// fn whose bound trait is imported METHOD-ONLY (not the trait) must
// monomorphise: `verify_constraints` roots the impl lookup at the trait's HOME
// (`fq_trait.module`, held on the constraint) via `has_impl_in_home`, NOT a
// bare re-resolve of the trait NAME in the caller's scope (`has_impl_with_state`)
// — the caller has no in-scope trait name. Pre-fix: `(wrap 1)` monomorphises
// wrap$Int → `verify_constraints` → "no impl of trait blib/Bump for type Int".
// `check_src` panics on that wrong-reject.
#[test]
fn method_only_import_constrained_fn_verify_constraints_home_rooted_d2() {
    let mut tc = tc_with_prims();
    // blib: trait Bump (method `bump`) + Int impl.
    let blib = ModuleFullPath::from("blib");
    tc.set_current_module(blib.clone());
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    register_int_returning_trait(&mut tc, "Bump", "bump");
    // user: import ONLY the method `bump` — NOT the trait `Bump`.
    let user = ModuleFullPath::from("user");
    tc.set_current_module(user.clone());
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    seed_specific_import(&mut tc, &blib, &["bump"]);
    // Submission 1 — `wrap` is a genuine constrained-poly fn (Bump a). Checked
    // in its OWN cluster so it commits constrained (a same-cluster concrete
    // call would collapse it to Int before pass-4 ever mono'd it — the batch
    // regeneralize). This mirrors the REPL multi-submission the e2e reproduces.
    check_src(&mut tc, "(defn wrap [x] (bump x))");
    // Submission 2 — `(wrap 1)` monomorphises wrap$Int → `verify_constraints`
    // checks the Bump/Int impl. Home-rooted (blib, held on the constraint), so
    // it resolves. Pre-fix: bare re-resolve of "Bump" in user scope →
    // "no impl of trait blib/Bump for type Int". `check_src` panics on it.
    check_src(&mut tc, "(defn use-int [] (wrap 1))");
    assert!(
        !symbol_names_containing(&tc, "wrap$").is_empty(),
        "wrap$Int must be minted (proving verify_constraints ran + passed \
         home-rooted); symbols: {:?}",
        symbol_names_containing(&tc, "wrap"),
    );
}

// §11.8.3 leg R1 — a CROSS-ARITY sibling self-call from a genuinely-poly
// multi-sig clause, monomorphised at a call site, MUST resolve (dispatch to
// the concrete sibling clause) rather than wrong-reject with an internal-name
// leak. `(g2 5)` monomorphises the 1-arg poly clause at Int; its body's
// `(g2 1 2)` targets the concrete 2-arg sibling. `check_src` panics on the
// wrong-reject, so a clean return IS the assertion.
#[test]
fn cross_arity_sibling_self_call_resolves_r1() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn g2 ([:a x] (g2 1 2)) ([:primitives/Int a :primitives/Int b] (add-i64 a b)))\n\
         (defn use-g2 [] (g2 5))",
    );
}

// §11.8.7 ruling 5 — the overload-gate LOCAL-SCOPE-FIRST guard. A `let`
// binding shadows a MULTI-SIG base `m1`; the shadowed call `(m1 x)` inside
// the let body MUST resolve to the LOCAL binding (an indirect call, no
// dispatch carrier), NOT enter the global overload path. On HEAD the
// `infer.rs:604` gate consulted `state.overloads` by name without checking
// local scope, so the call deferred past the drain and t1 wrong-rejected
// (`undefined variable: t1`). The `add-i64` wrapper forces t1 concrete so it
// carries a `codegen_view` to inspect. The `(m1 x)` callee `Var` must carry
// NO `resolved_target` (a local indirect call), unlike a genuine overload
// dispatch which would carry a `SigDispatch` mangle.
#[test]
fn overload_gate_skips_let_shadowed_multi_sig_base() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn m1 ([x] x) ([a b] a))\n\
         (defn t1 [x] (add-i64 (let [m1 (fn [y] y)] (m1 x)) 1))",
    );
    // t1 defined (not wrong-rejected) and concrete → has a codegen_view.
    let view = main_codegen_view_of(&tc, "t1");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    // The `(m1 x)` callee `Var m1` must resolve to the LOCAL let binding —
    // no dispatch carrier (the shadowed base is not the overload dispatch).
    let m1_carrier = targets
        .iter()
        .find(|(l, _)| l == "m1")
        .map(|(_, fq)| fq.clone());
    assert_eq!(
        m1_carrier,
        Some(None),
        "the let-shadowed `(m1 x)` callee `Var` must carry NO resolved_target \
         (it is the LOCAL `(fn [y] y)`, an indirect call — the overload gate \
         MUST NOT bypass local scope); collected: {targets:?}"
    );
}

// Fix 1 (/arch-directed) — during a mono recheck, a `(s1 x)` whose callee is a
// `let`-binding SHADOWING the base MUST record NO self-recursion dispatch: the
// frame-guarded `is_recursion_self_ref` verdict (via record_reference_target)
// left the callee carrier absent, so `record_self_recursion_dispatch` skips it.
// Pre-fix it recorded `SigDispatch{s1$Int}` on the shadowed inner call → the
// backend emitted a self-call (TCO loop → hang). The `add-i64` wrapper forces
// `s1` concrete so `(s1 5)` mints an inspectable `s1$Int`. TAIL cell.
#[test]
fn mono_recheck_shadowed_self_call_records_no_dispatch() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn s1 [x] (let [s1 (fn [y] y)] (s1 x)))\n\
         (defn use-s1 [] (add-i64 (s1 5) 0))",
    );
    let view = mono_instance_view_containing(&tc, "s1$");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    // No node in s1$Int's body may dispatch to a `s1$…` mono instance (the
    // shadowed `(s1 x)` is the LOCAL identity, an indirect call).
    let leaks_self_dispatch = targets.iter().any(|(_, fq)| {
        matches!(fq, Some(fq) if fq.symbol.as_ref().contains("s1$"))
    });
    assert!(
        !leaks_self_dispatch,
        "the let-shadowed `(s1 x)` inside `s1$Int` MUST NOT record a \
         self-recursion dispatch to `s1$Int` (Fix 1 — it is the LOCAL \
         identity); collected: {targets:?}"
    );
}

// Fix 1 non-tail sibling (/arch-required, typecheck half). Same shadow, but the
// shadowed `(s1 x)` is NOT in tail position (`(add-i64 (… (s1 x)) 1)`) — no TCO
// loop, but a mis-recorded self-dispatch would give the WRONG VALUE (call
// `s1$Int` instead of the local identity). Typecheck assertion: still no
// self-dispatch. (/testing lands the wrong-value e2e cell.)
#[test]
fn mono_recheck_shadowed_self_call_non_tail_records_no_dispatch() {
    let mut tc = tc_with_prims();
    // `(s1 x)` is bound to `r` (non-tail), keeping `s1` poly so it still
    // monomorphises to an inspectable `s1$Int`.
    check_src(
        &mut tc,
        "(defn s1 [x] (let [s1 (fn [y] y)] (let [r (s1 x)] r)))\n\
         (defn use-s1 [] (s1 5))",
    );
    let view = mono_instance_view_containing(&tc, "s1$");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    assert!(
        !targets.iter().any(|(_, fq)| matches!(fq, Some(fq) if fq.symbol.as_ref().contains("s1$"))),
        "the non-tail let-shadowed `(s1 x)` MUST NOT record a self-recursion \
         dispatch (Fix 1 non-tail cell); collected: {targets:?}"
    );
}

// Fix 2 (MC-X2) — an IMPORTED multi-sig base `h` (defined in `mlib`) called
// from `user` must dispatch AND its carrier must be keyed by the base's HOME
// module (`mlib`), not `current_module` (`user`). Pre-fix the imported base
// never entered the overload machinery → `undefined function: h`; and the
// `SigDispatch` carrier hard-coded `current_module`. The `(h 1)` Apply must
// carry a resolved_target `{mlib, h$Int}`.
#[test]
fn imported_multi_sig_base_carrier_keyed_by_home_mc_x2() {
    let mut tc = tc_with_prims();
    let mlib = ModuleFullPath::from("mlib");
    tc.set_current_module(mlib.clone());
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    check_src(&mut tc, "(defn h ([x] (add-i64 x 1)) ([a b] (add-i64 a b)))");
    let user = ModuleFullPath::from("user");
    tc.set_current_module(user.clone());
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    seed_specific_import(&mut tc, &mlib, &["h"]);
    // Simulate fresh per-cluster overload state (the real pipeline builds a
    // fresh CheckState per cluster; TestFixture reuses one, leaking `mlib`'s
    // local `h` overload into `user`'s cluster and masking the imported-base
    // rehydration path this test exercises).
    tc.state.overloads.clear();
    tc.state.resolved_overloads.clear();
    tc.state.overload_homes.clear();
    // `(add-i64 (h 1) 0)` pins use-h concrete → inspectable codegen_view.
    check_src(&mut tc, "(defn use-h [] (add-i64 (h 1) 0))");
    let view = main_codegen_view_of(&tc, "use-h");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    let home_keyed = targets.iter().any(|(l, fq)| {
        l == "@apply"
            && matches!(fq, Some(fq)
                if fq.module == mlib && fq.symbol.as_ref().contains("h$"))
    });
    assert!(
        home_keyed,
        "the imported multi-sig base call `(h 1)` MUST carry a resolved_target \
         keyed by the base's HOME module `mlib` (MC-X2, P24 storage identity — \
         NOT `user`); collected: {targets:?}"
    );
}

// Fix A (MC-X2 qualified face) — a QUALIFIED imported multi-sig call
// `(mlib/h 1)` must dispatch to the STORED mangled identity `h$Int` keyed by
// `mlib`, NOT re-derive from the written name (`mangle_sig("mlib/h",…)` =
// `mlib/h$Int` → the bad `mlib/mlib/h$Int` no-entry). The `(mlib/h 1)` Apply
// must carry `{mlib, h$Int}` — the symbol MUST NOT contain the `mlib/` prefix.
#[test]
fn imported_multi_sig_base_qualified_call_stored_identity_fix_a() {
    let mut tc = tc_with_prims();
    let mlib = ModuleFullPath::from("mlib");
    tc.set_current_module(mlib.clone());
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    check_src(&mut tc, "(defn h ([x] (add-i64 x 1)) ([a b] (add-i64 a b)))");
    let user = ModuleFullPath::from("user");
    tc.set_current_module(user.clone());
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    // Fresh per-cluster overload state (see the bare-face test).
    tc.state.overloads.clear();
    tc.state.resolved_overloads.clear();
    tc.state.overload_homes.clear();
    // Qualified reference `mlib/h` — resolves directly to the committed module
    // (no import needed).
    check_src(&mut tc, "(defn use-h [] (add-i64 (mlib/h 1) 0))");
    let view = main_codegen_view_of(&tc, "use-h");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    let good = targets.iter().any(|(l, fq)| {
        l == "@apply"
            && matches!(fq, Some(fq)
                if fq.module == mlib
                    && fq.symbol.as_ref() == "h$Int")
    });
    assert!(
        good,
        "the qualified imported call `(mlib/h 1)` MUST carry the STORED identity \
         `{{mlib, h$Int}}` (Fix A) — NOT the re-derived `mlib/h$Int` (which \
         renders `mlib/mlib/h$Int`, no entry); collected: {targets:?}"
    );
}

// Fix 1 / ruling-5 composition (/arch-flagged): §11.8.7's "during a mono
// recheck the base is not locally bound" is FALSIFIED by a let-rebinds-base
// case. A multi-sig base `m` shadowed by a `let` INSIDE a mono recheck
// (`poly$Int`) must skip BOTH the overload gate AND the self-call classifier.
// The ruling-5 gate does NOT rely on "base not locally bound" — it checks
// `env.lookup(m).is_none() || is_recursion_self_ref(m)`: here env.lookup(m) is
// Some (the let) and is_recursion_self_ref is false → gate false → the overload
// path is skipped and `(m p)` resolves to the LOCAL. `check_src` panics if it
// wrong-rejects; the mono instance's `(m p)` must carry no `m$…` dispatch.
#[test]
fn ruling5_composition_let_shadowed_multi_sig_base_in_mono_recheck() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn m ([x] x) ([a b] a))\n\
         (defn poly [p] (let [m (fn [y] y)] (m p)))\n\
         (defn use-poly [] (poly 5))",
    );
    let view = mono_instance_view_containing(&tc, "poly$");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    assert!(
        !targets.iter().any(|(_, fq)| matches!(fq, Some(fq) if fq.symbol.as_ref().contains("m$"))),
        "the let-shadowed multi-sig base call `(m p)` inside `poly$Int` MUST \
         resolve to the LOCAL (no `m$…` overload dispatch) — the ruling-5 gate \
         composes under a mono recheck even when the base IS locally bound; \
         collected: {targets:?}"
    );
}

// Fix 1 control — a GENUINE monomorphic self-recursion (no shadow) MUST still
// record its self-dispatch to the mono instance (the carrier is present via
// the frame-guarded verdict). `cnt` is poly in `x`; `(cnt 5 3)` mints
// `cnt$Int+Int` whose body's `(cnt x (sub-i64 n 1))` self-call dispatches to it
// — the fix must not disable genuine self-recursion.
#[test]
fn mono_recheck_genuine_self_recursion_still_records() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn cnt [x n] (if (eq-i64 n 0) x (cnt x (sub-i64 n 1))))\n\
         (defn use-cnt [] (cnt 5 3))",
    );
    let view = mono_instance_view_containing(&tc, "cnt$");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    assert!(
        targets.iter().any(|(_, fq)| matches!(fq, Some(fq) if fq.symbol.as_ref().contains("cnt$"))),
        "the genuine self-call `(cnt x (sub-i64 n 1))` MUST still dispatch to \
         the mono instance `cnt$Int+Int` (Fix 1 must not break genuine \
         self-recursion); collected: {targets:?}"
    );
}

// Fix B / FIXME 0653 — site 1 (pass-4 collector over a CONCRETE caller). A
// let-shadowed parametric fn `(idp n)` MUST resolve to the LOCAL — the
// name-scan collector (`collect_local_parametric_calls`) MUST NOT mint the
// top-level `idp`'s mono (its callee has no keyed carrier — the shadow gate
// declined it). Control: the UNSHADOWED call DOES mint `idp$Int`.
#[test]
fn shadowed_parametric_in_concrete_caller_no_mint_fix_b() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn idp [x] x)\n\
         (defn caller [n] (add-i64 (let [idp (fn [y] (add-i64 y 1))] (idp n)) 0))\n\
         (defn use-c [] (caller 5))",
    );
    assert!(
        symbol_names_containing(&tc, "idp$").is_empty(),
        "the let-shadowed `(idp n)` MUST NOT mint the top-level `idp`'s mono \
         (FIXME 0653); symbols: {:?}",
        symbol_names_containing(&tc, "idp"),
    );
    // Control — an UNSHADOWED `(idp n)` mints `idp$Int`.
    let mut tc2 = tc_with_prims();
    check_src(
        &mut tc2,
        "(defn idp [x] x)\n\
         (defn caller2 [n] (add-i64 (idp n) 0))\n\
         (defn use-c2 [] (caller2 5))",
    );
    assert!(
        !symbol_names_containing(&tc2, "idp$").is_empty(),
        "the UNSHADOWED `(idp n)` control MUST still mint `idp$Int`; symbols: {:?}",
        symbol_names_containing(&tc2, "idp"),
    );
}

// Fix B / FIXME 0653 — site 4 (mono-recheck epilogue, parametric hop). Inside a
// monomorphised `poly$Int` body, a let-shadowed parametric `(tgt p)` MUST
// resolve to the LOCAL — `monomorphise_inner_parametric_hops` MUST NOT record a
// `tgt$…` dispatch. Control: the unshadowed twin.
#[test]
fn shadowed_parametric_in_mono_body_no_record_fix_b() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn tgt [x] x)\n\
         (defn poly [p] (let [tgt (fn [y] y)] (tgt p)))\n\
         (defn use-poly [] (poly 5))",
    );
    let view = mono_instance_view_containing(&tc, "poly$");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    assert!(
        !targets.iter().any(|(_, fq)| matches!(fq, Some(fq) if fq.symbol.as_ref().contains("tgt$"))),
        "the shadowed `(tgt p)` in `poly$Int` MUST NOT record a `tgt$…` dispatch \
         (FIXME 0653 site 4); collected: {targets:?}"
    );
}

// Fix B / FIXME 0653 — site 3 (mono-recheck epilogue, constrained call). Inside
// `poly$Int`, a let-shadowed constrained `(cadd p)` MUST resolve to the LOCAL —
// `resolve_inner_constrained_calls` MUST NOT record a `cadd$…` dispatch.
#[test]
fn shadowed_constrained_in_mono_body_no_record_fix_b() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn cadd [x] (add-i64 x x))\n\
         (defn poly [p] (let [cadd (fn [y] y)] (cadd p)))\n\
         (defn use-poly [] (poly 5))",
    );
    let view = mono_instance_view_containing(&tc, "poly$");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    assert!(
        !targets.iter().any(|(_, fq)| matches!(fq, Some(fq) if fq.symbol.as_ref().contains("cadd$"))),
        "the shadowed `(cadd p)` in `poly$Int` MUST NOT record a `cadd$…` \
         dispatch (FIXME 0653 site 3); collected: {targets:?}"
    );
}

// spec: spec/05-definitions.md §5.1.2 — FIXME 0432 Face A (S91 Wave-7):
//   a multi-clause annotated `defn` whose body contains an in-body self-call
//   must carry that self-call's mangled `SigDispatch` resolution ON the AST
//   node of the MANGLED variant entry. The seam: `register_mangled_variants`
//   removes the internal `{name}__v{i}` keys and reinserts the variant
//   entries under their mangled names; the finalize re-annotation block must
//   re-annotate under the MANGLED keys (not the stale internal keys) so the
//   self-call's `SigDispatch` (written by `resolve_pending_overloads`) lands
//   on the body. Before the fix the lookup missed and the body's self-call
//   node carried NO `resolved_call` — the backend then fell back to the
//   undefined bare name `h` (`undefined function: h` at codegen).
//
// This is the unit-tier guard for the e2e
// `tests/spec_05_definitions::defn_multi_clause_annotated_self_call_minimal_repro`.
#[test]
fn multi_sig_self_call_carries_mangled_sig_dispatch() {
    let mut tc = tc_with_prims();
    // `h` variant 1 = `[:Int n] (h n n)`; the in-body 2-arg self-call must
    // dispatch to variant 2 (`h$Int+Int`). The mangled entry for variant 1
    // is `h$Int`; its body Apply node must carry SigDispatch{h$Int+Int}.
    let src = "\
        (defn h \
            ([:primitives/Int n] (h n n)) \
            ([:primitives/Int a :primitives/Int b] (add-i64 a b)))";
    let sexps = cranelisp_frontend::parse(src).expect("parse");
    let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
    tc.check_program_self(&program).unwrap();

    // Walk a body Expr tree collecting every `SigDispatch` mangled name.
    fn collect_sig_dispatch(expr: &Expr, out: &mut Vec<String>) {
        let rc = match expr {
            Expr::Apply { callee, args, resolved_call, .. } => {
                collect_sig_dispatch(callee, out);
                for a in args {
                    collect_sig_dispatch(a, out);
                }
                resolved_call.as_deref()
            }
            Expr::Var { resolved_call, .. } => resolved_call.as_deref(),
            Expr::If { cond, then_branch, else_branch, .. } => {
                collect_sig_dispatch(cond, out);
                collect_sig_dispatch(then_branch, out);
                collect_sig_dispatch(else_branch, out);
                None
            }
            Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                for (_, b) in bindings {
                    collect_sig_dispatch(b, out);
                }
                collect_sig_dispatch(body, out);
                None
            }
            Expr::Lambda { body, .. }
            | Expr::Annotate { expr: body, .. }
            | Expr::Trace { body, .. } => {
                collect_sig_dispatch(body, out);
                None
            }
            _ => None,
        };
        if let Some(ResolvedCall::SigDispatch { mangled_name }) = rc {
            out.push(mangled_name.as_ref().to_string());
        }
    }

    // The variant-1 entry lives under the MANGLED key `h$Int` (the internal
    // `h__v0` key was removed by `register_mangled_variants`).
    let st = tc.symbol_table();
    let entry = st
        .get("h$Int")
        .expect("mangled variant `h$Int` must be registered");
    let body = match entry {
        ModuleEntry::Def { ast: Some(variant), .. } => &variant.body,
        other => panic!("h$Int must carry an annotated ast: {other:?}"),
    };

    let mut dispatches = Vec::new();
    collect_sig_dispatch(body, &mut dispatches);
    assert!(
        dispatches.iter().any(|d| d == "h$Int+Int"),
        "the in-body self-call `(h n n)` must carry SigDispatch{{h$Int+Int}} \
         on the mangled variant body (not a bare unresolved name); \
         found dispatches: {dispatches:?}",
    );
}

// spec: spec/05-definitions.md §5.1.2 (u2/u3, §11.3(B)) — a clause pinned
//   concrete by a sibling self-call (the back-flow) is registered `Concrete`
//   under its CONCRETE mangle; NO `$Var`-mangled entry survives finalize, and
//   the drain's `SigDispatch` name is that same concrete mangle (one
//   `mangle_sig` source ⇒ entry-name and dispatch-name agree, Principle 7).
#[test]
fn multi_sig_backflow_pins_clause_concrete_no_var_entry_survives() {
    let mut tc = tc_with_prims();
    // rp4: the 2-arg clause delegates to the concrete 3-arg sibling, which
    // pins its params to Int (back-flow). Pre-drain the 2-arg clause is a
    // `$Var` Polymorphic template; post-drain it is a `Concrete` `rp4$Int+Int`.
    let src = "(defn rp4 ([p rot] (let [q (rp4 p rot 0)] p)) \
                         ([p rot idx] (primitives/add-i64 p (primitives/add-i64 rot idx))))";
    let program =
        cranelisp_frontend::build_forms(&cranelisp_frontend::parse(src).unwrap()).unwrap();
    tc.check_program_self(&program).expect("rp4 back-flow infers");
    let st = tc.symbol_table();
    match st.get("rp4$Int+Int") {
        Some(ModuleEntry::Def { kind, scheme, .. }) => {
            assert!(
                matches!(
                    kind.as_ref(),
                    DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                ),
                "the back-flow-pinned 2-arg clause must be Concrete, got {kind:?}"
            );
            assert!(
                scheme.ty.is_concrete(),
                "rp4$Int+Int scheme must be fully concrete, got {:?}",
                scheme.ty
            );
        }
        other => panic!("rp4$Int+Int concrete sibling not registered: {other:?}"),
    }
    // §11.3(B): the stale `$Var` template must NOT survive.
    assert!(
        st.get("rp4$Var+Var").is_none(),
        "no `$Var` entry may survive for a back-flow-pinned clause (§11.3(B))"
    );
    // The concrete 3-arg clause is its own concrete callable.
    assert!(
        matches!(
            st.get("rp4$Int+Int+Int"),
            Some(ModuleEntry::Def { kind, .. })
                if matches!(kind.as_ref(), DefKind::UserFn { fn_state: UserFnState::Concrete { .. } })
        ),
        "the 3-arg clause must be Concrete rp4$Int+Int+Int"
    );
}

// spec: spec/05-definitions.md §5.1.2 (u3, §11.3.2) — the B1 fix + I3 pin:
//   in a ≥2-hop self-call delegation chain (`f3`), every self-call's recorded
//   `SigDispatch` MUST name an entry that EXISTS in the final symbol table —
//   i.e. recorded-dispatch-name ≡ registered-entry-name over the FINALISED
//   post-drain types. This is the case that escaped W2: the pass-1 self-call
//   dispatch was derived MID-drain, when clause 2's params were still `Var`, so
//   clause 1 recorded a `$Var` template name that finalize later removed →
//   `f3$Var+Var` reached codegen. Deferring the derivation post-drain (one
//   `mangle_sig` over the finalised params) makes every recorded dispatch name a
//   live entry (no `$Var` residue), order-independent (Principle 24).
#[test]
fn multi_sig_delegation_chain_self_call_dispatches_name_live_entries_no_var_residue() {
    let mut tc = tc_with_prims();
    // f3: clause [a] delegates to [a b]; [a b] delegates to [a b c]; the 3-arg
    // leaf pins every clause to Int through the chain (the review's B1 repro).
    let src = "(defn f3 ([a] (f3 a 0)) ([a b] (f3 a b 1)) \
                         ([a b c] (primitives/add-i64 a (primitives/add-i64 b c))))";
    let program =
        cranelisp_frontend::build_forms(&cranelisp_frontend::parse(src).unwrap()).unwrap();
    tc.check_program_self(&program)
        .expect("the delegation chain back-flow-pins every clause to Int (§5.1.2)");

    let st = tc.symbol_table();
    // Every clause is a live Concrete entry under its finalised concrete mangle;
    // NO `$Var` template survives any clause of a fully back-flow-pinned chain.
    for concrete in ["f3$Int", "f3$Int+Int", "f3$Int+Int+Int"] {
        assert!(
            matches!(
                st.get(concrete),
                Some(ModuleEntry::Def { kind, .. })
                    if matches!(kind.as_ref(), DefKind::UserFn { fn_state: UserFnState::Concrete { .. } })
            ),
            "clause entry `{concrete}` must be a live Concrete entry",
        );
    }
    for var_key in ["f3$Var", "f3$Var+Var", "f3$Var+Var+Var"] {
        assert!(
            st.get(var_key).is_none(),
            "no `$Var` template (`{var_key}`) may survive a fully pinned chain (§11.3.2)",
        );
    }

    // The I3 invariant: walk each mangled clause body; every `SigDispatch`
    // mangled name MUST resolve to an existing symbol-table entry (no dangling
    // `$Var` dispatch), and none may contain `$Var`.
    fn collect_sig_dispatch(expr: &Expr, out: &mut Vec<String>) {
        let rc = match expr {
            Expr::Apply { callee, args, resolved_call, .. } => {
                collect_sig_dispatch(callee, out);
                for a in args {
                    collect_sig_dispatch(a, out);
                }
                resolved_call.as_deref()
            }
            Expr::Var { resolved_call, .. } => resolved_call.as_deref(),
            Expr::If { cond, then_branch, else_branch, .. } => {
                collect_sig_dispatch(cond, out);
                collect_sig_dispatch(then_branch, out);
                collect_sig_dispatch(else_branch, out);
                None
            }
            Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                for (_, b) in bindings {
                    collect_sig_dispatch(b, out);
                }
                collect_sig_dispatch(body, out);
                None
            }
            Expr::Lambda { body, .. }
            | Expr::Annotate { expr: body, .. }
            | Expr::Trace { body, .. } => {
                collect_sig_dispatch(body, out);
                None
            }
            _ => None,
        };
        if let Some(ResolvedCall::SigDispatch { mangled_name }) = rc {
            out.push(mangled_name.as_ref().to_string());
        }
    }

    let mut all_dispatches = Vec::new();
    for concrete in ["f3$Int", "f3$Int+Int", "f3$Int+Int+Int"] {
        if let Some(ModuleEntry::Def { ast: Some(variant), .. }) = st.get(concrete) {
            collect_sig_dispatch(&variant.body, &mut all_dispatches);
        }
    }
    // The chain's two hops must be recorded (proving the deferral fired), and
    // every recorded dispatch names a live bare-keyed entry with no `$Var`.
    assert!(
        all_dispatches.iter().any(|d| d == "f3$Int+Int"),
        "clause [a]'s self-call `(f3 a 0)` must dispatch to the live f3$Int+Int \
         (not a dangling `$Var`); found: {all_dispatches:?}",
    );
    assert!(
        all_dispatches.iter().any(|d| d == "f3$Int+Int+Int"),
        "clause [a b]'s self-call `(f3 a b 1)` must dispatch to f3$Int+Int+Int; \
         found: {all_dispatches:?}",
    );
    for d in &all_dispatches {
        assert!(
            !d.contains("$Var"),
            "no self-call `SigDispatch` may name a `$Var` template ({d}) — every \
             recorded dispatch must name a finalised concrete entry (§11.3.2)",
        );
        assert!(
            st.get(d).is_some(),
            "the recorded dispatch name `{d}` must resolve to a live symbol-table \
             entry (recorded-dispatch-name ≡ registered-entry-name, Principle 7)",
        );
    }
}

// spec: spec/05-definitions.md §5.1.2 (§11.3.1 caveat (b), the I1 fix) — a
//   genuinely-polymorphic RECURSIVE clause of a multi-sig defn is inference-
//   equivalent to the standalone recursive function (which accepts + runs). The
//   1-arg clause `([x] (if true x (g x)))` monomorphises at an external `(g 5)`;
//   during the template's mono recheck the inner self-call `(g x)` is
//   monomorphic recursion to THIS instance, resolved inline against the origin
//   base — NOT deferred to a pending entry the sole drain has already taken (the
//   residual-var wrong-reject with the internal `g$Var$Int` mangle leak).
#[test]
fn recursive_poly_multi_sig_clause_monomorphises_inline_no_residual() {
    let mut tc = tc_with_prims();
    let src = "(defn g ([x] (if true x (g x))) ([a b] a))\n\
               (defn use-g [] :primitives/Int (g 5))";
    let program =
        cranelisp_frontend::build_forms(&cranelisp_frontend::parse(src).unwrap()).unwrap();
    // MUST accept: P7 `finalize_mono_codegen_view` hard-errors on a residual
    // `Var` in the mono body, so a clean accept proves the inner self-call was
    // resolved (the instance body is fully concrete).
    tc.check_program_self(&program).expect(
        "g's recursive poly clause is inference-equivalent to the standalone \
         recursive fn — MUST accept, not wrong-reject with an internal mangle leak",
    );
    // The concrete instance is a live, fully-concrete Concrete entry.
    let st = tc.symbol_table();
    match st.get("test/g$Var$Int") {
        Some(ModuleEntry::Def { kind, scheme, .. }) => {
            assert!(
                matches!(
                    kind.as_ref(),
                    DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                ),
                "the mono instance `g$Var$Int` must be Concrete, got {kind:?}",
            );
            assert!(
                scheme.ty.is_concrete(),
                "the mono instance's stored type must be fully concrete \
                 (the inner self-call left no residual `Var`), got {:?}",
                scheme.ty,
            );
        }
        other => panic!("the `(g 5)` mono instance `test/g$Var$Int` is missing: {other:?}"),
    }
}

// spec: spec/05-definitions.md §5.1.2 (u1) — the post-drain per-clause
//   ambiguity classification: a genuinely-polymorphic clause is ADMISSIBLE
//   (skipped); a concrete-signature clause with an internally-unpinned var
//   reaching a codegen position is the §3.11 ambiguity — the same disposition
//   the equivalent standalone function would get.
#[test]
fn multi_sig_clause_admissible_poly_vs_genuinely_unpinned() {
    // Admissible: `([:a x] x)` is genuinely polymorphic → accepted.
    let mut tc = tc_with_prims();
    let ok = "(defn f ([:a x] x) ([:Int x :Int y] (primitives/add-i64 x y)))";
    let p = cranelisp_frontend::build_forms(&cranelisp_frontend::parse(ok).unwrap()).unwrap();
    tc.check_program_self(&p)
        .expect("a genuinely-polymorphic clause is admissible (§5.1.2)");

    // Ambiguous: a concrete-signature clause `([:Int n] (let [u []] n))` whose
    // internal `u = []` carries a free `(Vec a)` into a codegen position. The
    // sibling `([a b] a)` is admissibly poly (skipped); the defn errors on the
    // unpinned clause.
    let mut tc2 = tc_with_prims();
    let bad = "(defn f ([:primitives/Int n] (let [u []] n)) ([a b] a))";
    let p2 = cranelisp_frontend::build_forms(&cranelisp_frontend::parse(bad).unwrap()).unwrap();
    let err = tc2
        .check_program_self(&p2)
        .expect_err("an internally-unpinned concrete clause is §3.11 ambiguous");
    assert!(
        format!("{err}").to_lowercase().contains("ambiguous"),
        "the unpinned-clause rejection must be a §3.11 ambiguity, got: {err}"
    );
}

// spec: spec/05-definitions.md §5.1.2 (u7/u8/u9, §11.4) — a trait-constrained
//   clause of a multi-sig defn is a single-variant `Constrained` TEMPLATE under
//   its normalized `$Var` mangle (never a bogus `Concrete{got_slot}`); dispatch
//   to it routes through per-call-site monomorphisation, minting a concrete
//   instance — exactly as a standalone constrained fn.
#[test]
fn constrained_multi_sig_clause_is_template_and_dispatches_via_mono() {
    let mut tc = tc_with_prims();
    register_num_trait_inline(&mut tc);
    // g: a constrained 1-arg clause `([:a x] (+ x x))` (Num a) + a concrete
    // 2-arg clause; a use `(g 3)` at Int.
    let src = "(defn g ([:a x] (+ x x)) ([:primitives/Int x :primitives/Int y] (primitives/add-i64 x y)))\n\
               (defn use-g [] :primitives/Int (g 3))";
    let p = cranelisp_frontend::build_forms(&cranelisp_frontend::parse(src).unwrap()).unwrap();
    tc.check_program_self(&p)
        .expect("the constrained clause is admissible at a non-overlapping arity (§11.4)");
    let st = tc.symbol_table();
    // u7: the non-concrete-param clause is a SLOT-LESS TEMPLATE under its
    // normalized `$Var` mangle (`Constrained` with a real Num prelude, or
    // `Polymorphic` in this reduced fixture where `+`'s constraint does not
    // accrue) — never a bogus `Concrete{got_slot}` over the `Var` param
    // (§11.4 step 2 / §11.3(B); the constrained-specific path is exercised
    // end-to-end by `spec_05_definitions::constrained_clause_*` with the real
    // TestStandard Num).
    match st.get("g$Var") {
        Some(ModuleEntry::Def { kind, .. }) => assert!(
            matches!(
                kind.as_ref(),
                DefKind::UserFn {
                    fn_state:
                        UserFnState::Constrained(_) | UserFnState::Polymorphic(_)
                }
            ),
            "g$Var must be a slot-less template (never Concrete over Var), got {kind:?}"
        ),
        other => panic!("the clause template `g$Var` is missing: {other:?}"),
    }
    // u8/u9: `(g 3)` monomorphised the clause template at Int — a concrete
    // instance of `g$Var` at Int exists.
    assert!(
        st.all_symbols()
            .any(|(n, e)| n.as_ref().contains("g$Var")
                && n.as_ref().contains("Int")
                && matches!(e, ModuleEntry::Def { kind, .. }
                    if matches!(kind.as_ref(), DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }))),
        "`(g 3)` must monomorphise the constrained clause template to a concrete \
         Int instance (§11.4 step 4)"
    );
}
