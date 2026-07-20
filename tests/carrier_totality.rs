// carrier_totality.rs — Track A born-green totality fences for the typed
// resolution carrier (0653 prong 3; `design/arch/typed-resolution-carrier.md`).
//
// The carrier flips `resolved_target` from an `Option<FQSymbol>` convention to a
// closed sum `VarRef::Local{binder,binding_span} | VarRef::Global(FQSymbol)` (and
// `ApplyRef::Dispatch(FQSymbol) | ApplyRef::ViaCallee`), making "unresolved"
// unrepresentable — the phase-boundary gate becomes a LOCATED typecheck error
// (`ViewBuildError::Unresolved{span,name}`), never a codegen leak. These cells pin
// what the constructor must GUARANTEE across the flip; they are GREEN today (the
// current behaviour already handles them) and MUST STAY GREEN through the carrier
// change-set — they fence the flip against over-gating legal locals or losing a
// positive resolution. s114-test-plan §3.2 (CA-2, CA-3, CA-4).
//
// The "retired empty-maps-for-all-local-bodies license" (carrier doc §5.2) means
// every local now takes the `VarRef::Local` path end-to-end; CA-2/CA-3 guard that
// path, CA-4 guards the positive `ApplyRef::ViaCallee` verdict. Each runs through
// REPL / `--run` / `--link` via `run_through_all_modes` (the ×3-mode requirement),
// asserting mode-uniform correctness. Free-standing (no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{run_through_all_modes, PreludeVariant};

// CA-2 — TOTALITY POSITIVE, all-local body. `(defn f [x] (let [y x] y))` is an
// all-local body (param `x`, let-bound `y`); under the carrier every local takes
// the `VarRef::Local` path end-to-end. Born-green fence: guards the flip against
// OVER-gating legal locals (the retired all-local empty-maps license must not
// become a spurious Unresolved). `(f 42)` = 42 across all modes.
// spec: spec/04-expressions.md §4.3 — Let Expression: a local binding resolves to
// its binder in every mode.
#[test]
fn totality_all_local_body_resolves_local_all_modes() {
    run_through_all_modes(
        "(import [primitives [Pure]])\n\
         (defn f [x] (let [y x] y))\n\
         (defn main [] (Pure (f 42)))",
        PreludeVariant::None,
    )
    .assert_all_equal(42);
}

// CA-3a — TOTALITY POSITIVE, local (defn param) shadowing a same-named GLOBAL.
// `base` is a top-level nullary defn (→ 100 if called); a param named `base`
// shadows it. The body `base` MUST resolve to the LOCAL param (42), never phantom-
// dispatch to the global — the sharpest cell of the old `Option`-conflation, now
// decided by the constructor. `(f 42)` = 42 (a phantom-Global read would give the
// global identity, not 42). GREEN twin of the "no phantom Global dispatch" property.
// spec: spec/04-expressions.md §4.2 — Variable Reference: a local binder shadows a
// same-named top-level definition at every use site.
#[test]
fn local_defn_param_shadows_global_resolves_local_all_modes() {
    run_through_all_modes(
        "(import [primitives [Pure]])\n\
         (defn base [] 100)\n\
         (defn f [base] base)\n\
         (defn main [] (Pure (f 42)))",
        PreludeVariant::None,
    )
    .assert_all_equal(42);
}

// CA-3b — the `let` sibling. A `let` binding named `base` shadows the global
// `base`; the let body `base` MUST resolve to the local (42). `(f)` = 42.
// spec: spec/04-expressions.md §4.3 — a `let`-bound name shadows a same-named
// top-level definition inside its body.
#[test]
fn local_let_shadows_global_resolves_local_all_modes() {
    run_through_all_modes(
        "(import [primitives [Pure]])\n\
         (defn base [] 100)\n\
         (defn f [] (let [base 42] base))\n\
         (defn main [] (Pure (f)))",
        PreludeVariant::None,
    )
    .assert_all_equal(42);
}

// CA-3c — the MATCH-VAR sibling. A match var-pattern binds `base`, shadowing the
// global; the arm body `base` MUST resolve to the match binder (42), never the
// global. `(f 42)` = 42 — the match-arm binder-identity grain the carrier's
// `VarRef::Local.binding_span` disambiguates.
// spec: spec/06-pattern-matching.md §6.2 — a match var-pattern binds a local that
// shadows a same-named top-level definition in the arm body.
#[test]
fn local_match_var_shadows_global_resolves_local_all_modes() {
    run_through_all_modes(
        "(import [primitives [Pure]])\n\
         (defn base [] 100)\n\
         (defn f [v] (match v [base base]))\n\
         (defn main [] (Pure (f 42)))",
        PreludeVariant::None,
    )
    .assert_all_equal(42);
}

// CA-4 — VIACALLEE POSITIVE. A higher-order apply whose CALLEE is a param
// (`(g x)` where `g` is bound by `ap`'s params) runs correctly — `ApplyRef::ViaCallee`
// is a POSITIVE verdict (identity rides the callee `Var`), not a silent default.
// `(ap inc 41)` applies `inc` to 41 → 42. Born-green fence: the carrier records
// `ViaCallee` positively; its absence would be Unresolved = a defect.
// spec: spec/04-expressions.md §4.6 — Function Application: a computed/param callee
// is applied to its arguments.
#[test]
fn viacallee_param_callee_apply_runs_all_modes() {
    run_through_all_modes(
        "(import [primitives [Pure add-i64]])\n\
         (defn ap [g x] (g x))\n\
         (defn inc [n] (add-i64 n 1))\n\
         (defn main [] (Pure (ap inc 41)))",
        PreludeVariant::None,
    )
    .assert_all_equal(42);
}
