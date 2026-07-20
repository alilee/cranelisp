// qualified_binder_expansion_0670.rs — Track C 0670 chain cells (s114-test-plan
// §4.3; F8 three waves, strict order: int fix → frontend value-level reject
// re-lands → these cells).
//
// 0670: the int macro-expansion qualification pass (`qualify_expanded_sexp`,
// `src/process_form/macro_resolution.rs`) is scope-BLIND — it re-walks the tree the
// expander already walked scope-aware and can qualify a BINDER whose name collides
// with an importable symbol reachable from an expanded FOREIGN macro's defining
// module. /arch ruled path 1: a binder is never a reference; the pass must skip
// binder slots (thread the shadow set). The value-level binder REJECT — `(defn f
// [a/b] …)` MUST reject a qualified binder — re-lands in the frontend wave 2.
//
// IQ-P (positive): the colliding-binder-plus-macro program MUST compile and run.
// IQ-N (negative): a value-level QUALIFIED binder (`a/b`) MUST be a located reject,
//   with a BARE-binder twin that stays legal (the reject fires on the qualified
//   SPELLING, not on collision).
//
// POLARITY NOTE (/testing, verified 2026-07-20 post-c962f133; reported to /qa): the
// 0670 int defect does NOT reproduce at HEAD with the documented shapes — every
// IQ-P shape below (incl. the verbatim FIXME repro `(defn greet [name] (str …))`)
// already COMPILES AND RUNS. The skip guard `qualify_expanded_sexp` already carries
// ("hold verbatim if the symbol is available in the current module") plus the
// narrow `defining_modules` seeding suppress the mis-qualification for these cases.
// So IQ-P1..P3 are BORN-GREEN fences (they must STAY green through the int fix and
// the wave-2 reject re-land — wave-flip ledger §7), NOT the RED-until-int-fix cells
// the plan predicted. The RED wave-2 acceptance is IQ-N1..N4 (silent-accept today).
// Free-standing except IQ-P3 (the sanctioned stdlib touchpoint for the real route).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// A foreign macro module: `wrap` doubles its arg; `label` is a symbol the module
// also exports (so it is in the macro's defining-module qualify table — the
// collision surface the pass must not mis-qualify a binder against).
const MLIB: &str = "(import [primitives [add-i64]])\n\
     (defn label [] 0)\n\
     (defmacro wrap [x] `(add-i64 ~x ~x))\n";

// IQ-P1 — int-fix positive (BORN-GREEN fence): a defn PARAM named `label` collides
// with the foreign macro module's exported `label`, and the foreign macro `wrap` is
// expanded in the body (so the qualification pass runs). The program MUST compile
// and run — the binder `label` is held bare, never qualified to `mlib/label`.
// `(greet 21)` = 42.
// spec: spec/05-definitions.md §5.1.1 — a defn param is a binder held verbatim
// through macro-expansion qualification (a binder is never a reference).
#[test]
fn colliding_defn_param_with_foreign_macro_compiles_and_runs() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .file("mlib.cl", MLIB)
        .user(
            "(import [primitives [Pure]])\n\
             (import [mlib [wrap]])\n\
             (defn greet [label] (wrap label))\n\
             (defn main [] (Pure (greet 21)))\n",
        )
        .output()
        .assert_exit(42);
}

// IQ-P2 — the `let` sibling (BORN-GREEN fence): a `let`-bound name `label` collides
// with the foreign symbol, used inside the foreign-macro expansion. The let binder
// is held bare. `(f)` = 42.
// spec: spec/04-expressions.md §4.3 — a `let` binder is held verbatim through
// macro-expansion qualification.
#[test]
fn colliding_let_binder_with_foreign_macro_compiles_and_runs() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .file("mlib.cl", MLIB)
        .user(
            "(import [primitives [Pure]])\n\
             (import [mlib [wrap]])\n\
             (defn f [] (let [label 21] (wrap label)))\n\
             (defn main [] (Pure (f)))\n",
        )
        .output()
        .assert_exit(42);
}

// IQ-P3 — the verbatim FIXME repro, the real user-facing route (BORN-GREEN fence;
// sanctioned stdlib touchpoint). `(defn greet [name] (str "hello, " name))` where
// `str` is the foreign `text.string` macro and `name` is the param. MUST compile —
// the param binder `name` is NOT qualified to a `binder must be bare` reject.
// spec: spec/05-definitions.md §5.1.1 — a param used inside a foreign-macro
// expansion is a binder held verbatim.
#[test]
fn greet_name_param_with_str_macro_compiles() {
    let out = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .run("user.cl")
        .user(
            "(import [primitives [Pure]])\n\
             (import [text.string [str]])\n\
             (defn greet [name] (str \"hello, \" name))\n\
             (defn main [] (Pure 0))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.status.code() == Some(0) && !c.contains("binder must be bare"),
        "the verbatim FIXME repro `(defn greet [name] (str \"hello, \" name))` MUST \
         compile — the param binder `name` must NOT be qualified to a `binder must \
         be bare` reject by the scope-blind expansion pass (0670); got exit {:?}:\n{c}",
        out.status.code()
    );
}

// ---- IQ-N — value-level QUALIFIED-BINDER negatives (RED; wave-2 acceptance) ------
//
// A qualified name (`a/b`, both halves non-empty) is a valid REFERENCE, but in a
// BINDER position it MUST be a located reject ("a binder must be bare"). Today the
// value-level reject is NOT landed — `a/b` is SILENTLY ACCEPTED as a binder (the
// program runs, exit 5). These flip GREEN when wave 2 re-lands the reject. The
// BARE-binder twin stays legal in each cell (the reject fires on the qualified
// SPELLING, not on the collision — a colliding BARE binder is legal, per IQ-P).

// IQ-N1 — defn param qualified binder.
// spec: spec/05-definitions.md §5.1.1 — a defn param binder must be a bare symbol;
// a qualified spelling is a located error.
// defect: class=silent-accept locus=crates/cranelisp-frontend value-level binder reject (defn param) — qualified binder `a/b` silently accepted; reject re-lands wave 2 (0670 F8) found=S114 owner=/dev
#[test]
fn defn_param_qualified_binder_rejected_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn f [a/b] a/b)\n(defn main [] (Pure (f 5)))\n")
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error") && out.status.code() != Some(5),
        "a qualified defn-param binder `[a/b]` MUST be a located reject (a binder \
         must be bare) — today it is silently accepted and the program runs (exit \
         5); got exit {:?}:\n{c}",
        out.status.code()
    );
}

// IQ-N1 bare twin (GREEN) — the colliding BARE binder stays legal.
// spec: spec/05-definitions.md §5.1.1 — a bare defn-param binder is accepted.
#[test]
fn defn_param_bare_binder_twin() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn f [ab] ab)\n(defn main [] (Pure (f 5)))\n")
        .output()
        .assert_exit(5);
}

// IQ-N2 — fn param qualified binder.
// spec: spec/04-expressions.md §4.5 — an `fn` param binder must be a bare symbol.
// defect: class=silent-accept locus=crates/cranelisp-frontend value-level binder reject (fn param) — qualified binder silently accepted; reject re-lands wave 2 (0670 F8) found=S114 owner=/dev
#[test]
fn fn_param_qualified_binder_rejected_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn f [] (let [g (fn [a/b] a/b)] (g 5)))\n(defn main [] (Pure (f)))\n")
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error") && out.status.code() != Some(5),
        "a qualified `fn`-param binder `[a/b]` MUST be a located reject; today \
         silently accepted (exit 5); got exit {:?}:\n{c}",
        out.status.code()
    );
}

// IQ-N3 — let name qualified binder.
// spec: spec/04-expressions.md §4.3 — a `let` binding name must be a bare symbol.
// defect: class=silent-accept locus=crates/cranelisp-frontend value-level binder reject (let name) — qualified binder silently accepted; reject re-lands wave 2 (0670 F8) found=S114 owner=/dev
#[test]
fn let_name_qualified_binder_rejected_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn f [] (let [a/b 5] a/b))\n(defn main [] (Pure (f)))\n")
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error") && out.status.code() != Some(5),
        "a qualified `let` binding name `[a/b 5]` MUST be a located reject; today \
         silently accepted (exit 5); got exit {:?}:\n{c}",
        out.status.code()
    );
}

// IQ-N4 — match var-pattern qualified binder.
// spec: spec/06-pattern-matching.md §6.2 — a match pattern variable must be a bare
// symbol; a qualified spelling is a located error.
// defect: class=silent-accept locus=crates/cranelisp-frontend value-level binder reject (match var-pattern) — qualified binder silently accepted; reject re-lands wave 2 (0670 F8) found=S114 owner=/dev
#[test]
fn match_var_pattern_qualified_binder_rejected_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn f [v] (match v [a/b a/b]))\n(defn main [] (Pure (f 5)))\n")
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error") && out.status.code() != Some(5),
        "a qualified match var-pattern `[a/b a/b]` MUST be a located reject; today \
         silently accepted (exit 5); got exit {:?}:\n{c}",
        out.status.code()
    );
}
