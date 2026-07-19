// nullary_return_dispatch_method_only_import.rs — D2 repro (S112 Phase 6b).
//
// A NULLARY return-type-dispatched trait method, imported WITHOUT its trait,
// leaks past typecheck and surfaces as a codegen `undefined function`.
//
// Two free-standing modules (reduced from /stdlib's `Default`/`Zero` sketch):
//
//   zlib.cl:  (deftrait Zero (z [] self))
//             (impl Zero Int (defn z [] 42))
//   user.cl:  (import [zlib [z]])          <- method `z` ONLY, NOT the trait `Zero`
//             (defn get-z [] (let [x :Int (z)] x))
//
// `z` takes no arguments — dispatch is by the expected RETURN type (`:Int`), the
// §7.1.1 return-type-dispatch path. With only the method imported (not the
// trait), typecheck ACCEPTS `(z)`, then codegen hard-fails:
//   `codegen error … undefined function: z`.
//
// PIN IS RULING-AGNOSTIC. An OPEN NORMATIVE QUESTION (flagged to the user, S112
// Phase 6a): does importing a trait METHOD without its TRAIT suffice for dispatch
// (impl coherence is global), or is trait-in-scope required? EITHER ruling fixes
// this leak — (a) it dispatches and runs to 42, or (b) it is a clean LOCATED
// typecheck-family error naming the trait/impl (exactly what the unary analogue
// already produces: `no impl of trait Show for type … Int`). The `undefined
// function` leak fails BOTH arms: it is neither a successful dispatch nor a
// check-side rejection — a source-level fault typecheck must decide leaks to the
// backend layer (P25 "narrowing carries its check" / check-gate-leak class).
//
// This test asserts ONLY the ruling-agnostic invariant: NO codegen `undefined
// function` leak. The two GREEN fences bracket the correct behaviours the leak
// falls between: (1) importing the trait too runs to 42; (2) the unary analogue,
// method-only, errors cleanly at typecheck.
//
// ATTRIBUTION: /qa attributes precisely at S113 Phase 1.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// Module `zlib`: a nullary return-type-dispatched trait `Zero` with an `Int`
// impl. `z` takes no params; `self` (the return type) is the implementing type.
const ZLIB: &str =
    "(import [primitives [Int]])\n(deftrait Zero (z [] self))\n(impl Zero Int (defn z [] 42))\n";

// D2 — the method-only import MUST NOT leak an `undefined function` codegen
// error. Ruling-agnostic: either it runs to 42, or it is a clean located
// typecheck-family error naming the trait/impl. The leak fails both arms.
// spec: spec/07-traits.md §7.1.1 — the `self` (return) type: a nullary
// return-type-dispatched method resolves by expected return type.
// defect: class=check-gate-leak locus=typecheck nullary return-type-dispatch method-only-import resolution (accepts then leaks `undefined function` to codegen; open user Q: method-only import dispatch vs trait-in-scope required) found=S112 owner=/dev
#[test]
fn nullary_return_dispatch_method_only_import_no_codegen_leak() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .file("zlib.cl", ZLIB)
        .user(
            "(import [primitives [Pure Int]])\n\
             (import [zlib [z]])\n\
             (defn get-z [] (let [x :Int (z)] x))\n\
             (defn main [] (Pure (get-z)))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);

    // The load-bearing RED: no `undefined function` leak at codegen. This is the
    // ONE ruling-agnostic invariant — it fails under NEITHER admissible ruling.
    assert!(
        !c.contains("undefined function") && !c.contains("codegen error"),
        "the method-only import of nullary return-type-dispatched `z` MUST NOT \
         leak an `undefined function` codegen error — a source-level fault \
         typecheck must decide MUST NOT reach the backend (P25 check-gate); got:\n{c}"
    );

    // Ruling-agnostic disposition: EITHER arm is acceptable, so long as no leak.
    // (a) dispatch+run → exit 42; or (b) clean located typecheck error naming
    // the trait/impl. Documented, not separately asserted RED — the leak above is
    // the pin. When the leak is fixed one of these arms holds.
    let ran = out.status.code() == Some(42);
    let clean_reject = !out.status.success()
        && c.to_lowercase().contains("type")
        && (c.contains("trait") || c.contains("impl"));
    assert!(
        ran || clean_reject,
        "post-fix, the method-only import MUST resolve to ONE of the two \
         ruling-agnostic arms: (a) run to exit 42, or (b) a clean located \
         typecheck-family error naming the trait/impl; got exit {:?}:\n{c}",
        out.status.code()
    );
}

// GREEN fence (a) — importing the TRAIT alongside the method makes the nullary
// return-type dispatch resolve and run: `(get-z)` = 42 ⇒ `--run` exit 42. This
// is the "dispatches cleanly" arm; GREEN on HEAD.
// spec: spec/07-traits.md §7.1.1 — nullary return-type dispatch resolves when
// the trait is in scope.
#[test]
fn nullary_return_dispatch_trait_imported_runs_green_fence() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .file("zlib.cl", ZLIB)
        .user(
            "(import [primitives [Pure Int]])\n\
             (import [zlib [Zero z]])\n\
             (defn get-z [] (let [x :Int (z)] x))\n\
             (defn main [] (Pure (get-z)))\n",
        )
        .output();
    out.assert_exit(42);
}

// GREEN fence (b) — the UNARY analogue: a method that dispatches by its ARGUMENT
// type, imported method-only, errors CLEANLY at typecheck (`no impl of trait
// Show for type … Int`) — never an `undefined function` codegen leak. This is
// the shape D2's nullary path SHOULD take under ruling (b); GREEN on HEAD. It
// isolates the NULLARY return-type-dispatch path as D2's load-bearing element:
// the unary (arg-dispatched) sibling is already caught check-side.
// spec: spec/07-traits.md §7.1.1 — an arg-dispatched method, method-only import,
// is caught check-side.
#[test]
fn unary_arg_dispatch_method_only_import_clean_typecheck_error_green_fence() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .file(
            "ulib.cl",
            "(import [primitives [Int]])\n\
             (deftrait Show (sh [self] Int))\n\
             (impl Show Int (defn sh [x] 99))\n",
        )
        .user(
            "(import [primitives [Pure Int]])\n\
             (import [ulib [sh]])\n\
             (defn get-s [] (sh 5))\n\
             (defn main [] (Pure (get-s)))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !out.status.success() && !c.contains("undefined function"),
        "the unary arg-dispatched method-only import MUST be caught CLEANLY at \
         typecheck, NEVER leak `undefined function` at codegen; got exit {:?}:\n{c}",
        out.status.code()
    );
    assert!(
        c.to_lowercase().contains("type") && c.contains("trait"),
        "the unary analogue's clean error names the trait (`no impl of trait \
         Show …`) — the check-side shape D2's nullary path should take under \
         ruling (b); got:\n{c}"
    );
}
