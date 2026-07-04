//! S102 /qa trait-method `$Type`-grain probe (FIXME 0519 adjacent seam, P7/P8) —
//! a FOURTH instance of the lossy-head mangle class the unified mono-mangler
//! (0519) did NOT cover. The `/dev` unified the mono-instance mangler onto the
//! lossless home-qualified key `{home}/{bare}${recursive-sig}` but declared the
//! trait-method naming grain (`Trait.method$Type`, via `concrete_type_name`
//! head-name) a "distinct grain, correct-by-design", left UNCHANGED. This guard
//! proves that claim is WRONG: the trait-method grain is head-name-only and
//! collides across two same-named types from different modules.
//!
//! ROOT CAUSE (`crates/cranelisp-typecheck/src/traits/dispatch.rs:52,88`): trait
//! dispatch mints `mangled = "{Trait}.{method}${impl_type_name}"` where
//! `impl_type_name = concrete_type_name(resolved_arg)` — the BARE type name,
//! home erased. Two DISTINCT nominal types `a/Widget` and `b/Widget` (spec
//! §3.8.4: same bare name in different modules ⇒ distinct types), each with an
//! `impl Describe Widget`, both mint `Describe.describe$Widget`. The two impl
//! method bodies (a→100, b→200) collide on that one linker symbol; every
//! `(describe x)` call site — regardless of the value's true type — dispatches
//! to whichever same-named `Widget` is in the caller's scope. This is the same
//! lossy-head class as 0483 (ADT-arg erasure) and 0508 (home erasure), now at
//! the trait-method grain. It is a SILENT wrong-dispatch (no crash, no
//! diagnostic) — the worst defect class.
//!
//! OBSERVED (manual, target/debug/cranelisp):
//!   - `a/Widget` imported into caller: `(add-i64 (describe a/WA) (describe b/WB))`
//!     → 200 (BOTH dispatch a's `+100` body: 100+100). Correct is 300 (100+200).
//!   - `b/Widget` imported, calls reversed → 400 (BOTH dispatch b's `+200` body:
//!     200+200). Order/scope-confirmed: whichever same-named `Widget` is in the
//!     caller's scope captures BOTH dispatches — the hallmark of the head-name
//!     collision.
//!   - Each dispatch IN ISOLATION is correct (a/WA→100, b/WB→200) — the miscompile
//!     appears only when both same-named-type impls are reachable together.
//!
//! FIXME(/dev typecheck): the fix extends the 0519 unification to the
//! trait-method grain — the dispatch mangled name must carry the FQ type
//! identity (`{Trait}.{method}$${home}/{Type}` or equivalent), collision-free by
//! construction like the mono-mangler now is (`concrete_type_name` head-name is
//! retained only for trait-impl TARGET naming where a single home is implied;
//! the dispatch/codegen linker symbol must be FQ). `cranelisp-typecheck`
//! (`traits/dispatch.rs` + the `finalize_impl_method_writeback` symbol key in
//! `traits/impl_check.rs`, kept in lock-step). Routed for /sprint dispatch.
//!
//! Failing-not-ignored per `memory/feedback_failing_not_ignored.md`; ledger:
//! `tests/plan/ledger.md` §"Sprint 102 — trait-method $Type-grain home collision
//! (4th lossy-head instance)".

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// Module `a`: owns the SHARED trait `Describe`, a local type `Widget` (ctor
// `WA`), and an `impl Describe Widget` whose body yields 100.
const A_MODULE: &str = "(deftrait Describe (describe [x] Int))\n\
                        (deftype Widget WA)\n\
                        (impl Describe Widget (defn describe [w] 100))\n";

// Module `b`: imports the SAME trait from `a`, defines its OWN distinct `Widget`
// (ctor `WB`, nominally `b/Widget` ≠ `a/Widget`), impl body yields 200.
const B_MODULE: &str = "(import [a [Describe describe]])\n\
                        (deftype Widget WB)\n\
                        (impl Describe Widget (defn describe [w] 200))\n";

// spec: spec/07-traits.md §7.4 — a resolved trait-method call maps to the
// mangled name `Trait.method$Type`; this MUST respect the §3.8.4 rule that type
// identity is nominal and fully-qualified (two same-bare-named types from
// different modules are DISTINCT). RED on HEAD: the mangled name uses the BARE
// `Type` head-name (`Describe.describe$Widget`), so `a/Widget` and `b/Widget`
// collide → both `describe` dispatches bind ONE impl body. `(add-i64 (describe
// a/WA) (describe b/WB))` returns 200 (100+100, both a's body) not the correct
// 300 (100+200). Flips green when the dispatch mangled name carries FQ type
// identity (the 0519 unification extended to the trait-method grain).
// Cross-ref: spec/03-types.md §3.8.4 — nominal, fully-qualified type identity.
#[test]
fn two_same_named_types_same_trait_dispatch_to_own_impls() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("a.cl", A_MODULE)
        .file("b.cl", B_MODULE)
        .stdin(
            "(import [primitives [*]])\n\
             (import [a [Describe describe Widget]])\n\
             (add-i64 (describe a/WA) (describe b/WB))\n",
        )
        .output()
        // Succeeds (no crash) — the RED signal is the WRONG VALUE, the hallmark
        // of a silent miscompile.
        .assert_ok()
        // a/WA → a's impl (100); b/WB → b's impl (200); sum → 300 (correct
        // per-value nominal dispatch).
        .assert_stdout_contains(":primitives/Int 300")
        // The specific wrong-dispatch value: BOTH calls binding a's body
        // (100+100) because `Describe.describe$Widget` collapses the two homes.
        .assert_stdout_does_not_contain(":primitives/Int 200");
}
