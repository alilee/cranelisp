// nullary_return_dispatch_method_only_import.rs — D2 family (§7.11.2 Method-Import
// Dispatch), S113 W1 re-pointed to the SETTLED ruling.
//
// RULING (spec/07-traits.md §7.11.2, settled 2026-07-19, user): importing a trait
// METHOD without its TRAIT is sufficient for dispatch. A method reference carries
// the method's fully-qualified identity, which names the one trait that declares
// it and hence that trait's canonical home module; resolution roots there (a
// bounded keyed-lookup chain, P24 — never a scan) and the impl is found by key on
// (method identity, concrete dispatch type). "Reaching the method reaches
// everything dispatch needs." The trait NAME need not separately be in scope.
//
// This closes S112 defect D2 on the ACCEPT side: the nullary return-type-dispatch
// method-only-import cell (edge (e)) MUST typecheck AND compile to a working call;
// and the unary method-only-import case INVERTS from the old "no impl in scope"
// reject to accept-and-dispatch. Declaration (edge (d)) does NOT invert — an
// `impl` still requires the trait head in scope.
//
// FIX lands in W2 (accept-side, existing `MethodResolutions` carrier — arch Q4;
// /design(typecheck) `traits.md §7.0.1` threads the method's home). Until then the
// accept cells are RED. Every RED here flips at W2.
//
// Family map (tests/plan/s113-test-plan.md §1.1):
//   F-D2-1  nullary_return_dispatch_method_only_import_no_codegen_leak  (RED→W2)
//   F-D2-2  unary_arg_dispatch_method_only_import_accepts_and_dispatches (RED→W2, INVERTED)
//   F-D2-4  nullary_return_dispatch_trait_imported_runs_green_fence      (GREEN)
//   F-D2-5  nullary_dispatch_method_only_and_trait_imported_agree_twin   (RED→W2, the relations axis)
//   F-D2-6  method_import_same_name_two_modules_conflict_neg + _single_import_dispatches (§7.11.2(b))
//   F-D2-7  method_only_import_no_impl_diagnostic_names_owning_trait      (§7.11.2(c))
//   F-D2-8  impl_declaration_still_requires_trait_in_scope_neg           (GREEN — over-inversion fence, edge (d))
//   F-D2-9  method_only_import_no_impl_diagnostic_mode_uniform           (RED→W2, AG-2 class)

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{CrOutput, Cranelisp, PreludeVariant};

// Module `zlib`: a nullary return-type-dispatched trait `Zero` with an `Int`
// impl. `z` takes no params; `self` (the return type) is the implementing type.
const ZLIB: &str =
    "(import [primitives [Int]])\n(deftrait Zero (z [] self))\n(impl Zero Int (defn z [] 42))\n";

// Module `ulib`: a UNARY (argument-dispatched) trait `Show` with an `Int` impl —
// `sh` dispatches on the concrete type of its one argument.
const ULIB: &str = "(import [primitives [Int]])\n\
     (deftrait Show (sh [self] Int))\n\
     (impl Show Int (defn sh [x] 99))\n";

// Run a two-module program (one fixture module + user.cl) under BOTH `--run` and
// `--link`-then-run, asserting the produced process exits with `code` in each.
fn assert_run_and_link_exit(fixture: (&str, &str), user: &str, code: i32) {
    for link in [false, true] {
        let b = Cranelisp::new().with_prelude(PreludeVariant::None);
        let b = if link {
            b.link_then_run("user.cl")
        } else {
            b.run("user.cl")
        };
        b.file(fixture.0, fixture.1)
            .user(user)
            .output()
            .assert_exit(code);
    }
}

// Drive a REPL session with `fixture` on disk (imported by the piped input).
fn repl_with_fixture(fixture: (&str, &str), stdin: &str) -> CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::None)
        .file(fixture.0, fixture.1)
        .stdin(stdin)
        .output()
}

// F-D2-1 — nullary return-type-dispatch, method-only import, MUST accept and
// compile to a working call: `(z)` resolves by the expected `:Int` return type,
// dispatches to the `Zero Int` impl, and `--run` exits 42 across every mode. The
// old ruling-agnostic two-arm pin (no-codegen-leak OR clean reject) tightens to
// the ruled arm now that §7.11.2(e) settled the accept side. RED until W2 flips
// the accept path (the method-only import currently leaks `undefined function`
// at codegen). Name retained for the F-D2-1 plan citation.
// spec: spec/07-traits.md §7.11.2 — edge (e): the nullary return-type-dispatched
// method-only-import cell MUST accept and compile.
// defect: class=check-gate-leak locus=typecheck method-import dispatch — nullary return-type-dispatch method-only import (accepts then leaks `undefined function` to codegen; ruled accept per §7.11.2(e)) found=S112 owner=/dev
#[test]
fn nullary_return_dispatch_method_only_import_no_codegen_leak() {
    let user = "(import [primitives [Pure Int]])\n\
         (import [zlib [z]])\n\
         (defn get-z [] (let [x :Int (z)] x))\n\
         (defn main [] (Pure (get-z)))\n";
    assert_run_and_link_exit(("zlib.cl", ZLIB), user, 42);

    // REPL face: importing only `z`, `(let [x :Int (z)] x)` evaluates to 42.
    repl_with_fixture(
        ("zlib.cl", ZLIB),
        "(import [primitives [Int]])\n(import [zlib [z]])\n(let [x :Int (z)] x)\n",
    )
    .assert_stdout_contains("42");
}

// F-D2-2 — the UNARY inversion. A unary (argument-dispatched) method imported
// method-only MUST now ACCEPT and dispatch on the argument's concrete type, byte-
// for-byte as if the trait had been imported. Previously reported "no impl in
// scope" because the trait was absent; §7.11.2(e) final sentence inverts that to
// accept. `(sh 5)` dispatches to `Show Int` → 99 → `--run` exit 99. RED until W2.
// (Renamed from `..._clean_typecheck_error_green_fence`, which pinned the OLD
// wrong-reject as correct.)
// spec: spec/07-traits.md §7.11.2 — edge (e): the unary method-only-import case
// inverts to accept and dispatches on the argument's concrete type.
// defect: class=wrong-reject locus=typecheck method-import dispatch — unary arg-dispatched method-only import rejected as "no impl in scope" (trait absent); ruled accept per §7.11.2(e) inversion found=S113 owner=/dev
#[test]
fn unary_arg_dispatch_method_only_import_accepts_and_dispatches() {
    let user = "(import [primitives [Pure Int]])\n\
         (import [ulib [sh]])\n\
         (defn get-s [] (sh 5))\n\
         (defn main [] (Pure (get-s)))\n";
    assert_run_and_link_exit(("ulib.cl", ULIB), user, 99);
}

// MC-A1 (S113 W2a) — the import-shape × sig-mentions-foreign-type AXIS on the F-D2
// family. The review found every landed F-D2 accept cell imported `Int` into the
// calling module — a systematic hole: the cells never exercised dispatch when the
// signature mentions a type NOT in the importing module's scope. This variant of
// F-D2-2 imports ONLY `sh` (NOT `Int`): `Show`'s sig `(sh [self] Int)` mentions
// `Int`, which is reachable via the method's home but absent from the caller's
// scope. `(sh 5)` MUST still dispatch to `Show Int` → 99. GREEN post-W2a (the fix
// roots resolution at the method home, so foreign sig types come along); a RED
// here reveals the foreign-sig hole. (The nullary cell F-D2-1 has NO foreign-sig
// variant — its only sig type IS the return-dispatch type, which must be named at
// the call site.)
// spec: spec/07-traits.md §7.11.2 — dispatch reaches sig types via the method home,
// even when they are not imported at the call site.
// defect: class=carrier-loss locus=crates/cranelisp-typecheck method-import dispatch — sig type not in caller scope (foreign-sig axis) found=S113 owner=/dev
#[test]
fn unary_arg_dispatch_method_only_import_foreign_sig_type_accepts() {
    let user = "(import [primitives [Pure]])\n\
         (import [ulib [sh]])\n\
         (defn get-s [] (sh 5))\n\
         (defn main [] (Pure (get-s)))\n";
    assert_run_and_link_exit(("ulib.cl", ULIB), user, 99);
}

// F-D2-4 — GREEN control (untouched): importing the TRAIT alongside the method
// makes the nullary return-type dispatch resolve and run to 42. The "dispatches
// cleanly" arm; GREEN on HEAD, must stay green through W2.
// spec: spec/07-traits.md §7.11.2 — trait-imported dispatch resolves and runs.
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

// F-D2-5 — the RELATIONS-axis TWIN. The same program modulo the import line
// (method-only vs trait+method) MUST produce the SAME observable — exit 42 — under
// `--run`. This is the invariant §7.11.2 states directly ("reaching the method
// reaches everything dispatch needs"): the import shape is not load-bearing on the
// dispatch outcome. The trait-imported arm is GREEN today (F-D2-4); the method-
// only arm is RED until W2, so this twin is RED until W2, and it is exactly the
// pin that a per-import-shape codepath divergence would trip.
// spec: spec/07-traits.md §7.11.2 — method-only and trait-imported dispatch agree.
// defect: class=wrong-reject locus=typecheck method-import dispatch — method-only import diverges from trait-imported on the identical program found=S113 owner=/dev
#[test]
fn nullary_dispatch_method_only_and_trait_imported_agree_twin() {
    let program = |import_line: &str| {
        format!(
            "(import [primitives [Pure Int]])\n\
             {import_line}\n\
             (defn get-z [] (let [x :Int (z)] x))\n\
             (defn main [] (Pure (get-z)))\n"
        )
    };

    let method_only = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .file("zlib.cl", ZLIB)
        .user(&program("(import [zlib [z]])"))
        .output();
    let trait_imported = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .file("zlib.cl", ZLIB)
        .user(&program("(import [zlib [Zero z]])"))
        .output();

    assert_eq!(
        method_only.status.code(),
        trait_imported.status.code(),
        "method-only vs trait-imported dispatch of the same program MUST agree \
         (§7.11.2 — reaching the method reaches everything dispatch needs).\n\
         method-only: exit {:?}\n{}{}\ntrait-imported: exit {:?}\n{}{}",
        method_only.status.code(),
        method_only.stdout,
        method_only.stderr,
        trait_imported.status.code(),
        trait_imported.stdout,
        trait_imported.stderr,
    );
    assert_eq!(
        method_only.status.code(),
        Some(42),
        "both arms MUST run to exit 42; method-only got {:?}",
        method_only.status.code()
    );
}

// Two modules `alib`/`blib` each declaring a same-named method `m` on distinct
// traits, each with an `Int` impl returning a distinct value.
// Distinct return values 7/8 (NOT 1) so an error exit (1) can never be mistaken
// for a successful dispatch (the exit-1 collision that masks a RED).
const ALIB: &str =
    "(import [primitives [Int]])\n(deftrait Aa (m [self] Int))\n(impl Aa Int (defn m [x] 7))\n";
const BLIB: &str =
    "(import [primitives [Int]])\n(deftrait Bb (m [self] Int))\n(impl Bb Int (defn m [x] 8))\n";

// F-D2-6 (conflict polarity) — importing a method named `m` from TWO different
// modules (two traits' `m`) is a duplicate-bare-name CONFLICT per §8.6.4, located,
// at compile time — a conflict, NOT a shadow. §7.11.2(b): the method import is
// itself the disambiguator.
// spec: spec/07-traits.md §7.11.2 — edge (b): two same-named method imports conflict.
// defect: class=silent-accept locus=typecheck/int §8.6.4 duplicate-bare-name method import found=S113 owner=/dev
#[test]
fn method_import_same_name_two_modules_conflict_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .file("alib.cl", ALIB)
        .file("blib.cl", BLIB)
        .user(
            "(import [primitives [Pure Int]])\n\
             (import [alib [m]])\n\
             (import [blib [m]])\n\
             (defn get-m [] (m 5))\n\
             (defn main [] (Pure (get-m)))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.status.code() != Some(0)
            && out.status.code() != Some(7)
            && out.status.code() != Some(8),
        "importing method `m` from two modules MUST be a §8.6.4 duplicate-bare-name \
         conflict, rejected at compile time — NOT silently dispatched to either \
         module's `m` (exit 7 = alib, 8 = blib); got exit {:?}:\n{c}",
        out.status.code()
    );
    assert!(
        !c.contains("undefined function"),
        "the conflict MUST be a located compile-time error, NOT an `undefined \
         function` codegen leak; got:\n{c}"
    );
}

// F-D2-6 (single-import polarity, the NEG twin) — importing only ONE of the two
// modules' `m` dispatches fine: the import IS the disambiguator (§7.11.2(b)). Here
// `m` from `alib` → dispatches to `Aa Int` → 1 → exit 1. Method-only, so RED until
// W2.
// spec: spec/07-traits.md §7.11.2 — edge (b): a single method import disambiguates.
// defect: class=wrong-reject locus=typecheck method-import dispatch — single method-only import not dispatched found=S113 owner=/dev
#[test]
fn method_import_single_of_two_dispatches() {
    assert_run_and_link_exit(
        ("alib.cl", ALIB),
        "(import [primitives [Pure Int]])\n\
         (import [alib [m]])\n\
         (defn get-m [] (m 5))\n\
         (defn main [] (Pure (get-m)))\n",
        7,
    );
}

// F-D2-7 — a dispatch error on a method-only import MUST name the OWNING TRAIT even
// though the trait was never brought into scope (§7.11.2(c)). `Show` has an `Int`
// impl only; dispatching `(sh true)` on `Bool` has genuinely no impl → a clean
// typecheck-family error that names trait `Show`. Never an `undefined function`
// codegen leak.
// spec: spec/07-traits.md §7.11.2 — edge (c): diagnostics name the owning trait.
// defect: class=check-gate-leak locus=typecheck method-import dispatch — no-impl diagnostic must name the owning trait (method-only) found=S113 owner=/dev
#[test]
fn method_only_import_no_impl_diagnostic_names_owning_trait() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .file("ulib.cl", ULIB)
        .user(
            "(import [primitives [Pure Int Bool]])\n\
             (import [ulib [sh]])\n\
             (defn get-s [] (sh true))\n\
             (defn main [] (Pure (get-s)))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.status.code() != Some(0) && !c.contains("undefined function"),
        "a genuine no-impl dispatch MUST be a clean typecheck-family error, NOT a \
         codegen `undefined function` leak; got exit {:?}:\n{c}",
        out.status.code()
    );
    assert!(
        c.contains("Show"),
        "the diagnostic MUST name the owning trait `Show` even though it was never \
         imported (§7.11.2(c)); got:\n{c}"
    );
}

// F-D2-8 — the OVER-INVERSION fence (§7.11.2(d)). Declaring an `impl` still
// requires the trait head in scope: importing only a METHOD `m` of trait `Tt` is
// NOT sufficient to DECLARE `(impl Tt Foo …)`. Declaration reaches the trait;
// dispatch reaches the method. Guards W2 against overshooting the inversion — must
// STAY GREEN (reject holds) through W2.
// spec: spec/07-traits.md §7.11.2 — edge (d): declaration still requires the trait.
#[test]
fn impl_declaration_still_requires_trait_in_scope_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .file(
            "tlib.cl",
            "(import [primitives [Int]])\n(deftrait Tt (m [self] Int))\n(impl Tt Int (defn m [x] 1))\n",
        )
        .user(
            "(import [primitives [Pure Int]])\n\
             (import [tlib [m]])\n\
             (deftype Foo Bar)\n\
             (impl Tt Foo (defn m [y] 2))\n\
             (defn main [] (Pure 0))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.status.code() != Some(0),
        "declaring `(impl Tt Foo …)` with only the method `m` imported (trait `Tt` \
         NOT in scope) MUST be rejected — declaration reaches the trait (§7.11.2(d)); \
         got exit 0:\n{c}"
    );
}

// F-D2-9 — mode-uniformity guard (AG-2 class) for the (c)-diagnostic class: the
// genuine-no-impl dispatch on a method-only import MUST reject uniformly across
// REPL / `--run` / `--link`, and every mode's diagnostic names the trait. A
// per-mode divergence in the dispatch resolution path is itself a defect. Rides
// the W2 flip change-set.
// spec: spec/07-traits.md §7.11.2 — edge (c) + mode uniformity (§10.6.3).
// defect: class=mode-divergence locus=typecheck/int method-import dispatch — no-impl diagnostic across modes found=S113 owner=/dev
#[test]
fn method_only_import_no_impl_diagnostic_mode_uniform() {
    let user = "(import [primitives [Pure Int Bool]])\n\
         (import [ulib [sh]])\n\
         (defn get-s [] (sh true))\n\
         (defn main [] (Pure (get-s)))\n";

    for link in [false, true] {
        let b = Cranelisp::new().with_prelude(PreludeVariant::None);
        let b = if link {
            b.link_then_run("user.cl")
        } else {
            b.run("user.cl")
        };
        let out = b.file("ulib.cl", ULIB).user(user).output();
        let c = format!("{}{}", out.stdout, out.stderr);
        assert!(
            out.status.code() != Some(0) && c.contains("Show"),
            "mode {}: the no-impl dispatch MUST reject and name trait `Show`; got exit {:?}:\n{c}",
            if link { "--link" } else { "--run" },
            out.status.code()
        );
    }

    let repl = repl_with_fixture(
        ("ulib.cl", ULIB),
        "(import [primitives [Int Bool]])\n(import [ulib [sh]])\n(sh true)\n",
    );
    let rc = format!("{}{}", repl.stdout, repl.stderr);
    assert!(
        rc.contains("Show"),
        "REPL: the no-impl dispatch MUST name trait `Show`; got:\n{rc}"
    );
}

// =============================================================================
// F-D2-10 (FIXME 0672) — NULLARY return-dispatch to a type with NO impl MUST
// reject at typecheck (naming the owning trait §7.11.2(c)), uniform with the UNARY
// sibling (F-D2-7), NEVER an `undefined function` codegen leak. This is the general
// return-type-dispatch-to-no-impl gate — independent of method-only import
// (reproduces inline). The UNARY no-impl case already produces the clean
// `no impl of trait X for type Y` reject; the NULLARY sibling leaks to codegen.
// RED ×3 modes + a method-only-import variant.
// =============================================================================

// The inline shape: `Zeroable`/`zed` return-dispatched, an `Int` impl, and a
// `Widget` type with NO impl; `:Widget (zed)` pins the return type to the no-impl
// type. The load-bearing invariant: NO `undefined function` codegen leak, and the
// diagnostic NAMES the owning trait `Zeroable`.
const NOIMPL_INLINE: &str = "(import [primitives [Pure Int]])\n\
     (deftrait Zeroable (zed [] self))\n\
     (impl Zeroable Int (defn zed [] 0))\n\
     (deftype Widget (MkW [:Int n]))\n\
     (defn getw [] (let [x :Widget (zed)] x))\n\
     (defn main [] (Pure (getw)))\n";

fn assert_clean_noimpl_reject(c: &str, mode: &str) {
    assert!(
        !c.contains("undefined function") && !c.contains("codegen error"),
        "[{mode}] a nullary return-dispatch to a no-impl type MUST be caught at \
         typecheck, NEVER leak an `undefined function` codegen error (§7.11.2(c), \
         uniform with the unary sibling); got:\n{c}"
    );
    assert!(
        c.contains("Zeroable"),
        "[{mode}] the no-impl diagnostic MUST name the owning trait `Zeroable` \
         (§7.11.2(c)); got:\n{c}"
    );
}

// F-D2-10 --run face.
// spec: spec/07-traits.md §7.11.2 — edge (c): a no-impl dispatch is a clean
// typecheck-family error naming the owning trait; nullary uniform with unary.
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck return-type-dispatch no-impl gate (nullary accepts then leaks `undefined function` to codegen; unary rejects cleanly) found=S113 owner=/dev
#[test]
fn nullary_return_dispatch_no_impl_rejects_naming_trait_run() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .user(NOIMPL_INLINE)
        .output();
    assert_clean_noimpl_reject(&format!("{}{}", out.stdout, out.stderr), "run");
}

// F-D2-10 --link face.
// spec: spec/07-traits.md §7.11.2 — edge (c) (mode uniformity, --link).
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck return-type-dispatch no-impl gate found=S113 owner=/dev
#[test]
fn nullary_return_dispatch_no_impl_rejects_naming_trait_link() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .link_then_run("user.cl")
        .user(NOIMPL_INLINE)
        .output();
    assert_clean_noimpl_reject(&format!("{}{}", out.stdout, out.stderr), "link");
}

// F-D2-10 REPL face.
// spec: spec/07-traits.md §7.11.2 — edge (c) (mode uniformity, REPL).
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck return-type-dispatch no-impl gate found=S113 owner=/dev
#[test]
fn nullary_return_dispatch_no_impl_rejects_naming_trait_repl() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::None)
        .stdin(
            "(import [primitives [Int]])\n\
             (deftrait Zeroable (zed [] self))\n\
             (impl Zeroable Int (defn zed [] 0))\n\
             (deftype Widget (MkW [:Int n]))\n\
             (let [x :Widget (zed)] x)\n",
        )
        .output();
    assert_clean_noimpl_reject(&format!("{}{}", out.stdout, out.stderr), "repl");
}

// F-D2-10 method-only-import variant — the same gate reached via a method-only
// import (trait NOT imported): the nullary `z` (Int impl) dispatched at a no-impl
// `Widget` return type still MUST reject cleanly naming trait `Zero`, never leak.
// spec: spec/07-traits.md §7.11.2 — edge (c): the no-impl diagnostic names the
// owning trait even when the trait was never imported.
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck return-type-dispatch no-impl gate (method-only import) found=S113 owner=/dev
#[test]
fn nullary_return_dispatch_no_impl_method_only_import_rejects_naming_trait() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .file("zlib.cl", ZLIB)
        .user(
            "(import [primitives [Pure Int]])\n\
             (import [zlib [z]])\n\
             (deftype Widget (MkW [:Int n]))\n\
             (defn getw [] (let [x :Widget (z)] x))\n\
             (defn main [] (Pure (getw)))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("undefined function") && !c.contains("codegen error"),
        "[method-only] a nullary method-only-import no-impl dispatch MUST NOT leak \
         `undefined function` at codegen (§7.11.2(c)); got:\n{c}"
    );
    assert!(
        c.contains("Zero"),
        "[method-only] the no-impl diagnostic MUST name the owning trait `Zero` \
         even though it was never imported (§7.11.2(c)); got:\n{c}"
    );
}
