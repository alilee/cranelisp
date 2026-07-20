// multi_sig_module_locality.rs — MC-X2 (S113, review finding 8; FIXED in the W2
// window, these are now regression fences — GREEN).
//
// The defect (was RED pre-W2, attributed /qa): an IMPORTED multi-sig base failed
// even on the DIRECT call path. `(import [mlib [h]]) … (h 1)` → `undefined
// function: h`. The
// multi-sig dispatch machinery (overload gate → carrier writes → mangled-entry
// registration) derives its keys for LOCALLY-defined bases; an imported base's
// call site never gets a consumable carrier/mangled entry, so the backend's keyed
// read misses loudly (correct consumer behaviour — the PRODUCER is the owner).
// Same producer family as R2/D3, module-locality cell: `class=carrier-loss`,
// owner /dev(typecheck). The fix must key by the base's HOME module (storage
// identity, 0621 `storage_fq()` lesson, P24) — `state.current_module` is wrong for
// imported bases.
//
// Pre-existing: NO green cross-module multi-sig cell has ever existed (a
// coverage-matrix miss: module-locality × multi-sig). The LOCAL cell is the GREEN
// twin (module-locality axis {local, imported}). Free-standing (no stdlib).
//
// Landed RED at W2a; FLIPPED GREEN by the W2-window home-module keying fix.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// A library module exporting a MULTI-SIG defn `h` (arity-1 + arity-2 clauses).
const MLIB: &str =
    "(import [primitives [add-i64]])\n(defn h ([x] (add-i64 x 1)) ([a b] (add-i64 a b)))\n";

// Run a two-module `--run`/`--link` program, asserting exit `code`.
fn assert_run_and_link_exit(user: &str, code: i32) {
    for link in [false, true] {
        let b = Cranelisp::new()
            .with_prelude(PreludeVariant::PrimitivesOnly)
            .file("mlib.cl", MLIB);
        let b = if link {
            b.link_then_run("user.cl")
        } else {
            b.run("user.cl")
        };
        b.user(user).output().assert_exit(code);
    }
}

// MC-X2 (direct path) — an imported multi-sig base `h`, called on its arity-1
// clause `(h 1)` → 2. Was RED pre-W2 (`undefined function: h` at codegen — the
// imported base's call site got no carrier/mangled entry); fixed by keying on the
// base's home module (W2). GREEN regression fence.
// spec: spec/05-definitions.md §5.1.2 — a multi-sig defn is callable across a
// module boundary exactly as a single-sig defn is.
// defect: class=carrier-loss locus=crates/cranelisp-typecheck multi-sig dispatch carrier/mangled-entry keyed by state.current_module (wrong for imported bases; must key by the base's HOME module) found=S113 owner=/dev
#[test]
fn imported_multi_sig_base_direct_call_dispatches() {
    assert_run_and_link_exit(
        "(import [primitives [Pure]])\n\
         (import [mlib [h]])\n\
         (defn main [] (Pure (h 1)))\n",
        2,
    );
}

// MC-X2 (dispatch-requiring TWIN) — the same imported base called on its arity-2
// clause `(h 3 4)` → 7, forcing the overload gate to select among clauses. Was
// RED pre-W2 (same carrier-loss); fixed W2. The twin isolates dispatch-selection
// from the plain call: both work now the base is keyed by its home module.
// spec: spec/05-definitions.md §5.1.2 — arity dispatch works across a module boundary.
// defect: class=carrier-loss locus=crates/cranelisp-typecheck multi-sig dispatch carrier/mangled-entry keyed by state.current_module (wrong for imported bases; must key by the base's HOME module) found=S113 owner=/dev
#[test]
fn imported_multi_sig_base_dispatch_requiring_call() {
    assert_run_and_link_exit(
        "(import [primitives [Pure]])\n\
         (import [mlib [h]])\n\
         (defn main [] (Pure (h 3 4)))\n",
        7,
    );
}

// MC-X2 (REPL face of the direct path). Was RED pre-W2; GREEN fence now.
// spec: spec/05-definitions.md §5.1.2 — multi-sig call across a module boundary (REPL).
// defect: class=carrier-loss locus=crates/cranelisp-typecheck multi-sig dispatch carrier/mangled-entry keyed by state.current_module (wrong for imported bases; must key by the base's HOME module) found=S113 owner=/dev
#[test]
fn imported_multi_sig_base_direct_call_repl() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("mlib.cl", MLIB)
        .stdin("(import [mlib [h]])\n(h 1)\n")
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains(":primitives/Int 2"),
        "[repl] `(h 1)` on the imported multi-sig base MUST dispatch to the arity-1 \
         clause → 2; got:\n{c}"
    );
}

// MC-X2 LOCAL GREEN TWIN (the module-locality axis {local, imported}, local cell)
// — the IDENTICAL multi-sig base defined LOCALLY dispatches on both the direct and
// the arity-2 path. This is the twin the imported cells must converge onto; it is
// GREEN today and must stay GREEN (the fix keys imported bases by home module
// WITHOUT perturbing the local path).
// spec: spec/05-definitions.md §5.1.2 — a locally-defined multi-sig defn dispatches.
#[test]
fn local_multi_sig_base_direct_and_dispatch_green_twin() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(import [primitives [Pure add-i64]])\n\
             (defn h ([x] (add-i64 x 1)) ([a b] (add-i64 a b)))\n\
             (defn main [] (Pure (add-i64 (h 1) (h 3 4))))\n",
        )
        .output();
    // (h 1) = 2, (h 3 4) = 7, sum = 9.
    out.assert_exit(9);
}
