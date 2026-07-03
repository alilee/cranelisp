//! S102 Phase-5 Stage-1 — lane L-S3: the file-backed dev-loop
//! (`tests/plan/s102-test-plan.md` §1.3; `tests/plan/coverage-audit-s101.md`
//! §2.4 L-S3, curing miss-pattern P3 — backs Block A4: /port D3 + FIXME 0487).
//!
//! The exemplar-shaped loop as e2e: file-backed modules + `/mod M` turns ×
//! {fresh, cache-restored} × {same-module, cross-module dependents} ×
//! {prelude-using, prelude-free bodies} (the 0487 parity axis), then
//! redefine → cascade → revert → restart. Plus the 0487 introspection half:
//! the names the cascade report prints MUST be pasteable into the
//! introspection commands.
//!
//! Seed cells that stay in their home file (cross-referenced, not
//! duplicated):
//!   - cache-restored × prelude-free × redefine (the /port D3 reduced face,
//!     `unknown type … (from module ``)`) → RED guard
//!     `tests/repl_persist_redefine.rs::redefine_file_backed_module_symbol_after_cache_restore_works_like_fresh`
//!   - fresh × cross-module × third-module dependent → its GREEN control
//!     `…::redefine_file_backed_module_symbol_fresh_session_cross_module_control`
//!
//! Draft-time polarity (probed 2026-07-03 on the CS-A binary):
//!   RED ×6 (flip with Block A4 — CS-D3a/CS-D3b/CS-0487 per
//!   design/int/s102-defect-wave.md):
//!     devloop_cache_restored_prelude_using_mod_turn_compiles   (0487 face 1)
//!     sig_accepts_fq_module_qualified_name                     (0487 face 3)
//!     info_accepts_fq_module_qualified_name                    (0487 face 3)
//!     refs_accepts_fq_module_qualified_name                    (0487 face 3)
//!     sig_imported_name_shows_full_signature_line              (0487 face 3 / §3.8)
//!     cascade_report_broken_name_pasteable_into_info           (0487 face 3)
//!   GREEN ×5 controls/pins.
//! Ledger: tests/plan/ledger.md §"Sprint 102 Phase-5 Stage-1 QA-first RED set".
//!
//! Watch obligation (risk-register #10, qa plan §1.3): when the A2/A4 fixes
//! land, re-probe the two UNREDUCED residues — the D2 hybrid-meta arm and the
//! exemplar's false-`undefined variable: None` faces — against this lane's
//! cells; record outcomes in the ledger.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// =============================================================================
// The dev-loop proper — redefine → cascade → revert → restart
// =============================================================================

// spec: repl/spec.md §18.3 — the full dev-loop over a file-backed module with
// a SAME-module dependent, fresh session: the signature-changing `/mod m`
// turn breaks the dependent TRUE (module-local name, real type error), the
// revert heals it (`recompiled:`), and the world answers correctly after.
// GREEN control (fresh sessions are the working cell; the cache-restored
// sibling is the D3 guard).
#[test]
fn devloop_fresh_same_module_dependent_break_true_and_revert_heal() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "m.cl",
            "(defn mf [:Int x] (add-i64 x 1))\n\
             (defn mg [:Int y] (add-i64 (mf y) 100))\n",
        )
        .stdin(
            "(import [m [mg]])\n\
             (mg 41)\n\
             /mod m\n\
             (defn mf [:String s] (str-len s))\n\
             (defn mf [:Int x] (add-i64 x 1))\n\
             /mod user\n\
             (mg 41)\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains("mg —") // the TRUE break is reported…
        .assert_stdout_contains("; recompiled:") // …and the revert heals
        .assert_stdout_does_not_contain("unknown type")
        .assert_stdout_contains(":primitives/Int 142");
}

// spec: repl/spec.md §18.3 — the CROSS-module dev-loop survives a restart:
// after break → revert in `/mod m`, `/quit` + restart restores the healed
// world from the (unchanged) module sources. GREEN pin — extends the D3
// fresh-session control through the restart axis.
#[test]
fn devloop_fresh_cross_module_revert_then_restart_runs_clean() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("m.cl", "(defn mf [:Int x] (add-i64 x 1))\n")
        .file(
            "n.cl",
            "(import [m [mf]])\n\
             (defn ng [:Int y] (add-i64 (mf y) 100))\n",
        )
        .stdin(
            "(import [n [ng]])\n\
             (ng 41)\n\
             /mod m\n\
             (defn mf [:String s] (str-len s))\n\
             (defn mf [:Int x] (add-i64 x 1))\n\
             /mod user\n\
             (ng 41)\n\
             /quit\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains("n/ng —") // cross-module break, module-qualified
        .assert_stdout_contains("; recompiled:");
    first
        .run_again()
        .repl()
        .stdin("(import [n [ng]])\n(ng 41)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 142");
}

// =============================================================================
// The 0487 parity axis — prelude-using bodies in `/mod` turns
// =============================================================================

// spec: spec/08-modules.md §8.8 — module bodies compile with the implicit
// prelude; a `/mod m` turn defining a fn whose body uses prelude-provided
// operators MUST compile exactly as the module's file body would. FRESH
// session: GREEN control (probed 2026-07-03).
#[test]
fn devloop_fresh_prelude_using_mod_turn_compiles() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .file("m.cl", "(defn mf [x] (+ x 1))\n")
        .stdin(
            "(import [m [mf]])\n\
             (mf 1)\n\
             /mod m\n\
             (defn mh [x] (+ (mf x) 5))\n\
             (mh 1)\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 7")
        .assert_stdout_does_not_contain("undefined variable");
}

// spec: spec/08-modules.md §8.8 — the SAME turn in a CACHE-RESTORED session:
// the module-namespace environment MUST match the environment the module's
// file body was compiled in, regardless of how the module was installed
// (fresh typecheck vs cache restore). RED on HEAD (FIXME 0487 face 1 /
// /port D3 class; probed: `undefined variable: +` — the restored module's
// session env lacks the prelude). Root cause per
// design/int/s102-defect-wave.md: `install_module_session_env` runs only on
// the fresh-typecheck path.
#[test]
fn devloop_cache_restored_prelude_using_mod_turn_compiles() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .file("m.cl", "(defn mf [x] (+ x 1))\n")
        .stdin("(import [m [mf]])\n(mf 1)\n/quit\n")
        .output();
    assert!(
        first.status.success() && first.stdout.contains(":primitives/Int 2"),
        "session 1 sanity: (mf 1) = 2; stdout={} stderr={}",
        first.stdout,
        first.stderr
    );
    first
        .run_again()
        .repl()
        .stdin(
            "(import [m [mf]])\n\
             (mf 1)\n\
             /mod m\n\
             (defn mh [x] (+ (mf x) 5))\n\
             (mh 1)\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_does_not_contain("undefined variable") // the 0487 face
        .assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/08-modules.md §8.9.1 — prelude type aliases (`:Int` for
// `:primitives/Int`) resolve in a `/mod m` defining turn in a fresh session.
// GREEN pin of the 0487 face-2 boundary: fresh works; the cache-restored
// alias face is inside the D3 guard (`unknown type` wall).
#[test]
fn devloop_fresh_mod_turn_bare_type_alias_resolves() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("m.cl", "(defn mf [:Int x] (add-i64 x 1))\n")
        .stdin(
            "(import [m [mf]])\n\
             /mod m\n\
             (defn mh [:Int x] (add-i64 (mf x) 5))\n\
             (mh 1)\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_does_not_contain("unknown type")
        .assert_stdout_contains(":primitives/Int 7");
}

// =============================================================================
// The 0487 introspection half — FQ names must be usable where the REPL's own
// output prints them (repl/spec.md §3.8 + the self-documenting principle)
// =============================================================================

/// One file-backed module + import, for the introspection cells.
fn imported_module_session(stdin: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("m.cl", "(defn mf \"doc mf\" [:Int x] (add-i64 x 1))\n")
        .stdin(stdin)
        .output()
}

// spec: repl/spec.md §3.8 — `/sig` takes a symbol; a module-qualified name is
// a symbol (spec/08-modules.md §8.5.1) and MUST resolve like the bare form.
// RED on HEAD (FIXME 0487 face 3): `/sig m/mf` → `error: unknown symbol
// 'm/mf'` even while bare `mf` is imported and the module is loaded.
#[test]
fn sig_accepts_fq_module_qualified_name() {
    imported_module_session("(import [m [mf]])\n(mf 1)\n/sig m/mf\n")
        .assert_ok()
        .assert_stdout_does_not_contain("unknown symbol")
        .assert_stdout_contains(":(Fn [primitives/Int] primitives/Int) m/mf ; defn - doc mf");
}

// spec: repl/spec.md §3.6 — `/info` on a module-qualified name. RED on HEAD
// (FIXME 0487 face 3): rejected `unknown symbol 'm/mf'`.
#[test]
fn info_accepts_fq_module_qualified_name() {
    imported_module_session("(import [m [mf]])\n(mf 1)\n/info m/mf\n")
        .assert_ok()
        .assert_stdout_does_not_contain("unknown symbol")
        .assert_stdout_contains(":(Fn [primitives/Int] primitives/Int) m/mf ; defn - doc mf");
}

// spec: repl/spec.md §17.6.1 — `/refs <sym>`: the argument grammar includes
// the qualified form the REPL's own reports print. RED on HEAD (FIXME 0487
// face 3): `/refs m/mf` → `unbound symbol 'm/mf'` while bare `/refs mf`
// resolves (green pin below).
#[test]
fn refs_accepts_fq_module_qualified_name() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "m.cl",
            "(defn mf [:Int x] (add-i64 x 1))\n\
             (defn mg [:Int y] (add-i64 (mf y) 100))\n",
        )
        .stdin("(import [m [mg]])\n(mg 1)\n/refs m/mf\n")
        .output()
        .assert_ok()
        .assert_stdout_does_not_contain("unbound symbol")
        .assert_stdout_contains("m/mg"); // the cross-module caller is listed
}

// spec: repl/spec.md §17.6.1 — GREEN pin: bare `/refs mf` lists the
// cross-module caller `m/mg` (probed 2026-07-03). Pins the working half of
// the 0487 face-3 boundary: bare resolution works, FQ is the broken cell.
#[test]
fn refs_bare_name_lists_cross_module_caller_control() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "m.cl",
            "(defn mf [:Int x] (add-i64 x 1))\n\
             (defn mg [:Int y] (add-i64 (mf y) 100))\n",
        )
        .stdin("(import [m [mg]])\n(mg 1)\n/refs mf\n")
        .output()
        .assert_ok()
        .assert_stdout_contains("m/mg");
}

// spec: repl/spec.md §3.8 — `/sig` on an IMPORTED bare name MUST print the
// same primary line as bare lookup (byte-identical; bare lookup renders the
// full `:(Fn …) m/mf ; defn - doc mf` line). RED on HEAD (FIXME 0487 face 3
// minor + §3.8): `/sig mf` prints only `mf ; imported from m/mf` — no
// signature at all.
#[test]
fn sig_imported_name_shows_full_signature_line() {
    imported_module_session("(import [m [mf]])\n(mf 1)\n/sig mf\n")
        .assert_ok()
        .assert_stdout_contains(":(Fn [primitives/Int] primitives/Int) m/mf ; defn - doc mf");
}

// spec: repl/spec.md §18.3 — the cascade report prints module-qualified names
// (`n/ng`); §3.6's self-documentation contract requires those exact names to
// be pasteable into `/info` to read the break details. RED on HEAD (FIXME
// 0487 face 3 — "the transaction's own reports print FQ names the user
// cannot paste into /info").
#[test]
fn cascade_report_broken_name_pasteable_into_info() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("m.cl", "(defn mf [:Int x] (add-i64 x 1))\n")
        .file(
            "n.cl",
            "(import [m [mf]])\n\
             (defn ng [:Int y] (add-i64 (mf y) 100))\n",
        )
        .stdin(
            "(import [n [ng]])\n\
             (ng 41)\n\
             /mod m\n\
             (defn mf [:String s] (str-len s))\n\
             /mod user\n\
             /info n/ng\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains("n/ng —") // the report names it FQ…
        .assert_stdout_does_not_contain("unknown symbol") // …so /info must take it
        .assert_stdout_contains("broken by the redefinition of m/mf");
}
