//! Restart × session-end-state evidence. Each case owns a fresh temporary
//! project and varies only the restart or persisted-state condition named by
//! the test.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn prims_session(stdin: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(stdin)
        .output()
}

/// End state A: a healthy session — one defn + one call, then `/quit`.
const HEALTHY: &str = "(defn keep [:Int x] (add-i64 x 3))\n(keep 1)\n/quit\n";

/// End state B: an incompatible replacement was rejected, so the prior
/// coherent `f`/`k` definitions are the only source that may be restored.
const REJECTED_CHANGE: &str = "(defn f [:Int x] (add-i64 x 1))\n\
                               (defn k [:Int y] (f y))\n\
                               (defn f [:String s] (str-len s))\n\
                               /quit\n";

const VERIFY_RETAINED: &str = "(k 3)\n";

// =============================================================================
// Row E1 — healthy definitions × {clean, --no-cache, cache-wiped}
// =============================================================================

// spec: repl/spec.md §15.2 — session restore: definitions from the previous
// session survive a clean restart. GREEN control (the grid's origin cell).
#[test]
fn healthy_defns_restart_clean_restores() {
    prims_session(HEALTHY)
        .assert_ok()
        .run_again()
        .repl()
        .stdin("(keep 4)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 7");
}

// spec: repl/spec.md §15.2 — restore goes through the normal module graph
// pipeline: with the cache bypassed (`--no-cache`), the backing file alone
// reproduces the session. GREEN control.
#[test]
fn healthy_defns_restart_no_cache_restores() {
    prims_session(HEALTHY)
        .assert_ok()
        .run_again()
        .repl()
        .cli_flag("--no-cache")
        .stdin("(keep 4)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 7");
}

// spec: repl/spec.md §15.2 — a wiped cache directory is the first-session
// shape with an existing backing file: restore recompiles from source.
// GREEN control (dirty-world staging: the wipe is deliberate).
#[test]
fn healthy_defns_restart_cache_wiped_restores() {
    let first = prims_session(HEALTHY).assert_ok();
    std::fs::remove_dir_all(first.tmpdir.join(".cranelisp-cache")).expect("wipe .cranelisp-cache");
    first
        .run_again()
        .repl()
        .stdin("(keep 4)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 7");
}

// =============================================================================
// Row E2 — rejected replacement × {--no-cache, cache-wiped}
// =============================================================================

// spec: repl/spec/18-redefinition.md §18.2, §18.8 — rejection does not write
// the candidate source; a no-cache restart restores the prior coherent world.
#[test]
fn rejected_change_restart_no_cache_restores_prior_source() {
    prims_session(REJECTED_CHANGE)
        .assert_ok()
        .assert_stdout_contains("cannot redefine user/f")
        .run_again()
        .repl()
        .cli_flag("--no-cache")
        .stdin(VERIFY_RETAINED)
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 4")
        .assert_stdout_does_not_contain("has errors");
}

// spec: repl/spec/18-redefinition.md §18.2, §18.8 — the same prior-source
// reconstruction holds when the cache directory is absent.
#[test]
fn rejected_change_restart_cache_wiped_restores_prior_source() {
    let first = prims_session(REJECTED_CHANGE)
        .assert_ok()
        .assert_stdout_contains("cannot redefine user/f");
    let cache = first.tmpdir.join(".cranelisp-cache");
    if cache.exists() {
        std::fs::remove_dir_all(&cache).expect("wipe .cranelisp-cache");
    }
    first
        .run_again()
        .repl()
        .stdin(VERIFY_RETAINED)
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 4")
        .assert_stdout_does_not_contain("has errors");
}

// =============================================================================
// Row E3 — macro-defining-macro × --no-cache (clean cell = the /port D1 guard
// in tests/repl_persist.rs; this is its --no-cache neighbour — D1's report
// explicitly notes `--no-cache` does not recover, pinned here)
// =============================================================================

/// The D1 mechanism fixture — a macro-defining macro mirroring stdlib `def`,
/// hosted in a local module (stdlib-free per tests/CLAUDE.md). Same fixture
/// as tests/repl_persist.rs::MDEF_MODULE.
const MDEF_MODULE: &str = "(import [primitives [*]])\n\
                           (defmacro mdef \"define a named value\" [name value]\n\
                           \x20 (match name\n\
                           \x20   [(macros/SexpSym s)\n\
                           \x20    (let [impl-name (macros/SexpSym (primitives/str-concat s \"-def\"))]\n\
                           \x20      `(begin\n\
                           \x20        (defn ~impl-name [] ~value)\n\
                           \x20        (defmacro ~name [] (macros/SexpList (macros/SCons ~(primitives/quote-sexp impl-name) macros/SNil)))))\n\
                           \x20    _ name]))\n";

// spec: repl/spec.md §15.1 — round-trip MUST hold through every restart
// mode: `--no-cache` recompiles the regenerated backing file from source, so
// a poisoned regeneration (D1: expansion artifact + original call form
// co-persisted) locks the user out even WITHOUT the cache. RED on HEAD
// (/port D1 class; probed: exit 1, `defmacro name must be a symbol`).
#[test]
fn macro_defining_macro_restart_no_cache_recovers() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("mac.cl", MDEF_MODULE)
        .stdin("(import [mac [mdef]])\n(mdef x 1)\nx\n/quit\n")
        .output();
    assert!(
        first.status.success() && first.stdout.contains(":primitives/Int 1"),
        "session 1 sanity: `x` evaluates to 1; stdout={} stderr={}",
        first.stdout,
        first.stderr
    );
    first
        .run_again()
        .repl()
        .cli_flag("--no-cache")
        .stdin("x\n")
        .output()
        .assert_ok()
        .assert_stdout_does_not_contain("defmacro name must be a symbol")
        .assert_stdout_contains(":primitives/Int 1");
}

// =============================================================================
// Row E4 — accepted caller-free type change × cache-wiped
// =============================================================================

// spec: repl/spec/18-redefinition.md §18.1, §18.8 — an accepted caller-free
// type change restores correctly from source without its cache.
#[test]
fn caller_free_type_change_restart_cache_wiped_recompiles_from_source() {
    let first = prims_session(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (defn f [:String s] (str-len s))\n\
         (f \"hi\")\n\
         /quit\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 2");
    let cache = first.tmpdir.join(".cranelisp-cache");
    if cache.exists() {
        std::fs::remove_dir_all(&cache).expect("wipe .cranelisp-cache");
    }
    first
        .run_again()
        .repl()
        .stdin("(f \"abc\")\n/quit\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 3");
}

// =============================================================================
// Row E5 — `/mod`-touched module end state × {clean, cache-wiped}
// =============================================================================

// spec: repl/spec.md §15.1 — definitions entered under `/mod <m>` persist to
// THAT module's backing file (m.cl) and survive a clean restart, importable
// as ordinary module members. GREEN pin (probed: m.cl gains the defn; the
// restarted session imports and calls it).
#[test]
fn mod_touched_module_restart_clean_restores_new_symbol() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("m.cl", "(defn mf [:Int x] (add-i64 x 1))\n")
        .stdin(
            "(import [m [mf]])\n\
             (mf 1)\n\
             /mod m\n\
             (defn mh [:Int x] (add-i64 (mf x) 5))\n\
             (mh 1)\n\
             /mod user\n\
             /quit\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 7");
    // The touched module's backing file carries the new definition.
    assert!(
        first.read_tmp("m.cl").contains("(defn mh"),
        "the /mod-entered definition must persist to m.cl; m.cl:\n{}",
        first.read_tmp("m.cl")
    );
    first
        .run_again()
        .repl()
        .stdin("(import [m [mh]])\n(mh 2)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 8");
}

// spec: repl/spec.md §15.1 — the same end state restores from source alone
// (cache wiped). GREEN pin.
#[test]
fn mod_touched_module_restart_cache_wiped_restores_new_symbol() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("m.cl", "(defn mf [:Int x] (add-i64 x 1))\n")
        .stdin(
            "(import [m [mf]])\n\
             /mod m\n\
             (defn mh [:Int x] (add-i64 (mf x) 5))\n\
             /mod user\n\
             /quit\n",
        )
        .output()
        .assert_ok();
    let cache = first.tmpdir.join(".cranelisp-cache");
    if cache.exists() {
        std::fs::remove_dir_all(&cache).expect("wipe .cranelisp-cache");
    }
    first
        .run_again()
        .repl()
        .stdin("(import [m [mh]])\n(mh 2)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 8");
}

// =============================================================================
// Dirty-world cells — staged contents inside fresh tmpdirs (the cells the
// fresh-tmpdir discipline structurally hid, audit §2.3(c))
// =============================================================================

/// A hand-authored batch-style `user.cl` (the D2 precondition).
const HAND_AUTHORED: &str = ";; hand-authored batch module\n\
                             (defmacro twice [e] `(add-i64 ~e ~e))\n\
                             (defn square [x] (mul-i64 x x))\n";

// spec: repl/spec.md §15.1 — regeneration triggers on successful DEFINITIONS
// only, across restarts too: two consecutive expression-only sessions leave
// a pre-existing hand-authored `user.cl` byte-identical. GREEN pin (the
// restart axis of the D2 boundary control in tests/repl_persist.rs).
#[test]
fn hand_authored_user_cl_two_expression_only_sessions_byte_identical() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user(HAND_AUTHORED)
        .stdin("(square 3)\n/quit\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 9");
    let second = first
        .run_again()
        .repl()
        .stdin("(twice (square 2))\n/quit\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 8");
    assert_eq!(
        second.read_tmp("user.cl"),
        HAND_AUTHORED,
        "expression-only sessions MUST NOT rewrite a hand-authored backing \
         file, however many restarts (§15.1)"
    );
}

// spec: repl/spec.md §15.4 — round-trip correctness (invariant 1) for the
// ADOPTED hand-authored file: after a defining turn rewrites it (the D2
// authorship-fidelity TEXT defect is guarded in tests/repl_persist.rs), the
// regenerated file must still LOAD and reproduce the session semantics on
// restart — adoption must never produce a file that cannot restore. GREEN
// pin (probed: macro + defn + new defn all callable after restart).
#[test]
fn hand_authored_user_cl_defining_turn_restart_round_trips_semantically() {
    prims_session_with_user(HAND_AUTHORED, "(defn extra [y] (add-i64 y 10))\n/quit\n")
        .assert_ok()
        .run_again()
        .repl()
        .stdin("(extra (twice (square 3)))\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 28");
}

fn prims_session_with_user(user_cl: &str, stdin: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user(user_cl)
        .stdin(stdin)
        .output()
}

// spec: repl/spec.md §15.2 — a pre-seeded GARBAGE `.meta.json` beside a valid
// backing file MUST NOT prevent restore: the session starts and recompiles
// from source (the cache is an accelerator, never a gate). GREEN pin.
#[test]
fn stale_meta_garbage_json_session_starts_and_recompiles() {
    let first = prims_session(HEALTHY).assert_ok();
    std::fs::write(
        first.tmpdir.join(".cranelisp-cache/user.meta.json"),
        "{garbage not json",
    )
    .expect("stage garbage meta");
    first
        .run_again()
        .repl()
        .stdin("(keep 4)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 7");
}

// spec: repl/spec.md §15.2 — a TRUNCATED (valid-prefix) `.meta.json` likewise
// falls back to source recompilation. GREEN pin (the torn-write shape a
// crashed session can leave behind).
#[test]
fn stale_meta_truncated_json_session_starts_and_recompiles() {
    let first = prims_session(HEALTHY).assert_ok();
    let meta_path = first.tmpdir.join(".cranelisp-cache/user.meta.json");
    let full = std::fs::read_to_string(&meta_path).expect("read meta");
    let cut = full.len().min(120);
    std::fs::write(&meta_path, &full[..cut]).expect("stage truncated meta");
    first
        .run_again()
        .repl()
        .stdin("(keep 4)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 7");
}

// spec: repl/spec.md §15.2 — a complete `.meta.json` whose `.o` object file
// is MISSING must not be served stale or fatal: the session starts and
// recompiles. GREEN pin (the half-wiped-cache shape).
#[test]
fn missing_object_file_with_intact_meta_session_starts_and_recompiles() {
    let first = prims_session(HEALTHY).assert_ok();
    let obj = first.tmpdir.join(".cranelisp-cache/user.o");
    if obj.exists() {
        std::fs::remove_file(&obj).expect("remove user.o");
    }
    first
        .run_again()
        .repl()
        .stdin("(keep 4)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 7");
}
