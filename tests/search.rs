// search.rs — Pillar 3 importable-symbol `/search` (Sprint 91, Thread A,
// centerpiece).
//
// `/search <query>` is a default-build (NON-agent-gated) REPL command over
// symbols REACHABLE BUT NOT YET IMPORTED on the lib search path ∪ project root,
// matched by name and/or type signature, exact OR partial. Served by a
// nice-worker background indexer (read-or-produce-`.meta`, eager-from-REPL-
// startup, REPL-only). Design of record: repl/spec.md §17.19,
// design/int/agent.md §25, design/arch/repl-embedded-agent.md §11,
// design/typecheck/signature-match.md.
//
// RED-first: `/search` does not exist yet (Wave 5 lands it). Today the command is
// unknown — these tests fail at runtime (no `/search` results, no index). The
// unit suites for `signature_matches_exact`/`_partial` are /dev-authored in
// `cranelisp-typecheck` (NOT here — a unit test referencing a not-yet-existing
// `fn` would break this binary's compilation).
//
// All e2e — subprocess only. Free-standing: PrimitivesOnly prelude; reachable
// modules built inline in the per-test tmpdir. The default-build framing applies:
// `/search` works WITHOUT the agent feature, so these run in the DEFAULT lane.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

/// A REPL session at a project root containing a reachable-but-unimported sibling
/// module `lib1.cl` (on a lib-dir) that exports a few functions of known shapes,
/// plus a root-level module. The session pipes `cmds` and captures output. The
/// indexer (REPL-only) arms at startup and burns down the reachable modules.
fn search_session(cmds: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        // A reachable-but-unimported module on a lib-dir.
        .file(
            "lib/mathx.cl",
            "(import [primitives [add-i64 eq-i64]])\n\
             (defn gcd2 [x y] (add-i64 x y))\n\
             (defn is-zero [x] (eq-i64 x 0))\n",
        )
        // A reachable-but-unimported module at the PROJECT ROOT.
        .file(
            "rootmod.cl",
            "(import [primitives [add-i64]])\n\
             (defn root-helper [x] (add-i64 x 1))\n",
        )
        .lib_dir("lib")
        .stdin(cmds)
        .output()
}

// ===========================================================================
// A.6 — `/search` query e2e: name + scheme, exact + partial, over lib ∪ root
// ===========================================================================

// spec: repl/spec.md §17.19.2 — a `/search <name>` exact match returns a result
// row with FOUR facets: symbol name + its `:Type` signature + originating module
// + the exact `(import …)` form.
#[test]
fn search_by_name_exact_returns_four_facets() {
    let out = search_session("/search gcd2\n");
    // The four facets render exactly as §17.19.2's own example shows. For a
    // function-typed symbol the `:Type` signature is the WHOLE `(Fn …)` form with
    // FQ leaf type names (`primitives/Int`) inside it — NOT a colon-per-leaf
    // (matching `/sig`/`/list` and the spec's `(Fn [primitives/Int primitives/Int]
    // primitives/Int)` example, which is `:Type`-prefixed as one unit, FQ names
    // appearing but not per-leaf-colon-prefixed).
    out.assert_stdout_contains_all(&[
        "gcd2",                                                // (1) symbol name
        "(Fn [primitives/Int primitives/Int] primitives/Int)", // (2) full `:Type` sig, FQ leaves
        "mathx",                                               // (3) originating module
        "(import [mathx [gcd2]])",                             // (4) the actionable import form
    ]);
}

// spec: repl/spec.md §17.19.1 — `/search <fragment>` partial = case-insensitive
// substring of the bare name. `/search zero` finds `is-zero`.
#[test]
fn search_by_name_partial_substring() {
    let out = search_session("/search zero\n");
    out.assert_stdout_contains("is-zero");
}

// spec: repl/spec.md §17.19.1 — `/search (Fn …)` exact scheme match returns the
// alpha-equivalent symbol(s). `gcd2`/`root-helper` have an Int-arrow shape;
// `(Fn [Int Int] Int)` exact-matches `gcd2`.
#[test]
fn search_by_scheme_exact() {
    let out = search_session("/search (Fn [primitives/Int primitives/Int] primitives/Int)\n");
    out.assert_stdout_contains("gcd2");
}

// spec: repl/spec.md §17.19.1 — `/search (T)` partial = structural-contains: the
// query type-shape appears as a sub-structure of a candidate's scheme.
// `/search primitives/Int` matches any scheme mentioning `Int` (gcd2, is-zero,
// root-helper all do).
#[test]
fn search_by_scheme_partial_contains() {
    let out = search_session("/search primitives/Int\n");
    out.assert_stdout_contains_all(&["gcd2", "is-zero"]);
}

// spec: repl/spec.md §17.19 — reachable scope is the lib search path ∪ the
// project root (R10). A symbol in a lib-dir module (gcd2) AND a symbol in a
// project-root module (root-helper) both surface.
#[test]
fn search_spans_lib_path_and_project_root() {
    let out = search_session("/search primitives/Int\n");
    out.assert_stdout_contains_all(&["gcd2", "root-helper"]);
}

// spec: repl/spec.md §17.19.1 — NEG: an empty/no-match query re-prompts with a
// short self-documenting "no importable symbols matched" note, NEVER an opaque
// error or a crash.
#[test]
fn search_neg_no_match_self_documenting_note() {
    let out = search_session("/search this-symbol-does-not-exist-anywhere\n");
    let lc = out.stdout.to_lowercase();
    assert!(
        lc.contains("no importable") || lc.contains("no match") || lc.contains("nothing"),
        "an empty/no-match `/search` MUST render a self-documenting no-match note \
         (§17.19.1), never an opaque error; stdout={}",
        out.stdout
    );
    // Must not crash.
    assert!(
        out.status.code().is_some(),
        "/search MUST NOT crash the REPL (§17.19.5); status={:?}",
        out.status
    );
}

// spec: repl/spec.md §17.19 — NEG: `/search` covers what is importable-but-not-
// yet-in-scope. A symbol ALREADY imported into the session is NOT re-offered as
// importable. After `(import [mathx [gcd2]])`, `/search gcd2` must not re-offer
// it with an `(import …)` form (it is resident, not reachable-but-unimported).
#[test]
fn search_neg_already_imported_not_relisted() {
    let out = search_session("(import [mathx [gcd2]])\n/search gcd2\n");
    out.assert_stdout_does_not_contain("(import [mathx [gcd2]])");
}

// ===========================================================================
// A.3 — three-branch indexer coverage (skip-claimed / read-`.meta`-no-typecheck
// / typecheck-and-write-`.meta`)
// ===========================================================================

// spec: design/int/agent.md §25.1 — branch (c): a reachable module with no/stale
// `.meta` is typechecked once on the nice worker against throwaway staging, then
// a `.meta` is written via `cache::write_meta` — but NO `.o`. After a search that
// arms the index, the indexed lib module has a `.meta.json` but no `.o`.
#[test]
fn search_branch_c_stale_meta_typechecks_writes_meta() {
    let out = search_session("/search gcd2\n");
    // The branch-(c) write produces a `.meta` for the indexed module …
    assert!(
        out.tmp_exists(".cranelisp-cache/mathx.meta.json"),
        "branch (c) MUST write a `.meta` for the indexed reachable module \
         (design/int/agent.md §25.1); cache dir={:?}",
        out.tmpdir
    );
    // … but NO `.o` (the indexer never object-codegens or register_module's it).
    assert!(
        !out.tmp_exists(".cranelisp-cache/mathx.o"),
        "branch (c) MUST NOT write a `.o` for an INDEXED (not imported) module \
         (design/int/agent.md §25.1 — no object codegen, no register_module)"
    );
}

// spec: design/int/agent.md §25.1 — branch (c) NEG: the indexer writes a `.meta`
// for the indexed module but never an `.o` and never registers it. (Companion to
// the positive: this asserts the no-`.o` invariant in isolation as the negative
// of the codegen path.)
#[test]
fn search_branch_c_neg_no_object_file() {
    let out = search_session("/search root-helper\n");
    assert!(
        !out.tmp_exists(".cranelisp-cache/rootmod.o"),
        "an indexed reachable module MUST NOT produce a `.o` (design/int/agent.md \
         §25.1); the indexer reads-or-produces `.meta` only"
    );
}

// ===========================================================================
// A.4 — no-SharedState-residue keystone `_neg` (the observable consequence)
// ===========================================================================

// spec: design/int/agent.md §25.1 — the keystone +neg, observable form: after a
// burn-down indexing N reachable modules, NO indexed-but-unimported symbol leaks
// into the live session. A `/search`-discoverable symbol (gcd2) that was NOT
// `(import)`ed must NOT appear in `/list` (it is reachable, not resident). The
// SharedState four-map byte-unchanged invariant is the /dev unit-tier mirror;
// this is the user-visible floor.
#[test]
fn search_burndown_neg_no_sharedstate_residue() {
    // Arm the index (a /search burns down the reachable modules), then /list.
    let out = search_session("/search gcd2\n/list\n");
    // The indexed-but-unimported symbol must NOT have leaked into the session's
    // own `/list` (it is reachable via /search + import, not resident).
    // Find the /list output region (after the search) and assert gcd2 is not a
    // listed user/session symbol there. Conservative: gcd2 must not appear as a
    // bound user symbol — it only appears in the /search result region.
    assert!(
        out.status.code().is_some(),
        "the burn-down + /list MUST NOT crash; status={:?}",
        out.status
    );
    // The session has imported nothing, so `/list` must not present gcd2 as a
    // resident user-module function.
    let lc = out.stdout.to_lowercase();
    assert!(
        !lc.contains("user/gcd2"),
        "an indexed-but-unimported symbol MUST NOT leak into the live session as \
         a resident `user/` symbol (no SharedState residue, design §25.1); \
         stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.19 — a symbol FOUND by `/search` but NOT `/import`ed is
// absent from `/info` (reachable, not resident). `/info gcd2` on an unimported
// symbol must report it as not-in-scope, not as a live session binding.
#[test]
fn search_burndown_neg_indexed_symbol_not_in_session() {
    let out = search_session("/search gcd2\n/info gcd2\n");
    let lc = out.stdout.to_lowercase();
    // `/info` on a reachable-but-unimported name must not present it as a bound
    // session symbol (it would say unknown/not-in-scope, possibly suggesting the
    // import). The negative: it must NOT render gcd2 as a resident `user/gcd2`.
    assert!(
        !lc.contains("user/gcd2"),
        "a /search-discovered but unimported symbol MUST NOT be a live session \
         binding (reachable, not resident); stdout={}",
        out.stdout
    );
}

// ===========================================================================
// A.5 — CF.2 containment (the hard ship-gate)
// ===========================================================================

/// A search session whose reachable set includes a 0432-shaped module (an
/// unannotated multi-clause `defn` with a cross-variant self-call that trips the
/// monomorphiser) ALONGSIDE a well-formed module. The indexer must skip the
/// bad module gracefully and still index the good one.
fn search_session_with_unindexable(cmds: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        // Well-formed reachable module.
        .file(
            "lib/good.cl",
            "(import [primitives [add-i64]])\n\
             (defn good-fn [x] (add-i64 x 2))\n",
        )
        // 0432-shaped reachable module: unannotated multi-clause self-call.
        .file(
            "lib/bad.cl",
            "(import [primitives [eq-i64 sub-i64 add-i64]])\n\
             (defn sum-to ([n] (sum-to n 0)) \
                          ([n acc] (if (eq-i64 n 0) acc \
                                       (sum-to (sub-i64 n 1) (add-i64 acc n)))))\n",
        )
        .lib_dir("lib")
        .stdin(cmds)
        .output()
}

// spec: repl/spec.md §17.19.5 — searching the library MUST NEVER crash the REPL.
// A 0432-shaped reachable module on the lib-path is skipped per-module (CF.2
// catch_unwind), the REPL stays alive, and `/search` over the rest still returns
// results.
#[test]
fn search_cf2_unindexable_module_skipped_no_crash() {
    let out = search_session_with_unindexable("/search good-fn\n");
    // REPL stays alive (clean exit, not a signal-kill).
    assert!(
        out.status.code().is_some(),
        "an unindexable reachable module MUST NOT crash the REPL (§17.19.5, CF.2); \
         status={:?} stderr={}",
        out.status,
        out.stderr
    );
    // The good module is still indexed and searchable despite the bad sibling.
    out.assert_stdout_contains("good-fn");
}

// spec: repl/spec.md §17.19.5 — NEG: the failed (0432-shaped) module produces NO
// `.meta` and does NOT kill the nice worker — a subsequent `/search` of OTHER
// modules still succeeds (background capacity intact).
#[test]
fn search_cf2_neg_no_killed_worker_no_meta() {
    let out = search_session_with_unindexable("/search good-fn\n/search good-fn\n");
    // No `.meta` is written for the module that failed to typecheck.
    assert!(
        !out.tmp_exists(".cranelisp-cache/bad.meta.json"),
        "a module that fails to typecheck MUST NOT get a `.meta` written (CF.2 — \
         the failed module is skipped, not cached)"
    );
    // The nice worker survived: a second /search of the good module still works.
    out.assert_stdout_contains("good-fn");
}

// ===========================================================================
// A.7 — eager-from-startup trigger + partial results + cache-hit on import
// ===========================================================================

// spec: design/int/agent.md §25.5 — the burn-down arms EAGERLY at REPL start-up
// (REPL mode), not on the first `/search`. A `/search` issued early may catch it
// mid-flight and serve partial results + an "indexing N modules…" note, but the
// index is NOT gated on the search. We assert the eager behaviour observably: a
// `/search` issued as the FIRST command still returns results (the index was
// armed at startup, not by this search). For a small fixture the burn-down
// completes fast, so the result set is present immediately.
#[test]
fn search_partial_results_during_indexing() {
    let out = search_session("/search gcd2\n");
    // The very first /search returns a result — the index was armed at startup
    // (eager-from-REPL-startup), not as a side effect of this command. (For a
    // larger tree the "indexing N modules…" partial-results note would appear;
    // here the small burn-down completes promptly.)
    out.assert_stdout_contains("gcd2");
}

// spec: design/int/agent.md §25.5 — NEG: in REPL mode indexing begins AT START-UP,
// not gated on first `/search` or agent activation. A session that NEVER issues a
// `/search` still arms + burns down the index at startup (REPL-only invariant),
// so the index `.meta`s exist after a no-search session over reachable modules.
#[test]
fn search_burndown_arms_at_repl_startup_neg_not_on_first_search() {
    // Pipe ONLY a no-op (a newline) — no /search, no agent. The eager startup
    // burn-down must still run in REPL mode.
    let out = search_session("\n");
    assert!(
        out.tmp_exists(".cranelisp-cache/mathx.meta.json"),
        "the burn-down MUST arm at REPL start-up (eager-from-startup, §25.5), NOT \
         be gated on a first `/search` — a no-search REPL session over reachable \
         modules still produces the index `.meta`s; cache dir={:?}",
        out.tmpdir
    );
}

// spec: design/int/agent.md §25.5 — NEG (REPL-only invariant): a `--run`/`--link`
// invocation over a tree with reachable-but-unimported modules produces NO search
// index and NO index-driven `.meta` writes for those modules — the indexer never
// arms outside REPL mode. Here a `--run` driver imports only `mathx`; the
// reachable-but-unimported `unused.cl` must NOT be indexed (no `.meta` for it).
#[test]
fn search_neg_batch_mode_inert_no_index_no_meta_writes() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "lib/mathx.cl",
            "(import [primitives [add-i64]])\n(defn gcd2 [x y] (add-i64 x y))\n",
        )
        // Reachable-but-unimported in batch mode — the indexer must NOT touch it.
        .file(
            "lib/unused.cl",
            "(import [primitives [add-i64]])\n(defn never-indexed [x] (add-i64 x 9))\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [mathx [gcd2]])\n\
             (defn main [] (Pure (gcd2 1 2)))",
        )
        .lib_dir("lib")
        .run("main")
        .output();
    assert_eq!(
        out.status.code(),
        Some(3),
        "the `--run` driver must exit 3 (gcd2 1 2); stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    // The reachable-but-unimported module must NOT have an index-driven `.meta`
    // (batch mode never arms the indexer — REPL-only invariant §25.5).
    assert!(
        !out.tmp_exists(".cranelisp-cache/unused.meta.json"),
        "batch mode (`--run`) MUST NOT arm the indexer — a reachable-but-unimported \
         module MUST NOT get an index-driven `.meta` (REPL-only invariant, §25.5)"
    );
}

// spec: design/int/agent.md §25.5 — a symbol found via `/search` then `(import …)`
// is a `.meta` CACHE-HIT on the live import path: NO re-typecheck. With
// `CRANELISP_MODULE_TRACE=1`, the import of an already-indexed module shows a
// cache-hit rather than a fresh typecheck.
#[test]
fn search_index_to_import_is_meta_cache_hit() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "lib/mathx.cl",
            "(import [primitives [add-i64]])\n(defn gcd2 [x y] (add-i64 x y))\n",
        )
        .lib_dir("lib")
        .env("CRANELISP_MODULE_TRACE", "1")
        // /search arms+indexes mathx (writes its .meta), then import it → the
        // import must be a .meta cache-hit, not a re-typecheck.
        .stdin("/search gcd2\n(import [mathx [gcd2]])\n(gcd2 2 3)\n")
        .output();
    // The import resolves and the call works.
    assert!(
        out.stdout.contains(":primitives/Int 5"),
        "the indexed-then-imported call must work; stdout={}",
        out.stdout
    );
    // The module trace shows a cache-hit for mathx on the import path (it was
    // already indexed → `.meta` present → no re-typecheck).
    let combined = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        combined.contains("cache") && combined.contains("mathx"),
        "an indexed-then-imported module MUST be a `.meta` cache-hit on import \
         (no re-typecheck, §25.5); MODULE_TRACE should show a cache hit for \
         mathx; trace:\n{combined}"
    );
}

// spec: design/int/agent.md §25.1 — floor: clearing the in-memory indices + re-
// scanning `.meta` reproduces the same `/search` results (the indices are derived
// read-caches over `.meta`; no schema bump). Expressed e2e as cross-session
// reproducibility: a SECOND REPL session over the same tmpdir (with the `.meta`s
// already written by the first session) reproduces the same `/search` result.
#[test]
fn search_index_rebuild_from_meta_reproduces_results() {
    // First session: arm + index, writing the `.meta`s.
    let first = search_session("/search gcd2\n");
    assert!(
        first.status.code().is_some(),
        "first search session must not crash; status={:?}",
        first.status
    );
    // Second session over the SAME tmpdir: the index rebuilds from the written
    // `.meta`s and `/search gcd2` reproduces the same result.
    let second = first
        .run_again()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .lib_dir("lib")
        .stdin("/search gcd2\n")
        .output();
    second.assert_stdout_contains("gcd2");
}

// ===========================================================================
// A.9 — nice-worker flush / shutdown lifecycle guards (R18)
// ===========================================================================

// spec: design/int/agent.md §25.5 — NEG: a REPL session shut down while the eager
// burn-down may still be in flight leaves NO corrupt `.meta` (abandon-on-shutdown;
// `.meta` writes are atomic — a half-written module produces no `.meta`, never a
// truncated one). After an immediate-EOF session, any `.meta` present must parse
// as valid JSON (atomic write = whole-or-nothing).
#[test]
fn search_shutdown_mid_burndown_neg_no_corrupt_meta() {
    // Immediate EOF (empty stdin) — the session shuts down promptly; the eager
    // burn-down is abandoned between modules.
    let out = search_session("");
    assert!(
        out.status.code().is_some(),
        "shutdown during burn-down MUST be clean (no crash); status={:?}",
        out.status
    );
    // Any `.meta` that DID get written must be intact (valid JSON) — atomic write
    // means a half-written module leaves no `.meta`, never a truncated one.
    for name in ["mathx.meta.json", "rootmod.meta.json"] {
        let rel = format!(".cranelisp-cache/{name}");
        if out.tmp_exists(&rel) {
            let body = out.read_tmp(&rel);
            // Whole-or-nothing: a complete `.meta.json` is a balanced JSON object
            // (a truncated atomic-write victim would be empty or unbalanced). We
            // check structural wholeness without a JSON dep (serde_json is gated
            // behind the `agent` feature; `/search` is a DEFAULT-build facility).
            let trimmed = body.trim();
            let opens = body.matches('{').count();
            let closes = body.matches('}').count();
            assert!(
                trimmed.starts_with('{') && trimmed.ends_with('}') && opens == closes,
                "an abandoned mid-burn-down `.meta` MUST be whole (atomic write), \
                 never truncated/corrupt (R18); {rel} is not a balanced JSON \
                 object (opens={opens} closes={closes}):\n{body}"
            );
        }
    }
}

// spec: design/int/agent.md §25.1 — the NEXT REPL session after a shutdown-
// interrupted burn-down rebuilds the index cleanly and `/search` returns correct
// results (no stale/partial index poisons the new session).
#[test]
fn search_next_session_rebuilds_index_cleanly_after_interrupt() {
    // First session: immediate EOF (interrupt the burn-down early).
    let first = search_session("");
    // Second session over the same tree: a full /search must return correct
    // results (the index rebuilds cleanly from source/`.meta`).
    let second = first
        .run_again()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .lib_dir("lib")
        .stdin("/search gcd2\n")
        .output();
    second.assert_stdout_contains("gcd2");
}

// spec: design/int/agent.md §25.1 — NEG: a flush / `--link` path drains object
// codegen ONLY and does NOT block on index work — the `IndexModule` worklist is
// never part of a correctness-gating flush. A `--link` over a tree with
// reachable-but-unindexed modules completes (and the produced binary runs)
// WITHOUT waiting on the indexer (and without arming it — batch mode, R18/§25.5).
#[test]
fn flush_neg_does_not_block_on_index_work() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "lib/mathx.cl",
            "(import [primitives [add-i64]])\n(defn gcd2 [x y] (add-i64 x y))\n",
        )
        // Reachable-but-unindexed sibling — must not gate the link.
        .file(
            "lib/extra.cl",
            "(import [primitives [add-i64]])\n(defn extra [x] (add-i64 x 7))\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [mathx [gcd2]])\n\
             (defn main [] (Pure (gcd2 4 5)))",
        )
        .lib_dir("lib")
        .link_then_run("main")
        .output();
    // The link + run completes without blocking on index work (batch mode never
    // arms the indexer; the flush drains object codegen only).
    assert_eq!(
        out.status.code(),
        Some(9),
        "the linked binary must exit 9 (gcd2 4 5); stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    assert!(
        !out.tmp_exists(".cranelisp-cache/extra.meta.json"),
        "a `--link` flush MUST NOT arm/drain the index worklist — the reachable \
         sibling `extra` MUST NOT be indexed (R18 abandon-not-drain + batch-inert)"
    );
}

// ===========================================================================
// S106 — `/search` docstring axis (FIXME 0540) + exact-in-scope surfacing and
// exact-above-partial ranking (FIXME 0543). All RED-first: docstring matching,
// relevance ranking, and the marked-in-scope exact match are not yet implemented.
// ===========================================================================

/// The ordered list of result-symbol names in a `/search` capture. Each result
/// header line has the shape `:<sig> <name>`; the name is the token after the
/// final `") "` (schemes end in `)`; e.g. `:(Fn [..] primitives/Int) gcd2`).
fn search_result_order(stdout: &str) -> Vec<String> {
    let mut names = Vec::new();
    for line in stdout.lines() {
        let t = line.trim();
        if t.starts_with(":(") || (t.starts_with(':') && t.contains(") ")) {
            if let Some(name) = t.rsplit(") ").next() {
                let name = name.trim();
                if !name.is_empty() && !name.contains(' ') {
                    names.push(name.to_string());
                }
            }
        }
    }
    names
}

/// A search session whose reachable lib module carries docstrings, for the
/// docstring-axis and ranking tests. `foo`-style names left to the caller.
fn search_session_docs(cmds: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "lib/docmod.cl",
            "(import [primitives [add-i64]])\n\
             (defn gcd2 \"compute the greatest common divisor of two integers\" \
             [x y] (add-i64 x y))\n\
             (defn divisor-count \"count something\" [x] (add-i64 x 1))\n",
        )
        .lib_dir("lib")
        .stdin(cmds)
        .output()
}

// spec: repl/spec.md §17.19.1 — the docstring axis: a query that appears in a
// symbol's DOCSTRING (but not its name or scheme) MUST surface that symbol. RED on
// HEAD (FIXME 0540): only name/scheme axes exist, so a docstring-only query returns
// the no-match note.
#[test]
fn search_matches_docstring_only_hit() {
    let out = search_session_docs("/search divisor\n");
    // `gcd2`'s docstring says "greatest common divisor"; its name/scheme do not
    // contain "divisor". The docstring axis MUST surface it.
    out.assert_stdout_contains("gcd2");
}

// spec: repl/spec.md §17.19.1a — ranking: a name hit MUST rank above a
// docstring-only hit. Query "divisor" matches `divisor-count` by NAME and `gcd2`
// only by DOCSTRING; `divisor-count` MUST precede `gcd2`. RED on HEAD (FIXME
// 0540/0543): no docstring axis and no relevance ranking (alphabetical only).
#[test]
fn search_docstring_hit_ranked_below_name_scheme_neg() {
    let out = search_session_docs("/search divisor\n");
    let order = search_result_order(&out.stdout);
    let pos_name = order.iter().position(|n| n == "divisor-count");
    let pos_doc = order.iter().position(|n| n == "gcd2");
    assert!(
        pos_name.is_some() && pos_doc.is_some(),
        "both the name hit `divisor-count` and the docstring-only hit `gcd2` MUST \
         appear (§17.19.1a); order={order:?}\nstdout:\n{}",
        out.stdout
    );
    assert!(
        pos_name < pos_doc,
        "a NAME hit (`divisor-count`) MUST rank ABOVE a docstring-only hit (`gcd2`) \
         (§17.19.1a tier 1 vs tier 6); order={order:?}\nstdout:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §17.19.1 — NEG: a query matching NO name, NO scheme, and NO
// docstring returns the self-documenting no-match note — the docstring axis does
// not manufacture spurious hits. GREEN-expected guard.
#[test]
fn search_docstring_no_false_hit_neg() {
    let out = search_session_docs("/search zzzncomatchanywhere\n");
    let lc = out.stdout.to_lowercase();
    assert!(
        lc.contains("no importable") || lc.contains("no match") || lc.contains("nothing"),
        "a query matching neither name/scheme nor docstring MUST render the no-match \
         note (§17.19.1), never spurious hits; stdout:\n{}",
        out.stdout
    );
}

/// A search session with (a) an exact name `foo` reachable via the PRELUDE (so it
/// is already in scope) and (b) partial out-of-scope matches `foobar`/`foobaz`.
fn search_session_inscope(cmds: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .prelude("(export [primitives [*]])\n(defn foo [x] (add-i64 x 1))\n")
        .repl()
        .file(
            "lib/more.cl",
            "(import [primitives [add-i64]])\n\
             (defn foobar [x] (add-i64 x 1))\n\
             (defn foobaz [x] (add-i64 x 2))\n",
        )
        .lib_dir("lib")
        .stdin(cmds)
        .output()
}

// spec: repl/spec.md §17.19 (R13) — an EXACT-name match that is already in scope
// MUST be surfaced, MARKED "already in scope — no import needed", rather than
// silently dropped. RED on HEAD (FIXME 0543): `is_already_in_scope` filters the
// exact `foo` out entirely, leaving only the partial `foobar`/`foobaz`.
#[test]
fn search_exact_in_scope_match_surfaced_marked() {
    let out = search_session_inscope("/search foo\n");
    // The exact in-scope `foo` is surfaced with the marker.
    assert!(
        out.stdout.to_lowercase().contains("already in scope"),
        "an EXACT in-scope match (`foo`) MUST be surfaced MARKED `already in scope` \
         rather than dropped (§17.19 R13); stdout:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §17.19.2 — NEG: the marked exact in-scope row does NOT offer
// an `(import …)` form (the symbol is already usable bare). RED on HEAD (the row is
// absent today; after the fix it is shown marked, without an import form).
#[test]
fn search_exact_in_scope_not_offered_import_form_neg() {
    let out = search_session_inscope("/search foo\n");
    assert!(
        !out.stdout.contains("(import [prelude [foo]])"),
        "the marked exact in-scope match MUST NOT offer an `(import …)` form \
         (§17.19.2 R13); stdout:\n{}",
        out.stdout
    );
}

/// A search session whose custom prelude carries a PRIVATE binding `secret`
/// (`defn-`). The prelude provides only its PUBLIC names (§8.8.1), so `secret`
/// is NOT in scope in `user` — no reference can resolve it, and `/search` must
/// not claim it is "already in scope".
fn search_session_private_prelude(cmds: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .prelude("(export [primitives [*]])\n(defn- secret [x] (add-i64 x 1))\n")
        .repl()
        .stdin(cmds)
        .output()
}

// spec: repl/spec.md §17.19 (R13) / spec/08-modules.md §8.8.1 — the prelude
// provides only its PUBLIC names, so a PRIVATE prelude binding (`secret`, a
// `defn-`) is NOT in scope: no reference resolves it. `/search secret` (exact
// name) MUST therefore return NO result row for `secret` — not a row that is
// merely unmarked, but an EMPTY result set (the self-documenting no-match note).
// The leak was the `exact_in_scope_hit` synthesis path (repl.rs ~1304): it
// SYNTHESIZED a row via the prelude-fallback for an exact query that resolved
// in-scope but was absent from the public index (a prelude symbol). Without the
// public-only gate on that fallback, the PRIVATE `secret` synthesized a row
// marked "already in scope". Before the gate landed this was RED: `secret`
// appeared as a marked result row; the gate made `exact_in_scope_hit` return
// None → empty result. This test guards BOTH the synthesis
// (`exact_in_scope_hit`) and mark (`is_already_in_scope`) paths — they share
// the `lookup_with_prelude_fallback` seam.
//
// defect: class=enumeration-miss locus=src/repl.rs::exact_in_scope_hit found=S108 owner=/dev
#[test]
fn search_private_prelude_binding_returns_no_result_row_neg() {
    let out = search_session_private_prelude("/search secret\n");
    let lc = out.stdout.to_lowercase();
    // (a) The result SET is empty — the no-match note, not a (marked) row. On a
    //     revert of the gate, `secret` synthesizes a marked row and this note is
    //     replaced by that row → the assertion fails (pins the result-set intent).
    assert!(
        lc.contains("no importable") || lc.contains("no match") || lc.contains("nothing"),
        "a PRIVATE prelude binding is NOT in scope — `/search secret` MUST return \
         NO result row (the empty-set no-match note), not synthesize a marked \
         in-scope row (§8.8.1, §17.19.1); stdout:\n{}",
        out.stdout
    );
    // (b) The mark path too — no "already in scope" claim for the private name.
    assert!(
        !lc.contains("already in scope"),
        "`/search secret` MUST NOT mark the PRIVATE prelude binding `already in \
         scope — no import needed` (§8.8.1); stdout:\n{}",
        out.stdout
    );
    // (c) A private name is not importable either (§5.9) — no import offer.
    out.assert_stdout_does_not_contain("(import [prelude [secret]])");
}

// spec: repl/spec.md §4.1.10 / spec/08-modules.md §8.8.1 — a bare reference to a
// PRIVATE prelude binding takes the UNBOUND path: the prelude provides only its
// public names, so `secret` is not in scope and MUST display as unbound, NOT as
// an in-scope symbol. (Resolution already filtered the private prelude head; this
// test guards that the display/enumeration seam was brought into agreement by the
// same public-only gate.)
#[test]
fn bare_private_prelude_reference_is_unbound() {
    let out = search_session_private_prelude("secret\n");
    let lc = out.stdout.to_lowercase();
    assert!(
        lc.contains("unbound") || lc.contains("undefined"),
        "a bare reference to a PRIVATE prelude binding MUST take the unbound path \
         (§4.1.10), never display as an in-scope symbol; stdout:\n{}",
        out.stdout
    );
}

/// A search session with an exact OUT-OF-SCOPE match `beta` and partial matches
/// `alpha-beta` (interior substring) and `beta-gamma` (prefix). Alphabetically
/// `alpha-beta` sorts first — so alphabetic order buries the exact match.
fn search_session_ranking(cmds: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "lib/g.cl",
            "(import [primitives [add-i64]])\n\
             (defn beta [x] (add-i64 x 1))\n\
             (defn alpha-beta [x] (add-i64 x 2))\n\
             (defn beta-gamma [x] (add-i64 x 3))\n",
        )
        .lib_dir("lib")
        .stdin(cmds)
        .output()
}

// spec: repl/spec.md §17.19.1a — an exact-name match MUST rank ABOVE partial
// substring matches. `/search beta` MUST list exact `beta` before `alpha-beta`
// (interior substring). RED on HEAD (FIXME 0543): results sort alphabetically, so
// `alpha-beta` precedes `beta`.
#[test]
fn search_exact_ranked_above_partial() {
    let out = search_session_ranking("/search beta\n");
    let order = search_result_order(&out.stdout);
    let pos_exact = order.iter().position(|n| n == "beta");
    let pos_partial = order.iter().position(|n| n == "alpha-beta");
    assert!(
        pos_exact.is_some() && pos_partial.is_some(),
        "both the exact match `beta` and the partial `alpha-beta` MUST appear; \
         order={order:?}\nstdout:\n{}",
        out.stdout
    );
    assert!(
        pos_exact < pos_partial,
        "the EXACT-name match `beta` MUST rank ABOVE the partial substring match \
         `alpha-beta` (§17.19.1a tier 1 vs tier 4), not sort alphabetically; \
         order={order:?}\nstdout:\n{}",
        out.stdout
    );
}

// ===========================================================================
// S108 (Increment 2) — `/search` indexes the BUILT-IN SEEDED modules (E1)
//
// The importable-symbol indexer enumerates the reachable set as the `.cl`
// modules on the lib-path ∪ project root (`resolve_module_file`). The built-in
// `primitives` module is bootstrap-seeded — it has NO `.cl` file — so it is
// never enumerated, and every primitive (`vec-len`, `str-len`, …) is invisible
// to `/search` even though `(primitives/vec-len [1 2 3])` evaluates. The S108
// user ruling (repl/spec.md §17.19 R10) brings seeded modules into scope: the
// reachable set = lib-path ∪ project-root `.cl` modules ∪ the built-in seeded
// modules (`primitives`, seeded `macros`).
// ===========================================================================

// spec: repl/spec.md §17.19 — R10 reachable scope INCLUDES the built-in seeded
// modules: `/search vec-len`, with `vec-len` NOT bare-in-scope (no prelude), MUST
// surface `primitives/vec-len` and offer the `(import [primitives [vec-len]])`
// payoff. RED on HEAD: the indexer omits seeded modules, so the query returns the
// "no importable symbols matched 'vec-len'" note. Owner: /dev (src/, int).
//
// The import form is the load-bearing, spec-exact assertion — §17.19 R10 names
// `(import [primitives [vec-len]])` verbatim and §17.19.2 facet 4 makes it the
// actionable payoff; it also carries the symbol-name (facet 1) and module (facet
// 3) facets, so a substring test on it proves the whole row surfaced. Rendering
// is /dev-owned, so we substring-match the payoff rather than a full row layout.
//
// defect: class=enumeration-miss locus=src/session_v4/index_worker.rs::resolve_module_file found=S108 owner=/dev
#[test]
fn search_finds_seeded_primitive_offers_import() {
    // No prelude — `vec-len` is NOT bare-in-scope, but `primitives/vec-len` is
    // bootstrap-seeded (primitives are seeded regardless of prelude).
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::None)
        .stdin("/search vec-len\n")
        .output();
    // The seeded primitive MUST surface with its actionable import-form payoff.
    out.assert_stdout_contains_all(&[
        "vec-len",                         // (1) symbol-name facet
        "(import [primitives [vec-len]])", // (4) the actionable payoff (§17.19 R10, §17.19.2)
    ]);
}

// spec: repl/spec.md §17.19 — R13 companion for a SEEDED symbol: when `vec-len`
// IS bare-in-scope (here via the primitives-glob prelude re-export), its exact
// row is shown-but-MARKED `already in scope — no import needed` and MUST NOT
// offer the `(import [primitives [vec-len]])` form. This is GREEN on HEAD (the
// exact-in-scope R13 path reaches the live symbol table directly, independent of
// the importable index) — it is a REGRESSION GUARD: after E1 adds seeded modules
// to the importable index, the in-scope exact match MUST stay MARKED and MUST NOT
// start offering an import form for a symbol the user can already reference bare.
#[test]
fn search_seeded_primitive_already_in_scope_marked_no_import() {
    // `(export [primitives [*]])` re-exports the primitives as bare names through
    // the user module's implicit prelude glob, so `vec-len` is bare-in-scope.
    let out = Cranelisp::new()
        .prelude("(export [primitives [*]])\n")
        .repl()
        .stdin("/search vec-len\n")
        .output();
    assert!(
        out.stdout.to_lowercase().contains("already in scope"),
        "an EXACT in-scope seeded match (`vec-len`) MUST be surfaced MARKED \
         `already in scope — no import needed`, not dropped (§17.19 R13); \
         stdout:\n{}",
        out.stdout
    );
    out.assert_stdout_does_not_contain("(import [primitives [vec-len]])");
}

// spec: repl/spec.md §17.19.3 — the not-ready note (`indexing N module(s)…`)
// lifecycle under a SEEDED-vs-FILE module-name COLLISION. A user file named
// `primitives.cl` (or `macros.cl`) enumerates to the SAME module name as a
// bootstrap-seeded module. The I-1 fix (`arm_burndown`'s `modules.retain(|m|
// !seeded_modules.contains(m))`) keeps the two feeds DISJOINT: the colliding
// file is dropped from the file worklist BEFORE arming, so the already-
// typechecked-and-mounted seeded module wins and `pending_count` settles to 0.
// WITHOUT that retain filter the colliding file is counted in `enumerated_total`
// (via `arm`) AND the seeded module is `record_preindexed`'d (+1 both
// `enumerated_total` and `indexed`) — a permanent double-count that wedges
// `pending_count` at ≥1 FOREVER, so EVERY `/search` serves a stuck
// `; indexing 1 module(s)… (results may be incomplete)` not-ready note and
// `; search index complete.` never fires.
//
// The wedge is DETERMINISTIC (permanent, not a race), so — unlike the timing-
// coupled E2 lifecycle messages deferred below — it IS e2e-testable: `/search`'s
// handler (`src/repl.rs::handle_search`) calls `wait_for_index_settled` (a
// bounded 5s poll to `pending_count()==0`) BEFORE serving. On HEAD the tiny
// burn-down settles in ms → the wait returns with pending==0 → NO note. A wedged
// index instead spins the full timeout and still serves the note. The note's
// presence AFTER the SUT's own settle-wait is therefore a reliable wedge signal,
// not the arm-vs-serve race. This test relies on the SUT-side settle mechanism,
// so it needs no harness-side settle hook.
//
// defect: class=enumeration-miss locus=src/session_v4/index_worker.rs::arm_burndown found=S108 owner=/dev
#[test]
fn search_seeded_file_name_collision_does_not_wedge_pending_note() {
    // A user file at the PROJECT ROOT named `primitives.cl` — its enumerated
    // module name (`primitives`) COLLIDES with the bootstrap-seeded `primitives`
    // module. Innocuous body: an identity `defn` (no imports needed). No prelude,
    // so `vec-len` is not bare-in-scope and the importable-index path is exercised.
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::None)
        .file("primitives.cl", "(defn shadow-me [x] x)\n")
        .stdin("/search vec-len\n")
        .output();
    out
        // (1) seeded-wins: the REAL seeded primitive `vec-len` surfaces with its
        //     actionable import payoff — the colliding file must NOT shadow or
        //     replace the seeded `primitives` module in results (§17.19 R10). The
        //     file defines no `vec-len`, so the payoff proves the seeded feed
        //     survived the collision, not the file.
        .assert_stdout_contains_all(&["vec-len", "(import [primitives [vec-len]])"])
        // (2) not-wedged: after the SUT's bounded settle-wait, `/search` output
        //     MUST NOT carry a stuck not-ready note. Its presence after settle =
        //     the collision wedged `pending_count` (the retain filter defeated).
        .assert_stdout_does_not_contain("results may be incomplete")
        .assert_stdout_does_not_contain("indexing");
}

// ===========================================================================
// S108 (Increment 3) — E3: `/search` drops an already-LOADED module's
// importable-but-not-in-scope symbols.
//
// `/search`'s reachable set is (per §17.19 R10) the union of file-resolved lib/
// project-root `.cl` modules, the built-in seeded modules (Inc2), AND the
// live/registered modules already loaded into the session. Branch (a) of the
// indexer (`is_registered(module) → mark_skipped`) records ZERO importable rows
// for a loaded module, so a symbol that is importable-but-not-bare-in-scope
// (defined in a module some OTHER symbol of which was imported) is invisible to
// `/search`. This is the THIRD sighting of the `enumeration-miss` class in the
// `/search` indexer (Inc2 seeded modules = first/second; E3 loaded modules).
//
// Deterministic fixture (SPRINT.md §E3): `foo.cl` defines `count` + `other`; the
// prelude `(export [foo [other]])` LOADS/registers `foo` AND publicly re-exports
// `other`, so the implicit-prelude glob (§8.8.1 — provides the prelude's PUBLIC
// names) puts `other` in the user module's scope; `count` is neither exported nor
// imported by the prelude, so it stays importable-but-not-in-scope. `/search count`
// MUST surface `foo/count` with the `(import [foo [count]])` payoff. Serve
// determinism via the SUT's own settle-wait (`handle_search` →
// `wait_for_index_settled`), the Inc2 pattern — no new harness infra.
//
// NB: the prelude line MUST be `export`, not `import`. A private `(import [foo
// [other]])` binds `other` PRIVATE in the prelude (§8.4.0), so it is NOT a public
// name of the prelude and the implicit-prelude glob does NOT provide it to the
// user (verified S108: bare `other` is `undefined variable` under a private import,
// and `/search other` offers an import form rather than marking it in-scope). The
// R13 in-scope control below requires `other` to be LEGITIMATELY in scope, which
// only a public re-export (`export`) achieves.
// ===========================================================================

/// An E3 session: a project whose prelude `(export [foo [other]])` LOADS `foo`
/// (defining `count` + `other`) into the session AND publicly re-exports `other`,
/// so `other` is in the user module's scope while `count` stays importable-but-
/// not-in-scope, plus an UNLOADED reachable sibling `unloaded.cl` (defining
/// `unloaded-count`) on the same lib-dir. Pipes `cmds` and captures. Both feeds
/// (loaded-module live table + unloaded-module file resolution) must contribute rows.
fn e3_search_session(cmds: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        // Prelude PUBLICLY re-exports ONE symbol of `foo` — loads/registers the
        // module and makes `other` a public prelude name (→ in the user's scope via
        // the implicit-prelude glob, §8.8.1), while `count` stays importable-but-
        // not-in-scope. MUST be `export`, not `import`: a private import binds
        // `other` private in the prelude (§8.4.0) → not provided to the user.
        .prelude("(export [primitives [*]])\n(export [foo [other]])\n")
        .repl()
        // The LOADED module: `count` (not in scope) + `other` (re-exported via prelude).
        .file(
            "lib/foo.cl",
            "(export [primitives [*]])\n(defn count [x] x)\n(defn other [x] x)\n",
        )
        // An UNLOADED reachable sibling — indexed via the file feed (branches b/c),
        // NOT the live-table feed. Its `unloaded-count` shares the `count` substring.
        .file(
            "lib/unloaded.cl",
            "(export [primitives [*]])\n(defn unloaded-count [x] x)\n",
        )
        .lib_dir("lib")
        .stdin(cmds)
        .output()
}

// spec: repl/spec.md §17.19 — R10 reachable scope INCLUDES already-LOADED
// (registered) modules: a symbol that is importable-but-not-bare-in-scope in a
// loaded module MUST surface with its `(import …)` payoff. `foo` is loaded by the
// prelude's `(import [foo [other]])`, so `count` (also defined in `foo`, NOT
// imported) is importable-but-not-in-scope → `/search count` MUST surface
// `foo/count` and offer `(import [foo [count]])`.
//
// RED on HEAD (the E3 defect): branch (a) `mark_skipped`s the loaded module
// `foo`, recording ZERO importable rows for it, so the query surfaces only the
// UNLOADED file-feed hit `unloaded-count` and NOT `foo/count`. The import-form
// payoff is the load-bearing, spec-exact assertion (§17.19 R10 / §17.19.2 facet 4).
//
// defect: class=enumeration-miss locus=src/session_v4/index_worker.rs::index_one_module (branch (a) mark_skipped) found=S108 owner=/dev
#[test]
fn search_finds_loaded_module_not_in_scope_symbol_offers_import() {
    let out = e3_search_session("/search count\n");
    out.assert_stdout_contains_all(&[
        "count",                      // (1) symbol-name facet
        "(import [foo [count]])",     // (4) the actionable payoff for the LOADED module
    ]);
}

// spec: repl/spec.md §17.19 — R13 control for the LOADED feed: the in-scope exact
// match `other` is shown-but-MARKED `already in scope — no import needed` and MUST
// NOT offer an `(import …)` form. `other` is legitimately in scope because the
// prelude PUBLICLY re-exports it (`(export [foo [other]])`), so it is a public
// prelude name provided to the user via the implicit-prelude glob (§8.8.1); a
// private `(import [foo [other]])` would bind it private in the prelude (§8.4.0)
// and it would NOT be in scope — see the fixture note above. GREEN control — guards
// R13 against the Wave-B fix of branch (a): after loaded-module rows enter the
// index, an already-in-scope symbol must NOT start being offered as importable.
#[test]
fn search_loaded_module_in_scope_exact_match_still_marked_not_imported_neg() {
    let out = e3_search_session("/search other\n");
    assert!(
        out.stdout.to_lowercase().contains("already in scope"),
        "an EXACT in-scope match (`other`, imported by the prelude) MUST be surfaced \
         MARKED `already in scope — no import needed`, not dropped (§17.19 R13); \
         stdout:\n{}",
        out.stdout
    );
    // The marked in-scope row MUST NOT offer an import form (it is usable bare).
    out.assert_stdout_does_not_contain("(import [foo [other]])");
}

// spec: repl/spec.md §17.19 — R10 control: an UNLOADED reachable module still
// indexes via the file feed (branches b/c) ALONGSIDE the new live-table feed for
// loaded modules. `unloaded.cl` is reachable but never imported; its
// `unloaded-count` (a `count` substring hit) MUST still surface. GREEN control —
// guards the file path against the Wave-B rewrite of branch (a) (feed-union
// completeness: loaded ∪ file ∪ seeded, no source dropped).
#[test]
fn search_unloaded_module_still_indexes_alongside_loaded_feed_neg() {
    let out = e3_search_session("/search count\n");
    out.assert_stdout_contains("unloaded-count");
}

// ===========================================================================
// S108 (Increment 2) — indexing-lifecycle messages (E2): DEFERRED to /dev unit
// tests. NOT authored here — the two messages are timing-coupled and cannot be
// pinned deterministically in the subprocess harness.
//
// FIXME(/testing): E2's two lifecycle messages resist a deterministic e2e repro
// and were DELIBERATELY not committed here (a racy e2e test is forbidden — root
// CLAUDE.md §Testing / tests/CLAUDE.md "no `timing-sensitive` tests"):
//
//   * "indexing N modules…" (the not-ready note, spec §17.19.3) fires only when a
//     `/search` lands while file modules are still burning down. Empirically the
//     burn-down BEATS the first `/search` even with 30 reachable `.cl` modules on
//     the lib-path (measured 2026-07-11: no note across repeated trials) — there
//     is no way to hold pending_count > 0 at search-serve time deterministically,
//     because seeded modules index synchronously and file modules index faster
//     than the first piped line is served. Whether the note fires is exactly the
//     arm-vs-serve race, which is non-deterministic by construction.
//
//   * "search index complete." (spec §17.19.3, timing (b)) fires only AFTER a
//     not-ready note was shown this session — so it inherits the same
//     non-determinism (no note ⇒ no completion latch armed). Neither message
//     appears on HEAD across repeated trials.
//
// Per /arch's mechanism ruling (SPRINT.md §"Design outcome"), the not-ready-note
// + completion-latch logic is pinned by /dev UNIT tests at the `IndicesInner`
// seam — deterministic there: `take_completion_notice()` check-and-set, the
// `note_shown` gate, and `pending_count` accounting (incl. the `record_preindexed`
// arm-time count in BOTH enumerated_total and indexed). If the harness ever gains
// a way to hold the burn-down open (e.g. an injectable per-module index delay or
// a barrier env var), revisit for a deterministic e2e repro.
// ===========================================================================
