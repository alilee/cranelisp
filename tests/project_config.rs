// project_config.rs — `Cranelisp.toml` scaffold + additive lib-dir resolution
// (Sprint 91, Thread C, FIXME 0410).
//
// RED-first e2e for:
//   - the project-root scaffold (repl/spec.md §0.5.7): a REPL pointed at a bare
//     project-root directory (the §0.5.1 rule-3 case) scaffolds a default
//     `Cranelisp.toml` + a `[created Cranelisp.toml]` notice; never overwrites;
//     never litters the bare-cwd launch; carries the current `CRANELISP_LIB`
//     paths as a COMMENTED-OUT example; the scaffold changes resolution by
//     nothing (additive union — it cannot suppress a lower tier).
//   - the additive lib-dir search order (spec §8.11.4, settled S91): first-match
//     CLI/programmatic > CRANELISP_LIB (env) > Cranelisp.toml lib-dirs > {root}/
//     stdlib/ default; an empty/absent lib-dirs does NOT suppress {root}/stdlib/.
//
// These fail today because the scaffold writer does not exist yet (Wave 6 lands
// `scaffold_project_config` + the additive `assemble_lib_dirs` UNION).
//
// Free-standing: no stdlib dependency; project trees built inline in the per-test
// tmpdir; the rule-3 trigger is exercised by passing the project-root directory
// NAME as the positional target (cwd = the harness tmpdir).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

// spec: repl/spec.md §0.5.7 — a REPL launched with a project-root-directory
// target (rule 3: `cranelisp myproject` where `myproject/` exists and
// `myproject.cl` does NOT) lacking a `Cranelisp.toml` scaffolds one and emits a
// `[created Cranelisp.toml]` notice at startup.
#[test]
fn scaffold_creates_toml_on_bare_project_root() {
    // Build a bare project-root dir under the tmpdir (cwd). Pass its NAME as the
    // positional target to trigger the §0.5.1 rule-3 directory-as-project path.
    let out = Cranelisp::new()
        .file("myproject/user.cl", "(defn greet [] 0)\n")
        .cli_flag("myproject")
        .stdin("\n")
        .output();
    // The notice is emitted at startup.
    out.assert_stdout_contains("[created Cranelisp.toml]");
}

// spec: repl/spec.md §0.5.7 — NEG: an existing `Cranelisp.toml` is NEVER
// overwritten and NO `[created …]` notice is emitted (idempotent). The
// pre-existing file is left byte-for-byte untouched.
#[test]
fn scaffold_neg_never_overwrites_existing() {
    let sentinel = "# my hand-written config\nlib-dirs = []\n";
    let out = Cranelisp::new()
        .file("myproject/user.cl", "(defn greet [] 0)\n")
        .file("myproject/Cranelisp.toml", sentinel)
        .cli_flag("myproject")
        .stdin("\n")
        .output();
    // The original contents survive byte-for-byte.
    let after = out.read_tmp("myproject/Cranelisp.toml");
    assert_eq!(
        after, sentinel,
        "an existing Cranelisp.toml MUST be left untouched (§0.5.7 invariant 1); \
         got:\n{after}"
    );
    // No create notice — the file already existed.
    out.assert_stdout_does_not_contain("[created Cranelisp.toml]");
}

// spec: repl/spec.md §0.5.7 — NEG: the bare no-target `cranelisp` launch (rule 1,
// cwd default) MUST NOT scaffold a `Cranelisp.toml` (no littering of arbitrary
// directories). No create notice, no file written in cwd.
#[test]
fn scaffold_neg_not_created_on_bare_cwd_repl() {
    let out = Cranelisp::new()
        // No positional target — rule 1 (cwd default).
        .stdin("\n")
        .output();
    assert!(
        !out.tmp_exists("Cranelisp.toml"),
        "the bare-cwd REPL launch MUST NOT write Cranelisp.toml (§0.5.7 rule-1 \
         MUST NOT); the tmpdir cwd contains one unexpectedly"
    );
    out.assert_stdout_does_not_contain("[created Cranelisp.toml]");
}

// spec: spec/08-modules.md §8.11.4 — after scaffolding, lib-dir resolution is
// UNCHANGED (additive union). A module reachable via CRANELISP_LIB still resolves
// in the scaffolded project — the scaffold adds nothing that suppresses the env
// tier. `(val)` → 77 resolves from the env-tier lib even though a fresh
// Cranelisp.toml was scaffolded.
#[test]
fn scaffold_resolution_unchanged_lib_still_loads() {
    // Env-tier lib in a sibling tempdir.
    let env_lib_td = tempfile::tempdir().expect("env_lib TempDir");
    std::fs::write(env_lib_td.path().join("foo.cl"), "(defn val [] 77)\n")
        .expect("write env_lib/foo.cl");

    let out = Cranelisp::new()
        .file(
            "myproject/user.cl",
            "(import [foo [val]])\n(val)\n",
        )
        .cli_flag("myproject")
        .env(
            "CRANELISP_LIB",
            env_lib_td.path().to_str().expect("env_lib path utf8"),
        )
        .stdin("(val)\n")
        .output();
    // The scaffold was created AND the env-tier module still resolves.
    out.assert_stdout_contains_all(&["[created Cranelisp.toml]", ":primitives/Int 77"]);
}

// spec: repl/spec.md §0.5.7 — the generated file carries the current
// CRANELISP_LIB paths as a COMMENTED-OUT example (teaches the schema, adds
// nothing active). The live env path appears in the file, but only on a comment
// line — there is no active (uncommented) `lib-dirs` that injects it.
#[test]
fn scaffold_carries_commented_lib_paths() {
    let env_lib_td = tempfile::tempdir().expect("env_lib TempDir");
    let env_path = env_lib_td.path().to_str().expect("env path utf8").to_string();

    let out = Cranelisp::new()
        .file("myproject/user.cl", "(defn greet [] 0)\n")
        .cli_flag("myproject")
        .env("CRANELISP_LIB", &env_path)
        .stdin("\n")
        .output();
    assert!(
        out.stdout.contains("[created Cranelisp.toml]"),
        "scaffold notice expected; stdout={}",
        out.stdout
    );

    let toml = out.read_tmp("myproject/Cranelisp.toml");
    // The schema is taught via a commented `lib-dirs` example.
    assert!(
        toml.contains("lib-dirs"),
        "the scaffold MUST show the `lib-dirs` schema (§0.5.7 teaching template); \
         got:\n{toml}"
    );
    // Any line mentioning the live env path MUST be a comment (no ACTIVE lib-dirs
    // that would inject it — invariant 4, benign on resolution).
    for line in toml.lines() {
        if line.contains(&env_path) {
            assert!(
                line.trim_start().starts_with('#'),
                "the current CRANELISP_LIB path MUST appear only COMMENTED-OUT \
                 (§0.5.7); active line: {line:?}\nfull file:\n{toml}"
            );
        }
    }
}

// spec: spec/08-modules.md §8.11.4 — search order: when a module name resolves in
// more than one lib directory, first-match precedence is CLI/programmatic >
// CRANELISP_LIB (env) > Cranelisp.toml lib-dirs > {root}/stdlib/ default. The S91
// ruling places ENV BEFORE the toml config tier. Here the env-tier `foo.cl`
// (val→55) MUST win over the toml-tier `foo.cl` (val→13).
#[test]
fn lib_dir_search_order_cli_env_toml_stdlib() {
    let env_lib_td = tempfile::tempdir().expect("env_lib TempDir");
    std::fs::write(env_lib_td.path().join("foo.cl"), "(defn pick [] 55)\n")
        .expect("write env_lib/foo.cl");

    let out = Cranelisp::new()
        .file("Cranelisp.toml", r#"lib-dirs = ["./toml-lib"]"#)
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [foo [pick]])\n\
             (defn main [] (Pure (pick)))\n",
        )
        .file("toml-lib/foo.cl", "(defn pick [] 13)\n")
        .env(
            "CRANELISP_LIB",
            env_lib_td.path().to_str().expect("env_lib path utf8"),
        )
        .run("main")
        .output();
    // Env tier wins per the S91 search order (env BEFORE toml config).
    out.assert_exit(55);
}

// spec: spec/08-modules.md §8.11.4 — NEG: an empty/absent `lib-dirs` does NOT
// suppress the `{project_root}/stdlib/` default tier (the dissolved footgun —
// additive union, no replacing tier). A `Cranelisp.toml` with `lib-dirs = []`
// present, plus a module under `{root}/stdlib/`, MUST still resolve that module.
#[test]
fn lib_dir_union_neg_empty_toml_does_not_suppress() {
    let out = Cranelisp::new()
        // Present config with an EXPLICITLY empty lib-dirs — the old footgun.
        .file("Cranelisp.toml", "lib-dirs = []\n")
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [helper [forty]])\n\
             (defn main [] (Pure (forty)))\n",
        )
        // The {project_root}/stdlib/ default tier still contributes.
        .file("stdlib/helper.cl", "(defn forty [] 40)\n")
        .run("main")
        .output();
    out.assert_exit(40);
}
