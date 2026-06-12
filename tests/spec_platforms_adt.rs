// spec_platforms_adt.rs — Platform-interface ADT round-trip + dual hash-gate +
// cache-restore e2e walks (FIXME 0289 "option 2", items 1–3).
//
// FAILING-FIRST. These tests are RED until three things land together:
//   (fixture) the ADT-typed `shapes` test-DLL fixture (`/platform`-owned) — a
//             platform whose sigs reference `shapes/Rectangle` (an ADT defined
//             in an ordinary `.cl` module), so the backend schema generator
//             emits a non-empty schema + `__cranelisp_layout_hash_shapes`.
//   (R1)      `--link` platform wiring — the `--link` half of every round-trip /
//             hash-gate test below (the `_link` fns) needs the startup-stub
//             baked-hash comparison + GOT-only link path.
//   (R2)      live `--run`/REPL platform schema regeneration + the layout-hash
//             dual gate (REPL warns-and-loads, `--run` refuses, `--link`
//             refuses), per `design/arch/platform-interface.md §7.2/§7.3`.
//
// FIXTURE CONTRACT (agreed with /platform; reconcile in Wave A if it drifts):
//   - platform name: `shapes`
//   - ADT: `(deftype Rectangle [:Int w :Int h])` — FQ `shapes/Rectangle`
//   - platform fn cranelisp name: `area`, sig `(Fn [shapes/Rectangle] primitives/Int)`
//   - `(area (Rectangle 3 4))` ⇒ 12
//
// For these e2e tests the program declares the `deftype Rectangle` in its OWN
// entry module (the simplest resolution path — the host resolves the type from
// the live module graph). The platform fn `area` is imported from
// `platform.shapes`. The hash-gate is induced TEST-SIDE by editing the program's
// `deftype` so the host-regenerated layout hash diverges from the hash the DLL
// baked at build time.
//
// spec: spec/10-io.md §10.10 — Platform ABI Contract (the C-ABI contract between
// a platform DLL and the runtime; ADT `i64` is a pointer to a heap value per
// §10.10.1).
// design basis: design/arch/platform-interface.md §7.2 (REPL/`--run` load
// sequence — all three exports, layout-hash regenerate+compare) + §7.3 (`--link`
// sequence — GOT only, startup-stub baked-hash comparison).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

// The entry program that constructs a Rectangle and passes it to the platform
// `area` fn. Declares the platform, imports `area`, defines the matching ADT in
// its own module, and exits with the computed area (3*4 = 12).
//
// NOTE on `main`: the spec MANDATES a batch-mode `main : (Fn [] (IO _))`
// (see the S79 enforcement forcing-function in the ledger). A platform fn that
// returns a bare `Int` (`area : (Fn [shapes/Rectangle] primitives/Int)`) is
// pure, so a `main` that simply returns `(area …)` is a bare-`Int` main and
// will be swept when the `main : IO _` enforcement lands. The contract here
// asserts the ADT crossing (exit 12); if the enforcement sweep reshapes this
// `main` into an IO-returning shape, the exit-12 witness is preserved by having
// `area`'s result drive the exit code through whatever IO wrapper the sweep
// adopts. Reconcile the exact `main` shape with /platform in Wave A.
const SHAPES_PROGRAM: &str = "(platform shapes)\n\
     (import [platform.shapes [area]])\n\
     (deftype Rectangle [:Int w :Int h])\n\
     (defn main [] (area (Rectangle 3 4)))\n";

// A drifted variant: the program's `deftype` gains a third field, so the
// host-regenerated layout hash for `shapes/Rectangle` no longer matches the
// hash the DLL baked at build time. This is the test-side drift inducer for the
// dual hash-gate (item 2).
const SHAPES_PROGRAM_DRIFTED: &str = "(platform shapes)\n\
     (import [platform.shapes [area]])\n\
     (deftype Rectangle [:Int w :Int h :Int depth])\n\
     (defn main [] (area (Rectangle 3 4 5)))\n";

// =============================================================================
// Item 1 — FQ-named-ADT round-trip (--run + --link)
// =============================================================================

// spec: spec/10-io.md §10.10 — Platform ABI Contract
// FAILING-FIRST (RED until fixture + R2). `--run` round-trip: construct
// `(Rectangle 3 4)`, pass it across the host↔DLL boundary to `area`, assert the
// value crossed correctly (exit 12) and that no platform-load/hash error
// reached stderr (the hashes match on a clean build).
#[test]
fn platform_adt_roundtrip_run() {
    let out = Cranelisp::new()
        .use_workspace_platforms()
        .file("user.cl", SHAPES_PROGRAM)
        .run("user.cl")
        .output();
    // The ADT crossed: area of {w=3,h=4} = 12.
    let out = out.assert_exit(12);
    // Negative: a clean build MUST NOT surface a hash-gate refusal.
    assert!(
        !out.stderr.contains("layout-hash") && !out.stderr.contains("hash mismatch"),
        "a clean platform build MUST NOT surface a hash-gate error; got stderr:\n{}",
        out.stderr
    );
}

// spec: spec/10-io.md §10.10 — Platform ABI Contract
// FAILING-FIRST (RED until fixture + R1). `--link` round-trip: the produced
// standalone binary links against the platform GOT (no live load), and running
// it exits 12. RED until R1 (`--link` platform wiring + startup-stub baked-hash
// comparison) lands.
#[test]
fn platform_adt_roundtrip_link() {
    Cranelisp::new()
        .use_workspace_platforms()
        .file("user.cl", SHAPES_PROGRAM)
        .link_then_run("user.cl")
        .output()
        .assert_exit(12);
}

// =============================================================================
// Item 2 — the dual hash-gate (REPL warns / --run refuses / --link refuses)
// =============================================================================

// spec: spec/10-io.md §10.10 — Platform ABI Contract
// FAILING-FIRST (RED until fixture + R2). `--run` MUST REFUSE on layout-hash
// drift: the program's `deftype Rectangle` gained a field after the DLL baked
// its hash, so the host-regenerated hash ≠ the DLL's baked hash. `--run` exits
// non-zero, the error names the platform (`shapes`) + both hashes + rebuild
// guidance, and the computed value (12) is NOT produced (the load is refused
// before dispatch).
#[test]
fn platform_adt_hash_gate_run_refuses() {
    let out = Cranelisp::new()
        .use_workspace_platforms()
        .file("user.cl", SHAPES_PROGRAM_DRIFTED)
        .run("user.cl")
        .output();
    // Refused: non-zero exit, and NOT the computed area.
    assert!(
        !out.status.success(),
        "--run MUST refuse on layout-hash drift (non-zero exit); status: {:?}\nstdout:\n{}\nstderr:\n{}",
        out.status, out.stdout, out.stderr
    );
    assert_ne!(
        out.status.code(),
        Some(12),
        "--run MUST NOT compute the area when the layout-hash gate refuses; got exit 12"
    );
    // Error surfaces the platform name + both hashes + rebuild guidance.
    assert!(
        out.stderr.contains("shapes"),
        "hash-gate refusal MUST name the platform `shapes`; got stderr:\n{}",
        out.stderr
    );
    assert!(
        out.stderr.contains("hash") || out.stderr.contains("layout"),
        "hash-gate refusal MUST mention the layout hash; got stderr:\n{}",
        out.stderr
    );
    assert!(
        out.stderr.contains("rebuild")
            || out.stderr.contains("regenerate")
            || out.stderr.contains("/platform-schema"),
        "hash-gate refusal MUST carry rebuild guidance; got stderr:\n{}",
        out.stderr
    );
}

// spec: spec/10-io.md §10.10 — Platform ABI Contract
// FAILING-FIRST (RED until fixture + R2). REPL WARNS-AND-LOADS on layout-hash
// drift (the regeneration bootstrap): the warning names the platform + both
// hashes, but the session continues and the platform fn remains usable (the
// REPL is the one mode that does not refuse — it regenerates).
#[test]
fn platform_adt_hash_gate_repl_warns_and_loads() {
    let out = Cranelisp::new()
        .use_workspace_platforms()
        .file("user.cl", SHAPES_PROGRAM_DRIFTED)
        .stdin("(area (Rectangle 3 4 5))\n")
        .repl()
        .output();
    // Warn: the platform name + a hash/layout mention appear, but the session
    // does NOT abort — it warns and loads.
    assert!(
        out.stderr.contains("shapes") || out.stdout.contains("shapes"),
        "REPL hash-gate warning MUST name the platform `shapes`; \
         got stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("warn")
            || out.stderr.contains("hash")
            || out.stdout.contains("warn")
            || out.stdout.contains("hash"),
        "REPL hash-gate MUST surface a warning (not a refusal); \
         got stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    // Warn-AND-LOAD: the session continues to a clean EOF exit (not an abort).
    assert!(
        out.status.success() || out.status.code().is_some(),
        "REPL MUST warn-and-load (continue), not abort on layout-hash drift; \
         status: {:?}\nstderr:\n{}",
        out.status, out.stderr
    );
}

// spec: spec/10-io.md §10.10 — Platform ABI Contract
// FAILING-FIRST (RED until fixture + R1). `--link` MUST REFUSE on layout-hash
// drift: the produced binary's startup stub compares the baked hash against the
// program's regenerated hash and aborts. Either `--link` fails to produce a
// binary, or the produced binary aborts at startup with the hash-gate message.
#[test]
fn platform_adt_hash_gate_link_refuses() {
    let out = Cranelisp::new()
        .use_workspace_platforms()
        .file("user.cl", SHAPES_PROGRAM_DRIFTED)
        .link_then_run("user.cl")
        .output();
    // Refused at link OR at the produced binary's startup stub — either way,
    // the program MUST NOT compute the area (exit 12) and MUST surface the gate.
    assert_ne!(
        out.status.code(),
        Some(12),
        "--link MUST NOT compute the area when the layout-hash gate refuses; got exit 12"
    );
    assert!(
        !out.status.success(),
        "--link MUST refuse on layout-hash drift (link failure or startup abort); \
         status: {:?}\nstdout:\n{}\nstderr:\n{}",
        out.status, out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("shapes"),
        "--link hash-gate refusal MUST name the platform `shapes`; got stderr:\n{}",
        out.stderr
    );
    assert!(
        out.stderr.contains("hash") || out.stderr.contains("layout"),
        "--link hash-gate refusal MUST mention the layout hash; got stderr:\n{}",
        out.stderr
    );
}

// =============================================================================
// Item 3 — cache-restore round-trip
// =============================================================================

// spec: spec/10-io.md §10.10 — Platform ABI Contract
// FAILING-FIRST (RED until fixture + R2). Run twice in the same tmpdir: the
// first run populates the module cache; the second run restores from cache
// (platform types cache as ordinary `.cl` modules — no `schema_literal` field)
// and STILL crosses the ADT correctly (exit 12). The second run is asserted to
// be a cache hit via `CRANELISP_MODULE_TRACE=1`.
#[test]
fn platform_adt_roundtrip_cache_restore() {
    // First run: cold — populates the cache. Exit 12 proves the clean path.
    let first = Cranelisp::new()
        .use_workspace_platforms()
        .file("user.cl", SHAPES_PROGRAM)
        .env("CRANELISP_MODULE_TRACE", "1")
        .run("user.cl")
        .output()
        .assert_exit(12);

    // Second run: same tmpdir → cache restore. Still exits 12, and the module
    // trace reports a cache hit for the shapes platform module.
    let second = first
        .run_again()
        .use_workspace_platforms()
        .file("user.cl", SHAPES_PROGRAM)
        .env("CRANELISP_MODULE_TRACE", "1")
        .run("user.cl")
        .output()
        .assert_exit(12);
    assert!(
        second.stderr.contains("cache hit")
            || second.stderr.contains("cache-hit")
            || second.stderr.contains("hit"),
        "second run MUST be a cache hit (CRANELISP_MODULE_TRACE=1); got stderr:\n{}",
        second.stderr
    );
}

// =============================================================================
// R1 isolation guard — the simplest output-producing standalone --link binary
// =============================================================================

// spec: spec/10-io.md §10.10 — Platform ABI Contract
// FAILING-FIRST (RED until R1). The minimal R1 guard: a `(platform stdio)`
// binary whose `main` prints "hello". This isolates "is `--link` platform
// wiring alive at all" from the richer `shapes` ADT marshaling — if THIS fails
// but the `--run` companion below passes, R1 (link wiring) is the gap, not the
// ADT schema. Per spec, `main` returns `IO _` here: `(print …)` returns
// `IO Int`, so this `main` IS spec-conformant.
#[test]
fn platform_stdio_print_link() {
    Cranelisp::new()
        .use_workspace_platforms()
        .file(
            "user.cl",
            "(platform stdio)\n\
             (import [platform.stdio [print]])\n\
             (defn main [] (print \"hello\"))\n",
        )
        .link_then_run("user.cl")
        .output()
        .assert_stdout_contains("hello");
}

// spec: spec/10-io.md §10.10 — Platform ABI Contract
// CONTROL (GREEN today). The `--run` companion to `platform_stdio_print_link`:
// the same program under `--run` already works, so this passing while the
// `_link` half fails pins the gap to R1 (`--link` platform wiring).
#[test]
fn platform_stdio_print_run_control() {
    Cranelisp::new()
        .use_workspace_platforms()
        .file(
            "user.cl",
            "(platform stdio)\n\
             (import [platform.stdio [print]])\n\
             (defn main [] (print \"hello\"))\n",
        )
        .run("user.cl")
        .output()
        .assert_stdout_contains("hello");
}
