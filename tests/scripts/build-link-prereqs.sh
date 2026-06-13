#!/usr/bin/env bash
# Nextest setup-script: build the `--link` / platform e2e prerequisites.
#
# WHY THIS EXISTS
# ---------------
# The `--link` and platform e2e tests invoke the `cranelisp` binary as a
# subprocess; that binary, on its `--link` path, links three workspace
# members it does NOT have a Cargo dependency edge to:
#
#   * `cranelisp-exe-bundle`  -> target/debug/libcranelisp_exe_bundle.a
#   * `cranelisp-stdio`       -> target/debug/libcranelisp_stdio.{rlib,so}
#   * `cranelisp-test-capture`-> target/debug/libcranelisp_test_capture.{rlib,so}
#   * `cranelisp-shapes`      -> target/debug/libcranelisp_shapes.{rlib,so}  (ADT platform fixture)
#   * `cranelisp-shapes-badabi`-> target/debug/libcranelisp_shapes_badabi.{rlib,so}
#
# It resolves them AT RUNTIME by scanning `target/debug/` (see
# `src/exe.rs::find_bundle_lib` / `find_platform_rlibs` and
# `src/platform.rs::resolve_platform_path`). Because nothing in the
# dependency graph references these crates, a plain `cargo nextest run`
# never compiles them: nextest builds test targets + their transitive
# deps, and these crates are leaf workspace members with no test targets.
# The result is a clean-tree `--link` failure:
#
#   error: codegen error: could not find libcranelisp_exe_bundle.a
#
# This script makes the prerequisite build a deterministic, once-per-run
# step that nextest runs BEFORE any test in the default profile. One
# `cargo build -p ...` invocation builds all five into `target/debug`
# in the dev profile -- exactly the profile + directory the `--link`
# runtime path scans. No manual protocol, no stale artifacts.
#
# Cheap when already built: cargo no-ops in ~0.02s.
set -euo pipefail

cargo build \
  -p cranelisp-exe-bundle \
  -p cranelisp-stdio \
  -p cranelisp-test-capture \
  -p cranelisp-shapes \
  -p cranelisp-shapes-badabi
