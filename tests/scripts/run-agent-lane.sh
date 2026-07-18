#!/usr/bin/env bash
# run-agent-lane.sh — the isolated launcher for the `--features agent` e2e lane.
#
# WHY THIS EXISTS (FIXME 0615 — agent-lane binary-provenance race)
# ---------------------------------------------------------------
# The agent lane builds `cranelisp` with `--features agent` compiled in. Every
# e2e spawn resolves the compiled binary by PATH (see
# `tests/helpers/e2e.rs::binary_path`). If the agent lane and the default suite
# share one target dir, the agent-featured build clobbers the default
# `target/debug/cranelisp` mid-suite, and a feature-OFF guard — e.g.
# `agent_flag_errors_on_non_agent_build`, which asserts the binary REJECTS
# `--agent` — then spawns an agent-CAPABLE binary that ACCEPTS the flag and
# mis-asserts. The outcome is a pure function of which binary sits at the path
# at spawn time: deterministic in binary provenance, NOT a flake.
#
# A nextest setup-script cannot fix this — setup scripts order steps WITHIN one
# cargo invocation; the race is BETWEEN two invocations with different feature
# sets. The cure is target-dir isolation by construction:
#
#   * The agent-featured binary lives at `target/agent/debug/cranelisp`, so it
#     can never overwrite the default `target/debug/cranelisp`.
#   * The exported `CARGO_TARGET_DIR` propagates into the test process env;
#     `binary_path()` resolves the binary root from it, so this lane's tests
#     exec `target/agent/debug/cranelisp` — their own lane's binary.
#
# Run the agent lane with this script — NOT a bare
# `cargo nextest run --features agent --test agent`.

set -euo pipefail

# Resolve the workspace root from this script's location (tests/scripts/..).
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKSPACE_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$WORKSPACE_ROOT"

# Isolated target dir: the agent-featured binary is quarantined here and can
# never clobber the default `target/debug/cranelisp`.
export CARGO_TARGET_DIR="target/agent"

exec cargo nextest run --features agent --test agent "$@"
