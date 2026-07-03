#!/usr/bin/env python3
"""l_d1_turn_latency.py — L-D1 REPL body-only redefinition turn-latency lane.

tests/plan/s100-ownership-verification.md §3.5 L-D1 / §6.1 (S101 stage M).

Mechanics (per §3.5, verbatim): the REPL prints per-turn timing in the prompt
(`NN+NNms; user>`). Session A loads an F1-scale module (~50 defns) then runs a
loop of BODY-ONLY redefinitions of one hot fn; we parse the per-turn ms stamps
and compare toggle-on vs toggle-off medians.

  M-stage gate: body-only median <= 1.10 x toggle-off median.

At stage M both polarities run no analysis, so the gate measures exactly what
stage M adds — the summary-diff gate + reverse-index maintenance overhead on
the fast path (design/int/session-transaction.md §"The L-D1 pin").

Session B performs one ABI-CHANGING redefinition (signature change) mid-module
and REPORTS turn time + recompiled-set size (report-only at stage M, no gate).

Perf lane: NOT part of `cargo nextest run` (30s suite cap discipline).
Evaluated attended at wave close / Phase-5 exit (qa plan §0.4 / §5 limit 8).

Usage:
  python3 tests/perf/l_d1_turn_latency.py [--turns 30] [--defns 50] [--bin PATH]
Exit: 0 pass, 1 gate exceeded, 2 harness error.
"""
import argparse
import os
import re
import statistics
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# Per-turn prompt stamp: `NN+NNms; user>` (compile+eval ms).
STAMP_RE = re.compile(r"(\d+)\+(\d+)ms; \S+>")


def make_module(n_defns: int) -> str:
    """~F1-scale module: n chained defns + one hot fn the loop redefines."""
    lines = ["(defn base0 [:Int x] (add-i64 x 1))"]
    for i in range(1, n_defns):
        lines.append(f"(defn base{i} [:Int x] (base{i - 1} (add-i64 x 1)))")
    lines.append(f"(defn hot [:Int x] (base{n_defns - 1} x))")
    return "\n".join(lines) + "\n"


def run_session(binary: str, stdin: str, extra_env: dict) -> str:
    """One REPL session in a fresh tmpdir with the primitives-only prelude."""
    with tempfile.TemporaryDirectory(prefix="l_d1-") as td:
        with open(os.path.join(td, "prelude.cl"), "w") as f:
            f.write("(export [primitives [*]])\n")
        env = dict(os.environ)
        env.update(extra_env)
        proc = subprocess.run(
            [binary],
            input=stdin,
            capture_output=True,
            text=True,
            cwd=td,
            env=env,
            timeout=120,
        )
        if proc.returncode != 0:
            print(f"harness error: REPL exited {proc.returncode}", file=sys.stderr)
            print(proc.stdout[-2000:], file=sys.stderr)
            print(proc.stderr[-2000:], file=sys.stderr)
            sys.exit(2)
        return proc.stdout


def turn_times_ms(stdout: str) -> list[int]:
    """Total (compile+eval) ms per turn, in order."""
    return [int(m.group(1)) + int(m.group(2)) for m in STAMP_RE.finditer(stdout)]


def body_only_median(binary: str, turns: int, defns: int, env: dict) -> float:
    module = make_module(defns)
    redefs = "".join(
        f"(defn hot [:Int x] (base{defns - 1} (add-i64 x {i})))\n"
        for i in range(1, turns + 1)
    )
    stdout = run_session(binary, module + redefs + "/quit\n", env)
    times = turn_times_ms(stdout)
    # The stamp on the prompt line FOLLOWING each input reports that turn;
    # the last `turns` complete stamps correspond to the redefinition turns.
    redef_times = times[-(turns):] if len(times) >= turns else times
    if not redef_times:
        print("harness error: no turn stamps parsed", file=sys.stderr)
        sys.exit(2)
    return statistics.median(redef_times)


def abi_change_report(binary: str, defns: int) -> None:
    """Session B — one ABI-changing redefinition; report time + cone size."""
    module = make_module(defns)
    script = module + "(defn base0 [:String s] (str-len s))\n/quit\n"
    stdout = run_session(binary, script, {})
    times = turn_times_ms(stdout)
    abi_turn_ms = times[-1] if times else -1
    # Recompiled-set size from the §18.3 cascade report (`; recompiled:` then
    # one names line). Absent pre-machinery: report 0.
    cone = 0
    lines = stdout.splitlines()
    for i, line in enumerate(lines):
        if line.strip().startswith("; recompiled:") and i + 1 < len(lines):
            cone = len(lines[i + 1].lstrip("; ").split())
            break
    broken = sum(1 for l in lines if l.strip().startswith(";") and "broken" in l)
    print(f"[L-D1 report] ABI-changing turn: {abi_turn_ms}ms; "
          f"recompiled-set size: {cone}; broken-set lines: {broken} "
          f"(report-only at stage M, no gate)")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--turns", type=int, default=30)
    ap.add_argument("--defns", type=int, default=50)
    ap.add_argument("--bin", default=os.path.join(ROOT, "target", "debug", "cranelisp"))
    args = ap.parse_args()

    if not os.path.exists(args.bin):
        print(f"harness error: binary not found at {args.bin}", file=sys.stderr)
        return 2

    on = body_only_median(args.bin, args.turns, args.defns, {})
    off = body_only_median(args.bin, args.turns, args.defns,
                           {"CRANELISP_NO_OWNERSHIP": "1"})

    print(f"[L-D1] body-only redefinition turn median over {args.turns} turns "
          f"({args.defns}-defn module):")
    print(f"[L-D1]   default polarity:            {on:.1f}ms")
    print(f"[L-D1]   CRANELISP_NO_OWNERSHIP=1:    {off:.1f}ms")

    abi_change_report(args.bin, args.defns)

    # M-stage gate: body-only <= 1.10 x toggle-off median. Guard the zero-ms
    # floor (debug builds can stamp 0/1ms turns): compare on a >=1ms basis.
    gate = 1.10 * max(off, 1.0)
    if on <= gate:
        print(f"[L-D1] PASS: {on:.1f}ms <= 1.10 x {max(off, 1.0):.1f}ms")
        return 0
    print(f"[L-D1] FAIL: body-only median {on:.1f}ms exceeds gate {gate:.1f}ms "
          f"— the summary-diff fast path is not at today's cost "
          f"(design/int/session-transaction.md §'The L-D1 pin')", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
