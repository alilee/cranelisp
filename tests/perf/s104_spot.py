#!/usr/bin/env python3
"""S104 single-shot SPOT instrument — the per-wave order-of-magnitude attribution.

## Doctrine (user direction, S104 Wave 1, 2026-07-07)

We chase **order-of-magnitude** wins this sprint, so precision measurement
(reps / distributions / idle-guard / thread-sweep — the `s104_utilization.py`
rigorous matrix) is PREMATURE for per-wave attribution and *self-defeating*: a
full sweep spends ~an hour measuring a ~2-minute runtime, and its idle-guard
trips on the sweep's OWN load (`load1 < 0.5` never holds mid-sweep), causing
endless rep re-runs. This tool is the per-wave instrument instead:

  one shot per (fixture, config) at `T=nproc`, reporting **wall + spawns** from
  `[SPARK_STATS]` and (with `--sites`) the per-site emits from
  `[SPARK_SITE_STATS]` — the accessor-zero proof. NO idle-guard, NO reps.

The rigorous `s104_utilization.py` matrix is retained for **FINAL ACCEPTANCE
only** (Stage 4 north-star grading, on a confirmed-idle machine).

Single-sourced against `s104_utilization.py` (Principle 7): config env, fixture
generation, the `[SPARK_STATS]`/`[SPARK_SITE_STATS]` parsers, and the per-site
comparison are all imported, never mirrored.

Usage:
  SYS_BIN=target/release/cranelisp python3 tests/perf/s104_spot.py \
      [--fixtures f4_hard,f5_compute,f1_machinery,f2_contention,f3_inverted_search] \
      [--configs serial,syntactic,mstatic] [--threads 10] [--sites]
"""
import os, sys, subprocess, time, argparse

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import s104_utilization as h   # config_env / make_fixtures / parsers / print_site_comparison

DEVNULL = subprocess.DEVNULL
PIPE = subprocess.PIPE

# Config names understood here. serial/syntactic/mstatic/admit-all resolve today
# via h.config_env. `mdynamic` and `both` are Wave-2/3 rows — their env is not
# yet defined (M-dynamic re-parameterizes the existing IN_FLIGHT_SPARKS create-
# gate; the toggle lands with the Wave-2 /dev build). Listed so this tool extends
# without edit once that toggle exists; until then they raise a clear message.
# Display name -> s104_utilization.config_env name (single-sourced env, Principle 7).
NAME = {"serial": "serial", "syntactic": "current-syntactic",
        "mstatic": "mstatic", "admit-all": "admit-all"}
KNOWN = set(NAME)
FUTURE = {"mdynamic", "both"}


def spot(binp, clfile, config, T):
    """One shot: wall (perf_counter) + spawns/peak/exit from [SPARK_STATS]."""
    e = h.config_env(NAME[config], T, spark_stats=True)
    t0 = time.perf_counter()
    r = subprocess.run([binp, clfile, "--run"], env=e, stdout=DEVNULL, stderr=PIPE)
    wall = time.perf_counter() - t0
    m = h.SPARK_STATS_RE.search(r.stderr.decode(errors="replace"))
    spawns = int(m.group(1)) if m else None
    peak = int(m.group(3)) if m else None
    return wall, spawns, peak, r.returncode


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fixtures", default="f4_hard,f5_compute")
    ap.add_argument("--configs", default="serial,syntactic,mstatic")
    ap.add_argument("--threads", type=int, default=h.NPROC)
    ap.add_argument("--sites", action="store_true",
                    help="also dump the per-site emits (syntactic vs mstatic) — accessor-zero proof")
    args = ap.parse_args()

    binp = os.environ.get("SYS_BIN")
    if not binp or not os.path.exists(binp):
        print("SYS_BIN not set / missing; `cargo build --release` and set "
              "SYS_BIN=target/release/cranelisp", file=sys.stderr)
        sys.exit(2)

    T = args.threads
    configs = args.configs.split(",")
    for c in configs:
        if c in FUTURE:
            print(f"# config '{c}' is a Wave-2/3 row; its env toggle is not built yet — skipping",
                  file=sys.stderr)
    configs = [c for c in configs if c in KNOWN]

    files = h.make_fixtures()
    print(f"# S104 SPOT (single-shot, T={T}, no idle-guard, no reps) — order-of-magnitude attribution")
    print(f"# binary: {binp}\n")

    for fx in args.fixtures.split(","):
        if fx not in files:
            print(f"### {fx}  — UNKNOWN FIXTURE (have: {', '.join(files)})\n")
            continue
        print(f"### {fx}")
        base = None
        for config in configs:
            wall, spawns, peak, code = spot(binp, files[fx], config, T)
            if config == "serial":
                base = wall
            sp = f"{spawns:,}" if spawns is not None else "?"
            spd = ""
            if base and config != "serial":
                spd = "  vs-serial=%.1fx" % (wall / base if base else 0.0)
            print(f"  {config:<12} wall=%6.2fs  spawns=%-13s peak=%-3s exit=%-4s%s" % (
                wall, sp, str(peak), str(code), spd))
        if args.sites:
            print()
            h.print_site_comparison(binp, files[fx], fx, T)
        print()


if __name__ == "__main__":
    main()
