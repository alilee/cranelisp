#!/usr/bin/env python3
"""ig_gates.py — the increment-I acceptance-gate DIFFERENTIAL runner
(S102 stage 1; qa plan gap G-5 + G-6 + G-7 in tests/plan/s102-test-plan.md §6).

Where s99_measure.py MEASURES, this script GATES: every lane is a same-HEAD
toggle-on vs toggle-off differential (`CRANELISP_NO_OWNERSHIP=1` = off — the
permanent correctness oracle, s100-ownership-verification.md §0), so the
fresh toggle-off baseline discipline (gap G-6: never attribute compiler drift
to the mechanisms) is built in — no stored baselines.

Gates implemented (tests/plan/s100-ownership-verification.md §2.2):
  I-G1  F1 rc_inc serial, program-attributable: ≥ 99% drop on vs off
  I-G2  F2/F3/F4 rc_inc: within 1% of toggle-off (attribution honesty)
  I-G4  F2/F3 N-worker wall+user median: ≤ +5% vs toggle-off (F4: report-only
        distribution — never a single-number gate, §5 limit 7)
  I-G5  F1–F4 serial + 1-worker wall+user median: ≤ +3%; PLUS the
        compile-time probe (gap G-7): cold-cache --run-to-exit over the
        L-B1 corpus (tests/fixtures/clif_baseline/corpus/): ≤ +10%
  I-G3 / I-G7 are NOT here: they gate on the H2/H5 per-mechanism counters
        (owed /backend B3, /typecheck B2 — RED hook smokes in
        tests/ownership_fences.rs are the tripwire); extend this runner when
        the counters land.
  I-G6  lives in tests/perf/l_d1_turn_latency.py (ready as-is).

Close-short seam obligation (/arch Q3 pin 2): if S102 closes after B2, run
`--gates g5` at the seam — pass5's cost is live the moment it runs. I-G1/2/4
grade mechanisms and defer wholesale at a short close.

Usage (attended, at wave gates — not canonical nextest; perf lanes live
outside the 30s cap, §0.4):
  python3 tests/perf/ig_gates.py                 # all gates
  python3 tests/perf/ig_gates.py --gates g5      # the seam-mandatory subset
  python3 tests/perf/ig_gates.py --reps 7        # acceptance-grade medians
  SYS_BIN=path/to/release-binary python3 tests/perf/ig_gates.py
NOTE: acceptance runs use a RELEASE-tier binary (S99 metrics discipline,
§0.3); the debug default is for protocol/plumbing checks only.
"""
import argparse
import os
import shutil
import statistics
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import s99_measure as m  # noqa: E402  (the measurement machinery)

ROOT = m.ROOT
CORPUS = os.path.join(ROOT, "tests", "fixtures", "clif_baseline", "corpus")


def with_toggle(off):
    """Set/unset CRANELISP_NO_OWNERSHIP in this process' env (env_for copies it)."""
    if off:
        os.environ["CRANELISP_NO_OWNERSHIP"] = "1"
    else:
        os.environ.pop("CRANELISP_NO_OWNERSHIP", None)


def counts(binp, clfile, off):
    with_toggle(off)
    try:
        return m.count_run(binp, clfile, "serial")
    finally:
        with_toggle(False)


def med(binp, clfile, config, reps, off):
    with_toggle(off)
    try:
        return m.median_time(binp, clfile, config, reps)
    finally:
        with_toggle(False)


def cold_compile_seconds(binp, clfile, off, reps):
    """G-7 compile probe: cold-cache --run to process exit, fresh dir per rep."""
    walls = []
    for _ in range(reps):
        d = tempfile.mkdtemp(prefix="igg-cold-")
        dst = os.path.join(d, "user.cl")
        shutil.copy(clfile, dst)
        e = dict(os.environ)
        for k in ("CRANELISP_NO_LENIENT", "RAYON_NUM_THREADS", "CRANELISP_RC_STATS"):
            e.pop(k, None)
        if off:
            e["CRANELISP_NO_OWNERSHIP"] = "1"
        else:
            e.pop("CRANELISP_NO_OWNERSHIP", None)
        cmd = ["/usr/bin/time", "-f", "wall=%e user=%U sys=%S", binp, "--run", "user.cl"]
        r = subprocess.run(cmd, cwd=d, env=e, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        t = m.TIME_RE.search(r.stderr.decode())
        if not t:
            raise RuntimeError("no time parse: " + r.stderr.decode()[-200:])
        walls.append(float(t.group(1)))
        shutil.rmtree(d, ignore_errors=True)
    return statistics.median(walls)


def pct(on, off):
    return float("inf") if off == 0 else 100.0 * (on - off) / off


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--reps", type=int, default=3, help="7 for acceptance-grade medians")
    ap.add_argument("--gates", default="g1,g2,g4,g5",
                    help="comma list from {g1,g2,g4,g5}; seam-mandatory subset = g5")
    args = ap.parse_args()
    gates = set(args.gates.split(","))

    binp = os.environ.get("SYS_BIN") or os.path.join(ROOT, "target", "debug", "cranelisp")
    if not os.path.exists(binp):
        print(f"error: binary not found at {binp}"); sys.exit(2)
    if "release" not in binp:
        print("WARNING: debug-tier binary — protocol check only, not acceptance "
              "(S99 discipline: release tier for graded numbers)\n")

    files = m.gen_fixtures()
    failures = []

    def verdict(gate, ok, detail):
        print(f"[{gate}] {'PASS' if ok else 'FAIL'} — {detail}")
        if not ok:
            failures.append(gate)

    base_on = counts(binp, files["noop"], off=False)
    base_off = counts(binp, files["noop"], off=True)

    def prog_inc(fx, off):
        c = counts(binp, files[fx], off)
        b = base_off if off else base_on
        return c[0] - b[0]

    if "g1" in gates:
        on, off = prog_inc("f1_machinery", False), prog_inc("f1_machinery", True)
        drop = 100.0 * (off - on) / off if off else 0.0
        verdict("I-G1", drop >= 99.0,
                f"F1 rc_inc serial: off={off} on={on} drop={drop:.2f}% (bar ≥99%)")

    if "g2" in gates:
        ok, parts = True, []
        for fx in ("f2_contention", "f3_inverted_search", "f4_hard"):
            on, off = prog_inc(fx, False), prog_inc(fx, True)
            delta = abs(pct(on, off))
            parts.append(f"{fx}: off={off} on={on} Δ={delta:.2f}%")
            ok &= delta <= 1.0
        verdict("I-G2", ok, "; ".join(parts) + " (bar: within 1% — attribution honesty)")

    if "g4" in gates:
        ok, parts = True, []
        for fx in ("f2_contention", "f3_inverted_search"):
            won, uon, _, _ = med(binp, files[fx], "Nworker", args.reps, off=False)
            woff, uoff, _, _ = med(binp, files[fx], "Nworker", args.reps, off=True)
            dw, du = pct(won, woff), pct(uon, uoff)
            parts.append(f"{fx}: wall {dw:+.1f}% user {du:+.1f}%")
            ok &= dw <= 5.0 and du <= 5.0
        verdict("I-G4", ok, "; ".join(parts) + " (bar ≤ +5%)")
        # F4: distribution report only (never a single-number gate).
        dist_on = [m.time_run(binp, files["f4_hard"], "Nworker")[0] for _ in range(5)]
        with_toggle(True)
        dist_off = [m.time_run(binp, files["f4_hard"], "Nworker")[0] for _ in range(5)]
        with_toggle(False)
        print(f"[I-G4/F4 report] N-worker wall on={sorted(dist_on)} off={sorted(dist_off)}")

    if "g5" in gates:
        ok, parts = True, []
        for fx in ("f1_machinery", "f2_contention", "f3_inverted_search", "f4_easy"):
            for cfg in ("serial", "1worker"):
                won, uon, _, _ = med(binp, files[fx], cfg, args.reps, off=False)
                woff, uoff, _, _ = med(binp, files[fx], cfg, args.reps, off=True)
                dw, du = pct(won, woff), pct(uon, uoff)
                parts.append(f"{fx}/{cfg}: wall {dw:+.1f}% user {du:+.1f}%")
                ok &= dw <= 3.0 and du <= 3.0
        verdict("I-G5/runtime", ok, "; ".join(parts) + " (bar ≤ +3%)")

        # G-7: the compile-time probe over the L-B1 corpus, cold cache.
        # Gate on the CORPUS AGGREGATE: individual entries compile in well
        # under /usr/bin/time's 0.01s wall resolution, so per-entry deltas
        # are quantization noise; the sum is the meaningful pass5 budget
        # observation (typecheck §3.4). Per-entry medians printed as detail.
        corpus = sorted(f for f in os.listdir(CORPUS) if f.endswith(".cl"))
        tot_on = tot_off = 0.0
        parts2 = []
        for entry in corpus:
            p = os.path.join(CORPUS, entry)
            con = cold_compile_seconds(binp, p, off=False, reps=args.reps)
            coff = cold_compile_seconds(binp, p, off=True, reps=args.reps)
            tot_on += con
            tot_off += coff
            parts2.append(f"{entry}: on={con:.2f}s off={coff:.2f}s")
        d = pct(tot_on, tot_off)
        verdict("I-G5/compile", d <= 10.0,
                f"corpus aggregate cold-cache: on={tot_on:.2f}s off={tot_off:.2f}s "
                f"Δ={d:+.1f}% (bar ≤ +10%); " + "; ".join(parts2))

    print()
    if failures:
        print("GATES FAILED:", ", ".join(failures)); sys.exit(1)
    print("all selected gates PASS")


if __name__ == "__main__":
    main()
