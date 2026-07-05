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
  I-G2  attribution HONESTY (reframed S102 — see §2.2 acceptance record):
        the property is NOT "no rc_inc may change" (that mis-frames a
        legitimate borrow-elision beneficiary as mis-attribution). It is:
        (a) fixtures the read path does NOT apply to (F2/F3 — the 170M
            shared-artifact term is increment-II-deferred, backend §5.2) show
            NO spurious rc_inc drop: within 1% of toggle-off; AND
        (b) a fixture that IS a borrow-elision beneficiary (F4/sudoku) may
            drop rc_inc — that is an HONEST win iff it is PAIRED WITH A
            NON-REGRESSING WALL (a mechanism that "drops rc_inc" while slowing
            the program moved cost, it did not remove it — that is the
            dishonest signature the gate must catch). F4 serial wall ≤ +5%.
  I-G4  F2/F3 N-worker wall+user median: ≤ +5% vs toggle-off (F4: report-only
        distribution — never a single-number gate, §5 limit 7)
  I-G5  small-case overhead. Runtime: F2/F3 serial + 1-worker wall+user
        median ≤ +3% (the resolution-bearing fixtures); F1/F4-easy REPORT-ONLY
        (<60ms total wall → process-startup-dominated, pass5 delta below the
        noise floor; gross-regression tripwire ≤ +25% only). PLUS the
        compile-time probe (gap G-7): cold-cache --run-to-exit over the
        L-B1 corpus (tests/fixtures/clif_baseline/corpus/): ≤ +10%.
        ALL I-G5 timing uses hires (perf_counter wall + wait4 rusage
        user/sys, microsecond resolution) — /usr/bin/time's 0.01s
        quantization turned single-tick jitter into false +regressions on
        the <60ms fixtures and 0.00s→pct(0,0)=+inf on the corpus (S102 fix).
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
import time

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
    """G-7 compile probe: cold-cache --run to process exit, fresh dir per rep.
    hires wall via perf_counter — /usr/bin/time's 0.01s resolution read every
    <20ms corpus compile as 0.00-0.01s, so the aggregate quantized to 0.00 and
    pct(0,0)=+inf (the S102 harness bug this fixes). perf_counter resolves the
    real per-entry compile (8-18ms) to sub-ms, so the corpus-aggregate pass5
    ON-vs-OFF delta is a real number."""
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
        t0 = time.perf_counter()
        r = subprocess.run([binp, "--run", "user.cl"], cwd=d, env=e,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        walls.append(time.perf_counter() - t0)
        # The corpus programs use main's returned Pure(int) as the process exit
        # code (e.g. corpus 01 computes 24), so a nonzero exit is EXPECTED and
        # is not a failure. Only a signal kill (negative returncode in Python =
        # -signum) is a real crash worth aborting the probe.
        if r.returncode < 0:
            raise RuntimeError(f"compile probe crashed (signal {-r.returncode}) on {clfile}")
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
    # Absolute: the compile probe runs with cwd=tempdir, so a relative SYS_BIN
    # (e.g. target/release/cranelisp) would not resolve there (S102 fix).
    binp = os.path.abspath(binp)
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
        # Attribution HONESTY, reframed (S102). Two legs, two different bars —
        # see the header and s100-ownership-verification.md §2.2 record.
        ok, parts = True, []
        # (a) NON-BENEFICIARY leg: the read path does not touch the 170M
        # shared-artifact term (backend §5.2 — increment-II), so F2/F3 rc_inc
        # must stay flat. A drop HERE would be spurious mis-attribution.
        for fx in ("f2_contention", "f3_inverted_search"):
            on, off = prog_inc(fx, False), prog_inc(fx, True)
            delta = abs(pct(on, off))
            parts.append(f"{fx}(flat): off={off} on={on} Δ={delta:.2f}%")
            ok &= delta <= 1.0
        # (b) BENEFICIARY leg: F4/sudoku is a legitimate borrow-elision
        # target; its rc_inc drop is HONEST iff the wall does not regress.
        # Gate = wall non-regression (≤ +5%); the rc_inc drop is reported and
        # required > 0 (it must genuinely be a beneficiary, distinguishing it
        # from the flat non-beneficiaries — a zero drop here would mean the
        # read path never fired on the one fixture it should).
        for fx in ("f4_hard", "f4_easy"):
            on, off = prog_inc(fx, False), prog_inc(fx, True)
            drop = 100.0 * (off - on) / off if off else 0.0
            won, _, _, _ = m.hires_median(binp, files[fx], "serial", args.reps, off=False)
            woff, _, _, _ = m.hires_median(binp, files[fx], "serial", args.reps, off=True)
            dw = pct(won, woff)
            beneficiary = drop > 1.0
            wall_ok = dw <= 5.0
            parts.append(f"{fx}(elision): rc_inc off={off} on={on} drop={drop:.2f}% "
                         f"wall {dw:+.1f}% ({'honest' if beneficiary and wall_ok else 'SUSPECT'})")
            ok &= beneficiary and wall_ok
        verdict("I-G2", ok, "; ".join(parts)
                + " (bar: F2/F3 flat ≤1%; F4 drop paired with wall ≤+5%)")

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
        # Runtime overhead. hires timing (perf_counter wall + wait4 rusage)
        # throughout — /usr/bin/time's 0.01s tick turned single-tick jitter on
        # these fixtures into false +regressions (I-G5 harness under-resolution).
        ok, parts, reports = True, [], []
        # Graded lanes: the resolution-bearing fixtures (~450-490ms wall) where
        # a ≤+3% bar is honestly measurable.
        for fx in ("f2_contention", "f3_inverted_search"):
            for cfg in ("serial", "1worker"):
                won, uon, _, _ = m.hires_median(binp, files[fx], cfg, args.reps, off=False)
                woff, uoff, _, _ = m.hires_median(binp, files[fx], cfg, args.reps, off=True)
                dw, du = pct(won, woff), pct(uon, uoff)
                parts.append(f"{fx}/{cfg}: wall {dw:+.1f}% user {du:+.1f}%")
                ok &= dw <= 3.0 and du <= 3.0
        # Report-only lanes: F1 (~18ms) and F4-easy (~50ms) are process-startup-
        # dominated; the pass5 delta is below the wall noise floor, so a ≤+3%
        # gate cannot honestly resolve it (even hires medians swing several %
        # from process jitter). Kept with a GROSS-regression tripwire (≤+25%)
        # so a 2× blowup is still caught. F1's user CPU — the borrow-elision
        # headline, where the ~2.13M rc ops vanish — is the real ON-faster
        # evidence (consistently ~ -40%), corroborating I-G1.
        for fx in ("f1_machinery", "f4_easy"):
            for cfg in ("serial", "1worker"):
                won, uon, _, _ = m.hires_median(binp, files[fx], cfg, args.reps, off=False)
                woff, uoff, _, _ = m.hires_median(binp, files[fx], cfg, args.reps, off=True)
                dw, du = pct(won, woff), pct(uon, uoff)
                reports.append(f"{fx}/{cfg}: wall {dw:+.1f}% user {du:+.1f}%")
                ok &= dw <= 25.0  # gross-regression tripwire only
        verdict("I-G5/runtime", ok, "; ".join(parts) + " (graded bar ≤ +3%); "
                "report-only <60ms startup-dominated (tripwire ≤+25%): "
                + "; ".join(reports))

        # G-7: the compile-time probe over the L-B1 corpus, cold cache.
        # hires (perf_counter) resolves the real per-entry compile (8-18ms) to
        # sub-ms — /usr/bin/time's 0.01s quantized every entry to 0.00-0.01s and
        # the aggregate to 0.00 → pct(0,0)=+inf (the S102 harness bug). Gate on
        # the CORPUS AGGREGATE: the sum is the meaningful pass5 budget
        # observation (typecheck §3.4); per-entry medians printed as detail.
        # (Each entry's wall is still process-startup-dominated, so the
        # aggregate delta carries a few % of startup common-mode noise — well
        # inside the ≤+10% bar the true near-zero pass5 overhead sits under.)
        corpus = sorted(f for f in os.listdir(CORPUS) if f.endswith(".cl"))
        tot_on = tot_off = 0.0
        parts2 = []
        for entry in corpus:
            p = os.path.join(CORPUS, entry)
            con = cold_compile_seconds(binp, p, off=False, reps=args.reps)
            coff = cold_compile_seconds(binp, p, off=True, reps=args.reps)
            tot_on += con
            tot_off += coff
            parts2.append(f"{entry}: on={con:.3f}s off={coff:.3f}s")
        d = pct(tot_on, tot_off)
        verdict("I-G5/compile", d <= 10.0,
                f"corpus aggregate cold-cache: on={tot_on:.3f}s off={tot_off:.3f}s "
                f"Δ={d:+.1f}% (bar ≤ +10%); " + "; ".join(parts2))

    print()
    if failures:
        print("GATES FAILED:", ", ".join(failures)); sys.exit(1)
    print("all selected gates PASS")


if __name__ == "__main__":
    main()
