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
        median ≤ +3% (the resolution-bearing fixtures), EXCEPT density-declined
        cells (B4 declines dense speculative sparks — currently only
        f3/1worker): those grade user/CPU ≤+3% and print the 1-worker wall as a
        VISIBLE user-accepted-trade line (Phase-7 ruling 2026-07-05, §2.2.1);
        F1/F4-easy REPORT-ONLY
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


# --- increment-II (write-path) additions (S103; qa plan §2 II-G1..G6) --------

# B2: F2's program-attributable rc_inc baseline (s100-ownership-verification.md
# §1.2 table). II-G1's "< 1% of B2" collapse bar keys on it.
B2_F2_RC_INC = 169_902_081

import re as _re  # noqa: E402
_REUSE_RE = _re.compile(r"reuse_hit=(\d+) reuse_miss=(\d+)")


def reuse_counts(binp, clfile, off=False):
    """Parse (reuse_hit, reuse_miss) off the [RC_STATS] line for a serial --run.
    The reuse_hit/reuse_miss family (H2, landed S102) tallies the COW in-place
    (hit) vs copy (miss) arm — II-G2's hit-rate substrate."""
    e = m.env_for("serial", rc_stats=True)
    if off:
        e["CRANELISP_NO_OWNERSHIP"] = "1"
    else:
        e.pop("CRANELISP_NO_OWNERSHIP", None)
    r = subprocess.run([binp, clfile, "--run"], env=e,
                       stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    mm = _REUSE_RE.search(r.stderr.decode())
    if not mm:
        raise RuntimeError("no reuse parse: " + r.stderr.decode()[-300:])
    return int(mm.group(1)), int(mm.group(2))


def run_ii_gates(binp, files, base_on, base_off, reps, gates, verdict):
    """II-G1..G6 — the increment-II (write-path) acceptance gates. Graded on the
    analysis-ON binary against a fresh same-HEAD toggle-OFF baseline."""
    def prog_inc(fx, off):
        c = counts(binp, files[fx], off)
        b = base_off if off else base_on
        return c[0] - b[0]

    if "iig1" in gates:
        # R5 witness: F2v rc_inc collapses to < 1% of B2 AND F2v N-worker wall
        # < F2v serial wall (the first parallel-must-pay gate). Attribution:
        # rc_inc → near-zero is R5's own effect (RC_STATS), corroborated by the
        # null-elem-fn CLIF (L-B1). Analysis ON for both walls.
        on_inc = prog_inc("f2v", off=False)
        off_inc = prog_inc("f2v", off=True)
        frac = 100.0 * on_inc / B2_F2_RC_INC
        rc_ok = on_inc < 0.01 * B2_F2_RC_INC
        ws, _, _, _ = m.hires_median(binp, files["f2v"], "serial", reps, off=False)
        wn, _, _, _ = m.hires_median(binp, files["f2v"], "Nworker", reps, off=False)
        wall_ok = wn < ws
        verdict("II-G1", rc_ok and wall_ok,
                f"F2v rc_inc on={on_inc} (off={off_inc}) = {frac:.3f}% of B2 "
                f"(bar <1%); N-worker wall={wn:.3f}s serial={ws:.3f}s "
                f"(bar N<serial: {'PAY' if wall_ok else 'NO-PAY'})")

    if "iig2" in gates:
        # Reuse hit-rate ≥ 50% on F4 (the copy-per-guess grid). Counter movement
        # (reuse_hit > 0) is the attribution prerequisite (§0.3). Graded on
        # f4_hard; f4_easy reported. This gate is INDEPENDENT of the
        # (map inc (map dec v)) chaining witness (that is a companion, not the
        # numeric gate) — see the II-G2/0528 verdict.
        ok, parts = True, []
        for fx in ("f4_hard", "f4_easy"):
            hit, miss = reuse_counts(binp, files[fx], off=False)
            tot = hit + miss
            rate = 100.0 * hit / tot if tot else 0.0
            graded = fx == "f4_hard"
            parts.append(f"{fx}: reuse_hit={hit} reuse_miss={miss} "
                         f"hit-rate={rate:.1f}%{' (graded)' if graded else ' (report)'}")
            if graded:
                ok &= tot > 0 and rate >= 50.0
        verdict("II-G2", ok, "; ".join(parts) + " (bar ≥50% on f4_hard, counter must move)")

    if "iig3" in gates:
        # F4 floor progress: F4-hard median N-worker wall ≤ 2× serial (from B7's
        # 6-15×). Distribution reported (never a single-number gate, §5 limit 7).
        ws_list = [m.time_run(binp, files["f4_hard"], "serial")[0] for _ in range(reps)]
        wn_list = [m.time_run(binp, files["f4_hard"], "Nworker")[0] for _ in range(reps)]
        med_s = statistics.median(ws_list)
        med_n = statistics.median(wn_list)
        ratio = med_n / med_s if med_s else float("inf")
        verdict("II-G3", ratio <= 2.0,
                f"F4-hard median N-worker={med_n:.3f}s serial={med_s:.3f}s "
                f"ratio={ratio:.2f}× (bar ≤2×); dist N={sorted(round(x,2) for x in wn_list)} "
                f"serial={sorted(round(x,2) for x in ws_list)}")

    if "iig4" in gates:
        # F2 two-ctor honesty: report rc_inc drop from reuse (expected ~0 — F2's
        # shared-grid copies are genuine materializations, NOT R5-covered, §5
        # limit 1); wall ≤ 1.5× serial (from B7's 2.3×). MUST NOT be graded as
        # R5-covered.
        on_inc = prog_inc("f2_contention", off=False)
        off_inc = prog_inc("f2_contention", off=True)
        drop = 100.0 * (off_inc - on_inc) / off_inc if off_inc else 0.0
        ws, _, _, _ = m.hires_median(binp, files["f2_contention"], "serial", reps, off=False)
        wn, _, _, _ = m.hires_median(binp, files["f2_contention"], "Nworker", reps, off=False)
        ratio = wn / ws if ws else float("inf")
        verdict("II-G4", ratio <= 1.5,
                f"F2 rc_inc drop={drop:.2f}% (on={on_inc} off={off_inc}; "
                f"NOT R5-covered — honest, §5 limit 1); N-worker wall={wn:.3f}s "
                f"serial={ws:.3f}s ratio={ratio:.2f}× (bar ≤1.5×)")

    if "iig5" in gates:
        # II-G5/G6 = I-G non-regression re-run, INCLUDING F2v serial: increment II
        # must not regress increment I's small-case bars. F2v serial ON vs OFF
        # ≤ +3% wall+user (the new fixture's two-sided bar).
        won, uon, _, _ = m.hires_median(binp, files["f2v"], "serial", reps, off=False)
        woff, uoff, _, _ = m.hires_median(binp, files["f2v"], "serial", reps, off=True)
        dw, du = pct(won, woff), pct(uon, uoff)
        verdict("II-G5/f2v-serial", dw <= 3.0 and du <= 3.0,
                f"F2v serial wall {dw:+.1f}% user {du:+.1f}% (bar ≤+3%); "
                f"the I-G4/I-G5 re-run below covers the rest of II-G5/G6")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--reps", type=int, default=3, help="7 for acceptance-grade medians")
    ap.add_argument("--gates", default="g1,g2,g4,g5",
                    help="comma list from {g1,g2,g4,g5,iig1,iig2,iig3,iig4,iig5}; "
                         "seam-mandatory subset = g5; increment-II set = 'ii' "
                         "(= iig1,iig2,iig3,iig4,iig5,g4,g5 — the II-G gates + the "
                         "I-G non-regression re-run for II-G5/G6)")
    args = ap.parse_args()
    gates = set(args.gates.split(","))
    if "ii" in gates:
        gates.discard("ii")
        gates |= {"iig1", "iig2", "iig3", "iig4", "iig5", "g4", "g5"}

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
        #
        # Density-declined cells (S102 Wave-18; USER Phase-7 ruling 2026-07-05:
        # "perfectly reasonable tradeoff. reframe i-g5 and keep the gains").
        # B4's static alloc/RC-density admission axis DECLINES dense speculative
        # sparks to the serial arm. On f3_inverted_search that kills parallel
        # over-sparking contention (N-worker wall -82%, graded by I-G4) and drops
        # user CPU everywhere (-46%), at the documented, user-ACCEPTED cost of
        # forgoing eager speculation on the 1-worker critical path (wall +~6%).
        # The 1-worker config is a measurement baseline, not a production mode.
        # For THIS cell the acceptance property is CPU/user (must drop-or-hold
        # ≤+3% — the anti-false-green guard: a mechanism that moved cost into CPU
        # rather than removing it would trip here) PLUS serial wall (graded
        # normally below). The 1-worker WALL is printed as an accepted-trade
        # line — VISIBLE, not graded. The ordinary ≤+3% wall bar stays intact for
        # every other (fixture,config), so this does NOT mask future regressions
        # on non-density-declined workloads. See §2.2.1 of
        # tests/plan/s100-ownership-verification.md.
        DENSITY_DECLINED = {("f3_inverted_search", "1worker")}
        for fx in ("f2_contention", "f3_inverted_search"):
            for cfg in ("serial", "1worker"):
                won, uon, _, _ = m.hires_median(binp, files[fx], cfg, args.reps, off=False)
                woff, uoff, _, _ = m.hires_median(binp, files[fx], cfg, args.reps, off=True)
                dw, du = pct(won, woff), pct(uon, uoff)
                if (fx, cfg) in DENSITY_DECLINED:
                    # Grade CPU/user (the density-decline dividend); keep the
                    # user-accepted wall regression VISIBLE but ungraded.
                    parts.append(f"{fx}/{cfg}: wall {dw:+.1f}% [accepted trade — "
                                 f"density-declined spark, §2.2.1] user {du:+.1f}%")
                    ok &= du <= 3.0
                else:
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
        verdict("I-G5/runtime", ok, "; ".join(parts) + " (graded bar ≤ +3% "
                "wall+user; density-declined cells grade user only — the "
                "1-worker wall is a user-accepted trade, §2.2.1); "
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

    if gates & {"iig1", "iig2", "iig3", "iig4", "iig5"}:
        run_ii_gates(binp, files, base_on, base_off, args.reps, gates, verdict)

    print()
    if failures:
        print("GATES FAILED:", ", ".join(failures)); sys.exit(1)
    print("all selected gates PASS")


if __name__ == "__main__":
    main()
