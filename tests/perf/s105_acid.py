#!/usr/bin/env python3
"""Allocation-volume and allocator-wall probes for serial temporary aggregates
and the parallel F6 witness. Uses the S105 counter-off timing scaffold.

SYS_BIN and MI_BIN select the system and mimalloc release binaries.
"""
import os, sys, re, subprocess, statistics

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import s99_measure as s99
import s104_utilization as s104
import s105_attribution as s105

NPROC = s105.NPROC
DEVNULL = subprocess.DEVNULL
PIPE = subprocess.PIPE

# ── SPARK_SITE_STATS grammar (gate-5 / M-static spark tally, F6 (iii)) ──
SPARK_SITE_RE = re.compile(
    r"\[SPARK_SITE_STATS\] site=(\S+) scc=(\w+) tail=(\w+) admit=(\w+) emits=(\d+)")


# ── Fixtures: reuse s105/s104 scaffold; add F9/F10 + slice F10 arms ──
def make_fixtures():
    files = s105.make_fixtures()   # f1..f8 + f8_serial/f8_parallel + f6_parwin
    # F9 control-flow-shape probes + F10 temp-vec — copied VERBATIM (shape must
    # not be rescaled by scale_synth; the gate-3 decision is shape-exact).
    for name in ("f6_parwin", "f9_straightline", "f9_loop", "f9_nontailrec", "f10_tempvec"):
        src = os.path.join(s99.FIX, name + ".cl")
        p = os.path.join(s99.WORK, name + ".cl")
        open(p, "w").write(open(src).read())
        files[name] = p
    # F10 per-arm variants (SL vs LOOP) sliced on the region markers.
    sl, lp = _gen_f10_variants(open(os.path.join(s99.FIX, "f10_tempvec.cl")).read())
    files["f10_sl"], files["f10_loop"] = sl, lp
    return files


def _gen_f10_variants(src):
    def strip(s, name):
        return re.sub(r";;S105-F10-%s-BEGIN.*?;;S105-F10-%s-END\n" % (name, name),
                      "", s, flags=re.S)
    def pick_main(s, which):
        s = re.sub(r";;S105-F10-MAIN-BOTH\n.*?;;S105-F10-MAIN-BOTH-END\n", "", s, flags=re.S)
        keep = {"SL": "MAIN-SL", "LOOP": "MAIN-LOOP"}[which]
        drop = {"SL": "MAIN-LOOP", "LOOP": "MAIN-SL"}[which]
        s = re.sub(r";;S105-F10-%s\s+" % keep, "", s)
        s = re.sub(r";;S105-F10-%s\s.*\n" % drop, "", s)
        return s
    out = {}
    for arm, other in (("SL", "LOOP"), ("LOOP", "SL")):
        s = strip(src, other)
        s = pick_main(s, arm)
        p = os.path.join(s99.WORK, "f10_%s.cl" % arm.lower())
        open(p, "w").write(s)
        out[arm] = p
    return out["SL"], out["LOOP"]


# ── SPARK_SITE_STATS reader (F6 gate-5 tally) ──
def spark_sites(binp, clfile):
    e = dict(os.environ)
    for k in s105.STATS_ENV + s105.SEM_ENV:
        e.pop(k, None)
    e["CRANELISP_SPARK_STATS"] = "1"
    r = subprocess.run([binp, clfile, "--run"], env=e, stdout=DEVNULL, stderr=PIPE)
    admit = decline = 0
    rows = []
    for m in SPARK_SITE_RE.finditer(r.stderr.decode(errors="replace")):
        site, scc, tail, ad, emits = m.groups()
        rows.append((site, scc, tail, ad, int(emits)))
        if ad == "true":
            admit += 1
        else:
            decline += 1
    return admit, decline, rows


def rc_site(binp, clfile, serial=True):
    """Separate CRANELISP_RC_STATS run → the [RC_SITE_STATS] confined/crossing tally."""
    e = s105.counts_env(serial=serial)
    r = subprocess.run([binp, clfile, "--run"], env=e, stdout=DEVNULL, stderr=PIPE)
    txt = r.stderr.decode(errors="replace")
    conf = re.search(r"\[RC_SITE_STATS\] confined_cells=(\d+) crossing_cells=(\d+)", txt)
    sites = re.findall(r"\[RC_SITE_STATS\] site=(\S+) class=(\w+) ops=(\d+)", txt)
    return (int(conf.group(1)), int(conf.group(2))) if conf else (None, None), sites


def fmt(w):
    return "%.3fs" % w if isinstance(w, float) else str(w)


# ══ (ii) opportunity ceiling — serial non-scalar temp aggregate ═══════════════
def opportunity(sysb, mib, files, reps):
    print("\n" + "=" * 78)
    print("## (ii) OPPORTUNITY CEILING — serial non-scalar temp-aggregate (Vec)")
    out = {}
    for arm, fx in (("SL (non-recursive helper)", "f10_sl"),
                    ("LOOP (tail recursion)", "f10_loop")):
        clf = files[fx]
        c = s105.counts(sysb, clf, s105.counts_env(serial=True)) or {}
        (conf, cross), sites = rc_site(sysb, clf, serial=True)
        w_sys, _ = s105.timed_wall(sysb, clf, s105.wall_env(serial=True), reps)
        w_mi, _ = s105.timed_wall(mib, clf, s105.wall_env(serial=True), reps)
        sysc = s105.syscall_profile(sysb, clf, serial=True)
        mim_delta = (w_sys - w_mi) if None not in (w_sys, w_mi) else None
        mim_pct = (100.0 * mim_delta / w_sys) if (mim_delta is not None and w_sys) else None
        print("\n  %-38s [%s]" % (arm, fx))
        print("    N1: allocs=%s  alloc_bytes=%s  (bytes/alloc≈%s)" % (
            c.get("allocs"), c.get("alloc_bytes"),
            (c.get("alloc_bytes") // c.get("allocs")) if c.get("allocs") else "?"))
        print("        reuse_hit=%s reuse_miss=%s  rc_atomic=%s" % (
            c.get("reuse_hit"), c.get("reuse_miss"), c.get("rc_atomic")))
        print("    N3: confined_cells=%s crossing_cells=%s" % (
            conf, cross))
        for (s_id, cls, ops) in sites:
            print("        site=%s class=%s ops=%s" % (s_id, cls, ops))
        print("    wall[system]=%s  wall[mimalloc]=%s  → alloc-share of wall (mimalloc Δ)=%s (%s)" % (
            fmt(w_sys), fmt(w_mi),
            ("%+.3fs" % mim_delta) if mim_delta is not None else "n/a",
            ("%.1f%%" % mim_pct) if mim_pct is not None else "n/a"))
        if sysc.get("status") == "ok":
            print("    strace: alloc-share=%s%% [brk=%s mmap=%s]  sched-share=%s%% [futex=%s]" % (
                sysc["alloc_share"], sysc["brk"], sysc["mmap"], sysc["sched_share"], sysc["futex"]))
        else:
            print("    strace: %s" % sysc.get("status"))
        out[arm] = dict(allocs=c.get("allocs"), alloc_bytes=c.get("alloc_bytes"),
                        conf=conf, cross=cross, w_sys=w_sys, w_mi=w_mi,
                        mim_pct=mim_pct, sysc=sysc)
    return out


# ══ (iii) F6 re-probe ═════════════════════════════════════════════════════════
def f6_reprobe(sysb, files, reps):
    print("\n" + "=" * 78)
    print("## (iii) F6 RE-PROBE — the S104 positive-scaling parallel compute witness")
    clf = files["f6_parwin"]
    c = s105.counts(sysb, clf, s105.counts_env()) or {}            # lenient/parallel counts
    admit, decline, srows = spark_sites(sysb, clf)
    ser, _ = s105.timed_wall(sysb, clf, s105.wall_env(serial=True), max(1, reps // 2))
    par, _ = s105.timed_wall(sysb, clf, s105.wall_env(threads=NPROC), reps)
    speedup = (ser / par) if (ser and par) else None
    leaves = 16  # F6 knob
    print("  per-strand allocation volume (leaves=%d):" % leaves)
    print("    allocs=%s  alloc_bytes=%s  → per-strand alloc≈%s allocs / %s bytes" % (
        c.get("allocs"), c.get("alloc_bytes"),
        (c.get("allocs") // leaves) if c.get("allocs") is not None else "?",
        (c.get("alloc_bytes") // leaves) if c.get("alloc_bytes") is not None else "?"))
    print("    reuse_hit=%s  rc_atomic=%s" % (
        c.get("reuse_hit"), c.get("rc_atomic")))
    print("  gate-5 / M-static spark tally (SPARK_SITE_STATS):")
    print("    admit(would-spark)=%s  decline=%s" % (admit, decline))
    for (site, scc, tail, ad, emits) in srows:
        print("      site=%s scc=%s tail=%s admit=%s emits=%s" % (site, scc, tail, ad, emits))
    print("  wall[serial]=%s  wall[parallel@%d]=%s  → speedup=%s" % (
        fmt(ser), NPROC, fmt(par), ("%.2fx" % speedup) if speedup else "?"))
    verdict = ("COMPUTE-BOUND, negligible per-strand alloc ⇒ NO alloc-bound parallel "
               "opportunity behind gate 5") if (c.get("allocs") is not None and c.get("allocs") < 100) \
        else "ALLOC-BEARING — inspect gate-5 decline for allocation cost"
    print("  F6 VERDICT: %s" % verdict)
    return dict(allocs=c.get("allocs"), alloc_bytes=c.get("alloc_bytes"),
                admit=admit, decline=decline, ser=ser, par=par, speedup=speedup,
                verdict=verdict)


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--reps", type=int, default=3)
    args = ap.parse_args()

    sysb = os.environ.get("SYS_BIN")
    mib = os.environ.get("MI_BIN")
    if not sysb or not os.path.exists(sysb):
        print("SYS_BIN unset/missing (system release build)", file=sys.stderr); sys.exit(2)
    if not mib or not os.path.exists(mib):
        print("MI_BIN unset/missing (--features thread-caching-alloc build)", file=sys.stderr); sys.exit(2)

    files = make_fixtures()
    print("# S105 ACID harness  (nproc=%d, reps=%d)" % (NPROC, args.reps))
    print("# SYS_BIN=%s\n# MI_BIN=%s" % (sysb, mib))
    print("# start busy_cores=%.2f  load1=%.2f" % (s104.busy_cores(), os.getloadavg()[0]))
    print("# DOCTRINE: walls counter-OFF; counts separate run; idle out-of-band; HW external.")

    opportunity(sysb, mib, files, args.reps)
    f6_reprobe(sysb, files, args.reps)


if __name__ == "__main__":
    main()
