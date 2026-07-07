#!/usr/bin/env python3
"""Sprint 104 Stage-0 (Wave 0) utilization-thesis measurement harness.

Builds the core-count-controlled instrument specified in
`tests/plan/s104-utilization-measurement.md` §1–§4 and runs:

  1. the config × thread-count baseline matrix (the Wave-0-feasible configs
     only — the M-static/M-dynamic rows are Waves 1–3),
  2. THE DISCRIMINATION EXPERIMENT (§4) — classify every current spark site in
     F1–F5 by {recursive-SCC?, tail?} from the committed `[SPARK_SITE_STATS]`
     instrumentation and emit the clean-separation PASS/FAIL verdict that gates
     Wave 1, and
  3. the Regime-A fixture-adequacy check (§5) on F1 (+ F5 witness).

NOT part of `cargo nextest run` — a perf lane (0534 precedent). Extends
`tests/perf/s99_measure.py` (imported for `gen_fixtures`/`scale_synth`/the HARD
puzzle) with a `RAYON_NUM_THREADS` sweep, a mechanical idle guard
(INVALID-not-benign), and parsers for the S104 `[SPARK_STATS]` /
`[SPARK_SITE_STATS]` lines.

## Idle guard (as-built refinement of plan §1.1 — recorded here + in the plan)

The plan mandates `os.getloadavg()[0] < IDLE_MAX` before each rep. The 1-minute
load average is polluted by the harness's OWN prior reps (self-heat decays over
~1 min), which would spuriously mark valid back-to-back reps INVALID and
UNMEASURE whole cells. The *intent* is "no NON-benchmark work is stealing
cores." That intent is served more faithfully by an INSTANTANEOUS non-idle-cores
probe from `/proc/stat`, sampled in the gap BEFORE each rep while nothing of ours
is running (so self-heat, whose process has exited, does not count). We gate on
that instantaneous `busy_cores` and ALSO record `load1` on every rep for the
plan's transparency line. This STRENGTHENS the S102→S103 false-green guard (it
still rejects the "residual 4–8 background cores" case — that load does not
decay) without false-UNMEASURING the harness's own valid heavy cells.

Usage:
  SYS_BIN=target/release/cranelisp python3 tests/perf/s104_utilization.py \
      [--mode all|discriminate|baseline|adequacy] [--reps N] [--f4-reps N] \
      [--threads 1,2,4,6,8,10] [--quick]
"""
import os, sys, subprocess, re, statistics, argparse, json, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import s99_measure as s99  # gen_fixtures / scale_synth / HARD / EASY / WORK

NPROC = os.cpu_count()
DEVNULL = subprocess.DEVNULL
PIPE = subprocess.PIPE

IDLE_FLOOR = float(os.environ.get("S104_IDLE_FLOOR", "0.5"))  # background cores tolerated at T=nproc

SPARK_STATS_RE = re.compile(
    r"\[SPARK_STATS\] spawns=(\d+) serial_continues=(\d+) peak_executing=(\d+) "
    r"force_calls=(\d+) force_fastpath_resolved=(\d+) force_claim_wins=(\d+) "
    r"force_spin_waits=(\d+) force_spin_iters=(\d+)")
SITE_RE = re.compile(
    r"\[SPARK_SITE_STATS\] site=(\S+) scc=(\w+) tail=(\w+) admit=(\w+) emits=(\d+)")

# Config axis. Wave 0 was pre-M-static, so the shipped default WAS the syntactic
# filter; post the Wave-1 build (`3804e42`) the shipped default flipped to
# `CRANELISP_SPARK_ADMIT=mstatic` (M-static). Therefore `current-syntactic` MUST
# now pin `CRANELISP_SPARK_ADMIT=syntactic` explicitly — relying on the default
# would silently measure M-static (the Wave-1 hazard). `mstatic` is the Wave-1
# M-static-only row (M-static ON, B4 off). `admit-all` is the syntactic firehose
# ceiling with B4 explicitly off; post-flip it is env-identical to
# `current-syntactic` (SPARK_DENSITY_MAX unset ≡ 0), kept as a row to reconfirm
# that identity under the new binary.
CONFIGS = ["serial", "off", "current-syntactic", "mstatic", "current-b4on", "admit-all"]


def config_env(config, T, spark_stats=False):
    e = dict(os.environ)
    for k in ("CRANELISP_NO_LENIENT", "CRANELISP_NO_OWNERSHIP", "CRANELISP_SPARK_DENSITY_MAX",
              "RAYON_NUM_THREADS", "CRANELISP_SPARK_STATS", "CRANELISP_SATURATION_GATE",
              "CRANELISP_SPARK_BUDGET", "CRANELISP_SPARK_ADMIT"):
        e.pop(k, None)
    if T is not None:
        e["RAYON_NUM_THREADS"] = str(T)
    if config == "serial":
        e["CRANELISP_NO_LENIENT"] = "1"
    elif config == "off":
        e["CRANELISP_NO_OWNERSHIP"] = "1"
    elif config == "current-syntactic":
        e["CRANELISP_SPARK_ADMIT"] = "syntactic"  # pin — default is now mstatic
    elif config == "mstatic":
        e["CRANELISP_SPARK_ADMIT"] = "mstatic"     # M-static-only (Wave 1)
        e["CRANELISP_SPARK_DENSITY_MAX"] = "0"     # B4 off (attribution pin, plan §2)
    elif config == "current-b4on":
        e["CRANELISP_SPARK_ADMIT"] = "syntactic"  # old default admission …
        e["CRANELISP_SPARK_DENSITY_MAX"] = "1"    # … + B4 on: the ~112s parked anchor
    elif config == "admit-all":
        e["CRANELISP_SPARK_ADMIT"] = "syntactic"  # syntactic firehose ceiling …
        e["CRANELISP_SPARK_DENSITY_MAX"] = "0"    # … B4 off; == current-syntactic post-flip
    else:
        raise ValueError("unknown config " + config)
    if spark_stats:
        e["CRANELISP_SPARK_STATS"] = "1"
    return e


# ── Idle guard: instantaneous non-idle cores from /proc/stat ──────────────────
def busy_cores(interval=0.3):
    def snap():
        with open("/proc/stat") as f:
            v = list(map(int, f.readline().split()[1:]))
        idle = v[3] + (v[4] if len(v) > 4 else 0)  # idle + iowait
        return idle, sum(v)
    i0, t0 = snap()
    time.sleep(interval)
    i1, t1 = snap()
    dt = t1 - t0
    if dt <= 0:
        return 0.0
    return max(0.0, (1.0 - (i1 - i0) / dt) * NPROC)


def idle_max_cores(T):
    return max(IDLE_FLOOR, 0.5 * (NPROC - (T if T is not None else NPROC)))


# ── One timed rep: perf_counter wall + wait4 rusage (µs CPU) ───────────────────
def timed_rep(binp, clfile, config, T):
    e = config_env(config, T)
    t0 = time.perf_counter()
    p = subprocess.Popen([binp, clfile, "--run"], env=e, stdout=DEVNULL, stderr=DEVNULL)
    _, status, ru = os.wait4(p.pid, 0)
    wall = time.perf_counter() - t0
    return wall, ru.ru_utime, ru.ru_stime, os.waitstatus_to_exitcode(status)


def instrumented_run(binp, clfile, config, T):
    """One SPARK_STATS=1 run → (stats dict, [sites], exit). Deterministic per
    (fixture,config,T), so one instrumented run per cell suffices for spawns."""
    e = config_env(config, T, spark_stats=True)
    r = subprocess.run([binp, clfile, "--run"], env=e, stdout=DEVNULL, stderr=PIPE)
    err = r.stderr.decode(errors="replace")
    stats = None
    m = SPARK_STATS_RE.search(err)
    if m:
        stats = dict(spawns=int(m.group(1)), serial_continues=int(m.group(2)),
                     peak_executing=int(m.group(3)), force_calls=int(m.group(4)),
                     force_fastpath_resolved=int(m.group(5)), force_claim_wins=int(m.group(6)),
                     force_spin_waits=int(m.group(7)), force_spin_iters=int(m.group(8)))
    sites = [(s, scc == "true", tail == "true", admit == "true", int(emits))
             for (s, scc, tail, admit, emits) in SITE_RE.findall(err)]
    return stats, sites, r.returncode


# ── Measure one cell (fixture, config, T): distribution + %CPU + spawns ────────
def measure_cell(binp, clfile, config, T, reps):
    walls, cpus, exits, loads = [], [], [], []
    invalids = 0
    imax = idle_max_cores(T)
    for r in range(reps + 1):  # +1 warm-exclude
        bc = busy_cores()               # nothing of ours running now
        load1 = os.getloadavg()[0]
        invalid = bc > imax
        wall, u, s, code = timed_rep(binp, clfile, config, T)
        if r == 0:
            continue                     # warm rep (JIT / page cache) discarded
        loads.append((round(bc, 2), round(load1, 2)))
        if invalid:
            invalids += 1
            continue
        walls.append(wall)
        cpus.append((u + s) / wall * 100.0 if wall > 0 else 0.0)
        exits.append(code)
    stats, _, icode = instrumented_run(binp, clfile, config, T)
    cell = dict(config=config, T=T, invalids=invalids, reps=reps,
                loads=loads, spawns=(stats or {}).get("spawns"),
                peak=(stats or {}).get("peak_executing"),
                serial_continues=(stats or {}).get("serial_continues"),
                exit=(exits[0] if exits else icode))
    if not walls or invalids > 0.20 * reps:
        cell["status"] = "UNMEASURED"
        return cell
    cell["status"] = "ok"
    cell["wall_min"] = min(walls)
    cell["wall_med"] = statistics.median(walls)
    cell["wall_max"] = max(walls)
    cell["cpu_med"] = statistics.median(cpus)
    return cell


def fmt_cell(c):
    if c["status"] == "UNMEASURED":
        return "  UNMEASURED (idle guard: %d/%d reps INVALID; loads=%s)" % (
            c["invalids"], c["reps"], c["loads"])
    sp = c["spawns"]
    sp = f"{sp:,}" if sp is not None else "?"
    return ("wall[min/med/max]=%.3f/%.3f/%.3f  %%CPU=%3.0f  spawns=%s  peak=%s  exit=%s%s" % (
        c["wall_min"], c["wall_med"], c["wall_max"], c["cpu_med"], sp,
        c["peak"], c["exit"], ("  [INVALID:%d]" % c["invalids"] if c["invalids"] else "")))


# ── Fixtures ──────────────────────────────────────────────────────────────────
def make_fixtures():
    files = s99.gen_fixtures()  # f1_machinery, f2_contention, f3_inverted_search, f2v,
                                 # f4_easy, f4_hard, noop  (scaled synth for F1-F3)
    # F5 — generated UNSCALED (its heavy fib depth must stay small).
    f5_src = os.path.join(s99.FIX, "f5_compute.cl")
    if os.path.exists(f5_src):
        p = os.path.join(s99.WORK, "f5_compute.cl")
        open(p, "w").write(open(f5_src).read())
        files["f5_compute"] = p
    return files


# ── THE DISCRIMINATION EXPERIMENT (plan §4) ───────────────────────────────────
# Expected recursive-non-tail D&C callees per fixture (MUST admit; §4.2). fib in
# F5 is recursive-non-tail COMPUTE — M-static correctly admits it (quality axis);
# its ~2/core collapse is M-dynamic's job, not a discrimination concern here.
EXPECTED_COARSE = {
    "f1_machinery": {"reduce-tree"},
    "f2_contention": {"reduce-tree"},
    "f3_inverted_search": {"search-tree"},
    # F4's ONLY coarse spark site is solve-range (its two args to first-success,
    # §4.2). `solve` is mutually recursive with solve-range but is NEVER a
    # sparkable apply-arg — it is the sole call in solve-range's leaf branch
    # `(solve (set-cell …))`, not one of two independent args — so it correctly
    # never appears as a spark site. Confirmed by the SPARK_SITE_STATS dump.
    "f4_easy": {"solve-range"},
    "f4_hard": {"solve-range"},
    "f5_compute": {"reduce-tree", "fib"},
}
# Flat non-recursive callees that MUST decline where they appear as spark sites.
KNOWN_FLAT = {"cell-at", "cell-value", "vec-get", "vec-set", "vec-len", "vec-push",
              "rem-i64", "mid-of", "first-success", "copies", "leaves", "full-mask",
              "mask-to-digits", "bit-count", "bit-lowest", "copy-work", "read-work"}


def bare_callee(site_id):
    # site = "module/callee@start..end"  → callee bare name
    head = site_id.split("@", 1)[0]
    return head.split("/")[-1]


def run_discrimination(binp, files):
    print("## DISCRIMINATION EXPERIMENT (plan §4) — classify every spark site by {scc?, tail?}\n")
    fixtures = ["f1_machinery", "f2_contention", "f3_inverted_search", "f4_easy", "f5_compute"]
    all_sites = {}          # fixture -> [(callee, scc, tail, admit, emits)]
    scc_by_callee = {}      # callee -> set of scc values seen (structural-consistency check)
    fails = []
    for fx in fixtures:
        # T=nproc, current-syntactic (default): the as-shipped spark set.
        _, sites, _ = instrumented_run(binp, files[fx], "current-syntactic", NPROC)
        recs = [(bare_callee(s), scc, tail, admit, emits) for (s, scc, tail, admit, emits) in sites]
        all_sites[fx] = recs
        print(f"### {fx}")
        for (callee, scc, tail, admit, emits) in sorted(recs):
            print(f"    {callee:<16} scc={str(scc):<5} tail={str(tail):<5} admit={str(admit):<5} emits={emits}")
            scc_by_callee.setdefault(callee, set()).add(scc)
            # (c) universal invariant: admit == (scc and not tail)
            if admit != (scc and not tail):
                fails.append(f"[c] {fx}:{callee} admit={admit} != (scc={scc} && !tail={tail})")
            # (b) flat accessors must decline
            if callee in KNOWN_FLAT and admit:
                fails.append(f"[b] {fx}:{callee} is a flat accessor but admit=true (MISCLASSIFIED)")
        # (a) expected coarse D&C sites must admit with emits>0
        present = {c: (scc, tail, admit, emits) for (c, scc, tail, admit, emits) in recs}
        for coarse in EXPECTED_COARSE.get(fx, set()):
            if coarse not in present:
                fails.append(f"[a] {fx}:{coarse} expected coarse-D&C site ABSENT from spark set")
            else:
                scc, tail, admit, emits = present[coarse]
                if not (scc and admit and emits > 0):
                    fails.append(f"[a] {fx}:{coarse} coarse-D&C NOT admitted "
                                 f"(scc={scc} admit={admit} emits={emits})")
        print()
    # structural: a callee's scc classification must be consistent across fixtures
    for callee, sccs in scc_by_callee.items():
        if len(sccs) > 1:
            fails.append(f"[struct] {callee} scc classification differs across fixtures: {sccs}")

    print("### VERDICT")
    if fails:
        print("  DISCRIMINATION: **FAIL** — misclassified / inconsistent sites:")
        for f in fails:
            print("    -", f)
    else:
        print("  DISCRIMINATION: **PASS**")
        print("    (a) every coarse-D&C site (reduce-tree/search-tree/solve-range/solve/fib) admits, emits>0")
        print("    (b) every flat accessor site (cell-at/cell-value/vec-get/rem-i64/mid-of/...) declines")
        print("    (c) admit == (scc && !tail) at every site — verdict is a pure function of {scc,tail}")
        print("    (structural) each callee's scc classification is identical across all fixtures")
    print()
    return (not fails), all_sites


# ── Baseline matrix ───────────────────────────────────────────────────────────
def run_baseline(binp, files, threads, reps, f4_reps, quick):
    print("## BASELINE MATRIX — Wave-0-feasible configs × thread sweep\n")
    light = ["f1_machinery", "f2_contention", "f3_inverted_search", "f5_compute"]
    for fx in light:
        print(f"### {fx}  (reps={reps})")
        for config in ["serial", "off", "current-syntactic", "admit-all"]:
            for T in threads:
                if config == "serial" and T != threads[0] and T != NPROC:
                    continue  # serial is T-invariant; show endpoints only
                c = measure_cell(binp, files[fx], config, T, reps)
                print(f"  {config:<18} T={T:<3} {fmt_cell(c)}")
            print()
        print()

    # F4-hard: the anchor + config differentiation. Expensive parked cells → few reps.
    print(f"### f4_hard  (anchor reproduction; f4-reps={f4_reps})\n")
    print("  Serial floor + the config differentiation at T=nproc, plus the")
    print("  current-b4on super-linear-in-T ramp (0534 (D)/(4)).\n")
    anchor_cells = []
    for (config, Ts) in [("serial", [1]),
                         ("off", [NPROC]),
                         ("admit-all", [NPROC]),
                         ("current-b4on", [2, 4, 6, NPROC] if not quick else [2, NPROC])]:
        for T in Ts:
            c = measure_cell(binp, files["f4_hard"], config, T, f4_reps)
            anchor_cells.append((config, T, c))
            print(f"  {config:<18} T={T:<3} {fmt_cell(c)}")
    print()
    return anchor_cells


# ── WAVE 1: M-static-only attribution (plan §2 / §8.5) ────────────────────────
# The M-static QUALITY axis alone (CRANELISP_SPARK_ADMIT=mstatic, B4 off) vs the
# syntactic firehose (current-syntactic) and the admit-all ceiling. Per the arch
# ruling (plan §2, §6 U-G5): SINGLE-MECHANISM ROWS ARE DIAGNOSTIC, NOT PASS/FAIL.
# M-static cuts spawn QUALITY (fine flat-accessor sites → 0) but NOT quantity
# (coarse D&C recursion still fires at every level — the fib-explosion; that is
# M-dynamic's ~2/core job in Wave 2). Expect: fewer spawns than syntactic
# (accessors gone), coarse recursion retained, wall improvement partial.
def site_table(binp, clfile, config, T):
    _, sites, _ = instrumented_run(binp, clfile, config, T)
    return [(bare_callee(s), scc, tail, admit, emits)
            for (s, scc, tail, admit, emits) in sites]


def print_site_comparison(binp, clfile, fx, T=None):
    """The M-static QUALITY proof: per-site emits under syntactic vs mstatic.
    Iterates the UNION of both admission modes' site sets so a fine-accessor site
    that VANISHES entirely under mstatic (declined → 0 sparks) is still shown as
    `N -> 0`, the accessor-zero confirmation, rather than dropped from the table.
    Aggregates per (callee, scc, tail) so the repeated-per-call-site rows collapse
    to one line with a summed emit count."""
    if T is None:
        T = NPROC
    def agg(rows):
        d = {}
        for (callee, scc, tail, admit, emits) in rows:
            k = (callee, scc, tail)
            v = d.setdefault(k, [admit, 0, 0])
            v[0] = admit
            v[1] += emits
            v[2] += 1
        return d
    cs = agg(site_table(binp, clfile, "current-syntactic", T))
    ms = agg(site_table(binp, clfile, "mstatic", T))
    keys = sorted(set(cs) | set(ms))
    print(f"  [site emits @ T={T}]  callee            scc   tail  syntactic→mstatic   admit(ms)  class")
    for (callee, scc, tail) in keys:
        e_cs = cs.get((callee, scc, tail), [None, "—", 0])[1]
        adm_ms, e_ms, n = ms.get((callee, scc, tail), [False, 0, 0])
        if callee in KNOWN_FLAT or not scc:
            cls = "FINE  → 0 under mstatic ✓" if e_ms == 0 else "FINE  BUT NONZERO (!)"
        else:
            cls = "COARSE→ retained ✓" if e_ms > 0 else "COARSE→ DROPPED (!)"
        print(f"    {callee:<18} {str(scc):<5} {str(tail):<5} {str(e_cs):>9} → {e_ms:<9} "
              f"{str(adm_ms):<6} {cls}")
    print()


def run_wave1(binp, files, threads, reps, f4_reps, quick, only=None):
    print("## WAVE-1 M-STATIC-ONLY ATTRIBUTION (plan §2 / §8.5)\n")
    print("  ┌─────────────────────────────────────────────────────────────────┐")
    print("  │ SINGLE-MECHANISM ROWS ARE DIAGNOSTIC, NOT PASS/FAIL.              │")
    print("  │ M-static is the QUALITY axis: it cuts WHICH sites spark (fine     │")
    print("  │ accessors → 0) but NOT the COUNT (coarse D&C fires every level).  │")
    print("  │ The ~2/core quantity collapse is M-dynamic's job (Wave 2).        │")
    print("  │ Grade the composed `both` row at Stage 4, not this row.           │")
    print("  └─────────────────────────────────────────────────────────────────┘\n")

    # (fixture, per-fixture reps). Contention fixtures get fewer reps (slow at high T).
    fixtures = [("f1_machinery", reps), ("f5_compute", reps),
                ("f2_contention", min(reps, 5)), ("f3_inverted_search", min(reps, 5)),
                ("f4_hard", f4_reps)]
    if only:
        want = set(only.split(","))
        fixtures = [(fx, r) for (fx, r) in fixtures if fx in want]
    for (fx, r) in fixtures:
        print(f"### {fx}  (reps={r})\n")
        for T in threads:
            cs = measure_cell(binp, files[fx], "current-syntactic", T, r)
            ms = measure_cell(binp, files[fx], "mstatic", T, r)
            print(f"  T={T:<3} current-syntactic  {fmt_cell(cs)}")
            print(f"  T={T:<3} mstatic            {fmt_cell(ms)}")
            # spawn-delta attribution (quality axis): syntactic - mstatic
            sp_cs, sp_ms = cs.get("spawns"), ms.get("spawns")
            if sp_cs is not None and sp_ms is not None:
                drop = sp_cs - sp_ms
                pct = (100.0 * drop / sp_cs) if sp_cs else 0.0
                wr = ""
                if cs.get("status") == "ok" and ms.get("status") == "ok":
                    wr = "  wall_med %.3f→%.3f (%.2fx)" % (
                        cs["wall_med"], ms["wall_med"],
                        cs["wall_med"] / ms["wall_med"] if ms["wall_med"] else 0.0)
                print(f"       Δspawns(syntactic−mstatic) = {drop:,} ({pct:.1f}% cut){wr}")
            print()
        # admit-all reconfirm at T=nproc (env-identical to current-syntactic post-flip)
        aa = measure_cell(binp, files[fx], "admit-all", NPROC, r)
        print(f"  T={NPROC:<3} admit-all         {fmt_cell(aa)}   (≡ current-syntactic post-flip)\n")
        # ── per-site emits: the accessor-zero confirmation (M-static quality proof) ──
        print_site_comparison(binp, files[fx], fx, NPROC)


# ── Adequacy (plan §5) ────────────────────────────────────────────────────────
def run_adequacy(binp, files, reps):
    print("## FIXTURE ADEQUACY (plan §5) — Regime-A positive witness\n")
    T = NPROC
    ser = measure_cell(binp, files["f1_machinery"], "serial", 1, reps)
    best = None
    for config in ["current-syntactic", "admit-all"]:
        c = measure_cell(binp, files["f1_machinery"], config, T, reps)
        if best is None or (c.get("wall_med", 9e9) < best.get("wall_med", 9e9)):
            best = c
    target = ser["wall_med"] / (0.5 * NPROC)
    print(f"  F1 serial wall_med={ser['wall_med']:.4f}s ; best parallel wall_med={best.get('wall_med')}")
    print(f"  Regime-A decisive-win target: wall <= serial/(0.5*nproc) = {target:.4f}s")
    f1_ok = best.get("status") == "ok" and best.get("wall_med", 9e9) <= target
    print(f"  F1 decisively measurable coarse win under a Wave-0 config: {f1_ok}")
    # F5 witness
    if "f5_compute" in files:
        f5s = measure_cell(binp, files["f5_compute"], "serial", 1, reps)
        f5p = measure_cell(binp, files["f5_compute"], "admit-all", T, reps)
        print(f"\n  F5 serial wall_med={f5s['wall_med']:.4f}s (exit={f5s['exit']}) ; "
              f"F5 admit-all(T={T}) wall_med={f5p.get('wall_med')} (exit={f5p.get('exit')})")
        print(f"  F5 parallel≡serial correctness: exit match = {f5s['exit'] == f5p.get('exit')}")
        print("  (F5's DECISIVE coarse-parallel win requires M-static+M-dynamic — graded at")
        print("   Stage 4 / U-G2. In Wave 0 all parallel configs over-spark F5's fib internals;")
        print("   F5 is the PREPARED positive witness, not yet a Wave-0 win.)")
    print(f"\n  ADEQUACY VERDICT: F1 {'ADEQUATE' if f1_ok else 'INADEQUATE'} for Regime A → "
          f"{'no new fixture' if f1_ok else 'F5 authored (tests/fixtures/s99/f5_compute.cl)'}")
    print()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", default="all",
                    choices=["all", "discriminate", "baseline", "adequacy", "wave1"])
    ap.add_argument("--reps", type=int, default=7)
    ap.add_argument("--f4-reps", type=int, default=3)
    ap.add_argument("--threads", default="1,2,4,6,8,10")
    ap.add_argument("--fixtures", default=None,
                    help="wave1 only: comma-list subset e.g. f4_hard,f3_inverted_search")
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()

    binp = os.environ.get("SYS_BIN")
    if not binp or not os.path.exists(binp):
        print("SYS_BIN not set / missing; build with `cargo build --release` and set "
              "SYS_BIN=target/release/cranelisp", file=sys.stderr)
        sys.exit(2)
    threads = [int(x) for x in args.threads.split(",")]

    print(f"# S104 utilization harness  (nproc={NPROC}, idle_floor={IDLE_FLOOR}, "
          f"reps={args.reps}, f4_reps={args.f4_reps})")
    print(f"# binary: {binp}")
    print(f"# start busy_cores={busy_cores():.2f}  load1={os.getloadavg()[0]:.2f}\n")

    files = make_fixtures()

    if args.mode in ("all", "discriminate"):
        run_discrimination(binp, files)
    if args.mode in ("all", "baseline"):
        run_baseline(binp, files, threads, args.reps, args.f4_reps, args.quick)
    if args.mode == "wave1":
        run_wave1(binp, files, threads, args.reps, args.f4_reps, args.quick, args.fixtures)
    if args.mode in ("all", "adequacy"):
        run_adequacy(binp, files, args.reps)


if __name__ == "__main__":
    main()
