#!/usr/bin/env python3
"""S105 residual-attribution instrument — the per-fixture attribution vector.

Implements `tests/plan/s105-residual-attribution.md` (Phase-3 plan): the upgraded
instrument that attributes the post-increment-II F3/F4 parallel residual BY
MECHANISM — {scheduler-spread, (a)-allocation, residual-atomic-RC,
unavailable-parallelism} + the named joint interaction term `I` — so the build
phase selects the evidence-supported lever rather than an asserted one.

## What it produces (per fixture)
  * the **2×2 factorial** (allocator-swap × ownership-off) walls + the explicit
    interaction `I = baseline − ¬a − ¬b + ¬a∧¬b` (§2, §3.1.6-R1);
  * the **fine-probe** direct-oracle net-recovery columns — `CRANELISP_NONATOMIC_RC`
    (b-via-RC), `CRANELISP_CAPTURE_BORROW` (b-via-borrow), `CRANELISP_NO_STACK_ALLOC`
    (a-via-stack), and the COARSE `CRANELISP_NO_OWNERSHIP` CEILING only (§3, §4);
  * the **core-count speedup-ceiling sweep** RAYON_NUM_THREADS ∈ {1,2,4,6,8,10} (I5);
  * the **syscall profile** (strace -c futex/sched_yield vs brk/mmap share, I1);
  * the **HW HITM** row (perf stat) — marked UNAVAILABLE gracefully if the PMU is
    blocked (I4, scope-gap #3);
  * F8's **gate-5 sub-verdict** — per-arm STACK_SLOT_HITS (serial>0, parallel=0)
    and the per-arm stack-oracle net-recovery (§5.2, §4.1);
  * the per-fixture **[S105-GATE ...]** verdict block (§6).

## Doctrine guards (§0 / §7 — non-negotiable, encoded as INVALID-marking preconds)
  G-wall-off     : every timed region runs with ALL stats/trace env UNSET; a wall
                   taken with a counter set is dropped `[INVALID: stats-on]`.
  G-separate     : counts + walls come from DISTINCT process invocations (never one).
  G-idle-oob     : idleness confirmed out-of-band (instantaneous /proc/stat busy-cores
                   probe in the pre-rep gap, s104 refinement) — a rep that cannot
                   confirm idle full-cores is `[INVALID: busy_cores=X]` (NOT benign)
                   and excluded from the median.
  G-hw-external  : perf stat / strace -c run EXTERNALLY, on graded cells only, on
                   their own runs — never composed with the counter-off wall.
  G-two-build    : the allocator factorial uses two release builds (system vs
                   `--features thread-caching-alloc`); walls compared only within
                   the factorial, each cell labelled with its build id.

Single-sourced (Principle 7) on the S104 harnesses: fixture generation, the
busy-cores idle probe, and the config-env scaffold are imported from
`s99_measure` / `s104_utilization`, not mirrored.

Usage:
  SYS_BIN=.../cranelisp-system MI_BIN=.../cranelisp-mimalloc \
    python3 tests/perf/s105_attribution.py \
      [--mode all|factorial|fine|sweep|syscall|hw|stack|gate] \
      [--fixtures f4_hard,f3_inverted_search,f7_alloc,f8_stack_witness] \
      [--reps 3] [--threads 1,2,4,6,8,10]
"""
import os, sys, subprocess, re, statistics, argparse, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import s99_measure as s99          # gen_fixtures / scale_synth / FIX / WORK
import s104_utilization as s104    # busy_cores / NPROC / idle_max_cores

NPROC = s104.NPROC
DEVNULL = subprocess.DEVNULL
PIPE = subprocess.PIPE

# ── Full [RC_STATS] grammar (post-S105 N1: alloc_bytes appended at the tail) ──
RC_RE = re.compile(
    r"\[RC_STATS\] rc_inc=(\d+) rc_dec=(\d+) allocs=(\d+) deallocs=(\d+) "
    r"stack_slot=(\d+) reuse_hit=(\d+) reuse_miss=(\d+) "
    r"rc_nonatomic=(\d+) rc_atomic=(\d+) str-len_adapt=(\d+) alloc_bytes=(\d+)")
RC_FIELDS = ["rc_inc", "rc_dec", "allocs", "deallocs", "stack_slot", "reuse_hit",
             "reuse_miss", "rc_nonatomic", "rc_atomic", "str_len_adapt", "alloc_bytes"]

# Env keys the harness must scrub before a graded WALL (G-wall-off). Any stats/trace
# gate perturbs the wall with its atomics — a wall taken with one set is INVALID.
STATS_ENV = ("CRANELISP_RC_STATS", "CRANELISP_SPARK_STATS", "CRANELISP_OWNERSHIP_TRACE",
             "CRANELISP_CODEGEN_TRACE", "CRANELISP_RC_TRACE", "CRANELISP_SPARK_DENSITY_TRACE",
             "CRANELISP_SCHEDULER_TRACE")
# Semantic toggles the harness sets (never perturb the wall — they change codegen).
SEM_ENV = ("CRANELISP_NO_LENIENT", "CRANELISP_NO_OWNERSHIP", "CRANELISP_NONATOMIC_RC",
           "CRANELISP_CAPTURE_BORROW", "CRANELISP_NO_STACK_ALLOC", "RAYON_NUM_THREADS")


# ── Fixtures ──────────────────────────────────────────────────────────────────
def make_fixtures():
    files = s104.make_fixtures()   # f1_machinery..f6_parwin, f4_easy/hard, f2v, noop
    # F7 / F8 are copied VERBATIM (no scale_synth blow-up: F7 must stay shallow /
    # scheduler-light; F8's gate-5 shape must not be rescaled).
    for name in ("f7_alloc", "f8_stack_witness"):
        src = os.path.join(s99.FIX, name + ".cl")
        p = os.path.join(s99.WORK, name + ".cl")
        open(p, "w").write(open(src).read())
        files[name] = p
    # F8 per-arm variants (sliced on the region markers) for the clean per-arm
    # STACK_SLOT_HITS read (the global codegen counter attributes cleanly only when
    # one arm is present).
    sv, pv = _gen_f8_variants(open(os.path.join(s99.FIX, "f8_stack_witness.cl")).read())
    files["f8_serial"], files["f8_parallel"] = sv, pv
    return files


def _gen_f8_variants(src):
    def strip(s, name):
        return re.sub(r";;S105-F8-%s-BEGIN.*?;;S105-F8-%s-END\n" % (name, name),
                      "", s, flags=re.S)
    def pick_main(s, which):
        s = re.sub(r";;S105-F8-MAIN-BOTH\n.*?;;S105-F8-MAIN-BOTH-END\n", "", s, flags=re.S)
        keep = {"SERIAL": "MAIN-SERIAL", "PARALLEL": "MAIN-PARALLEL"}[which]
        drop = {"SERIAL": "MAIN-PARALLEL", "PARALLEL": "MAIN-SERIAL"}[which]
        s = re.sub(r";;S105-F8-%s   " % keep, "", s)      # uncomment chosen main
        s = re.sub(r";;S105-F8-%s .*\n" % drop, "", s)    # drop the other
        return s
    out = {}
    for arm in ("SERIAL", "PARALLEL"):
        s = strip(src, "PARALLEL" if arm == "SERIAL" else "SERIAL")
        s = pick_main(s, arm)
        p = os.path.join(s99.WORK, "f8_%s.cl" % arm.lower())
        open(p, "w").write(s)
        out[arm] = p
    return out["SERIAL"], out["PARALLEL"]


# ── Env builders ──────────────────────────────────────────────────────────────
def wall_env(serial=False, no_ownership=False, nonatomic=False, capture_borrow=False,
             no_stack=False, threads=None):
    """A counter-OFF wall env (G-wall-off). Sets only the semantic toggles; scrubs
    every stats/trace gate so the wall is unperturbed."""
    e = dict(os.environ)
    for k in STATS_ENV + SEM_ENV:
        e.pop(k, None)
    if serial:         e["CRANELISP_NO_LENIENT"] = "1"
    if no_ownership:   e["CRANELISP_NO_OWNERSHIP"] = "1"
    if nonatomic:      e["CRANELISP_NONATOMIC_RC"] = "1"
    if capture_borrow: e["CRANELISP_CAPTURE_BORROW"] = "1"
    if no_stack:       e["CRANELISP_NO_STACK_ALLOC"] = "1"
    if threads is not None:
        e["RAYON_NUM_THREADS"] = str(threads)
    return e


def counts_env(serial=False, no_stack=False):
    """A SEPARATE counts run (G-separate): RC_STATS on. Never timed."""
    e = dict(os.environ)
    for k in STATS_ENV + SEM_ENV:
        e.pop(k, None)
    e["CRANELISP_RC_STATS"] = "1"
    if serial:   e["CRANELISP_NO_LENIENT"] = "1"
    if no_stack: e["CRANELISP_NO_STACK_ALLOC"] = "1"
    return e


def _assert_wall_clean(e):
    bad = [k for k in STATS_ENV if k in e]
    return bad  # non-empty ⇒ INVALID: stats-on


# ── Timed wall (counter-off) + out-of-band idle guard ─────────────────────────
def timed_wall(binp, clfile, env, reps):
    """Median counter-off wall over `reps`, with a pre-rep out-of-band idle probe
    (G-idle-oob). Returns (wall_med|None, meta). A rep that cannot confirm idle
    full-cores is INVALID (excluded), NOT benign."""
    bad = _assert_wall_clean(env)
    if bad:
        return None, {"status": "INVALID: stats-on (%s)" % ",".join(bad)}
    T = env.get("RAYON_NUM_THREADS")
    T = int(T) if T else NPROC
    imax = s104.idle_max_cores(T)
    walls, invalids, loads, code = [], 0, [], None
    for r in range(reps + 1):        # +1 warm-exclude
        bc = s104.busy_cores()        # nothing of ours running now (out-of-band)
        invalid = bc > imax
        t0 = time.perf_counter()
        p = subprocess.run([binp, clfile, "--run"], env=env, stdout=DEVNULL, stderr=DEVNULL)
        wall = time.perf_counter() - t0
        code = p.returncode
        if r == 0:
            continue                  # warm rep discarded (JIT / page cache)
        loads.append(round(bc, 2))
        if invalid:
            invalids += 1
            continue
        walls.append(wall)
    meta = {"invalids": invalids, "reps": reps, "loads": loads, "exit": code}
    if not walls or invalids > 0.4 * reps:
        meta["status"] = "INVALID: busy_cores=%s" % (max(loads) if loads else "?")
        return None, meta
    meta["status"] = "ok"
    return statistics.median(walls), meta


def counts(binp, clfile, env):
    """Separate RC_STATS run → dict of the 11 counters (or None)."""
    r = subprocess.run([binp, clfile, "--run"], env=env, stdout=DEVNULL, stderr=PIPE)
    m = RC_RE.search(r.stderr.decode(errors="replace"))
    if not m:
        return None
    return dict(zip(RC_FIELDS, (int(x) for x in m.groups())))


# ── I6: the 2×2 allocator-swap × ownership-off factorial (§2) ──────────────────
def factorial(sysb, mib, clfile, reps):
    """{baseline, ¬a, ¬b, ¬a∧¬b} counter-off walls + explicit interaction I. The
    (a) axis is the TWO-BUILD allocator swap (G-two-build); the (b) axis is the
    COARSE NO_OWNERSHIP ceiling oracle (§2 last para: the ceiling factorial uses
    NO_OWNERSHIP; the fine apportionment is done separately in fine())."""
    cells = {}
    for key, binp, own_off in [("baseline", sysb, False), ("¬a", mib, False),
                               ("¬b", sysb, True), ("¬a∧¬b", mib, True)]:
        w, meta = timed_wall(binp, clfile, wall_env(no_ownership=own_off), reps)
        cells[key] = (w, meta)
    b = cells["baseline"][0]; na = cells["¬a"][0]; nb = cells["¬b"][0]; nab = cells["¬a∧¬b"][0]
    I = (b - na - nb + nab) if None not in (b, na, nb, nab) else None
    return cells, I


# ── fine-probe direct-oracle net-recovery (§3 / §4) ───────────────────────────
def fine(sysb, clfile, reps):
    """Each fine probe's net wall recovery vs the coupled baseline (system, all-on).
    Granularity-disciplined (§3): the stack/RC/borrow FINE probes apportion; the
    COARSE NO_OWNERSHIP is reported ONLY as the ceiling, never as a (b) toggle."""
    base, _ = timed_wall(sysb, clfile, wall_env(), reps)
    out = {"baseline": base}
    probes = [("nonatomic_rc", dict(nonatomic=True), "b-via-RC (fine)"),
              ("capture_borrow", dict(capture_borrow=True), "b-via-borrow (fine)"),
              ("no_stack_alloc", dict(no_stack=True), "a-via-stack (fine)"),
              ("no_ownership(CEILING)", dict(no_ownership=True), "COARSE all-memory-off ceiling")]
    for name, kw, _desc in probes:
        w, meta = timed_wall(sysb, clfile, wall_env(**kw), reps)
        rec = (base - w) if (base is not None and w is not None) else None
        out[name] = (w, rec, meta.get("status"))
    return out


# ── I5: core-count speedup-ceiling sweep (§6.1 accept-done criterion) ──────────
def sweep(sysb, clfile, reps, threads):
    ser, _ = timed_wall(sysb, clfile, wall_env(serial=True), max(1, reps // 2))
    rows = []
    for T in threads:
        w, meta = timed_wall(sysb, clfile, wall_env(threads=T), reps)
        sp = (ser / w) if (ser and w) else None
        rows.append((T, w, sp, meta.get("status")))
    ceiling = max((sp for (_, _, sp, st) in rows if sp and st == "ok"), default=None)
    return ser, rows, ceiling


# ── I1: syscall profile (strace -c share) — EXTERNAL, graded cell only ─────────
def syscall_profile(binp, clfile, serial=False):
    e = wall_env(serial=serial)   # counter-off (strace itself is the instrument)
    try:
        r = subprocess.run(["strace", "-f", "-c", "-w", binp, clfile, "--run"],
                           env=e, stdout=DEVNULL, stderr=PIPE, timeout=180)
    except (FileNotFoundError, subprocess.TimeoutExpired) as ex:
        return {"status": "UNAVAILABLE: %s" % type(ex).__name__}
    txt = r.stderr.decode(errors="replace")
    calls = {}
    for line in txt.splitlines():
        m = re.match(r"\s*[\d.]+\s+[\d.]+\s+\d+\s+(\d+)\s+\d*\s*(\w+)$", line)
        if m:
            calls[m.group(2)] = calls.get(m.group(2), 0) + int(m.group(1))
    tot = sum(calls.values()) or 1
    sched = sum(calls.get(k, 0) for k in ("futex", "sched_yield"))
    alloc = sum(calls.get(k, 0) for k in ("brk", "mmap", "munmap", "madvise"))
    return {"status": "ok", "total": tot,
            "sched_share": round(100.0 * sched / tot, 1),
            "alloc_share": round(100.0 * alloc / tot, 1),
            "futex": calls.get("futex", 0), "sched_yield": calls.get("sched_yield", 0),
            "brk": calls.get("brk", 0), "mmap": calls.get("mmap", 0)}


# ── I4: HW HITM (perf stat) — EXTERNAL; UNAVAILABLE if PMU blocked ─────────────
def hw_hitm(binp, clfile):
    ev = "mem_load_l3_miss_retired.remote_hitm,cache-misses,context-switches"
    e = wall_env()
    try:
        r = subprocess.run(["perf", "stat", "-e", ev, binp, clfile, "--run"],
                           env=e, stdout=DEVNULL, stderr=PIPE, timeout=180)
    except (FileNotFoundError, subprocess.TimeoutExpired) as ex:
        return {"status": "UNAVAILABLE: %s" % type(ex).__name__}
    txt = r.stderr.decode(errors="replace")
    if "not supported" in txt or "Permission" in txt or "perf_event_paranoid" in txt \
       or "<not supported>" in txt:
        return {"status": "UNAVAILABLE: host PMU (perf_event_paranoid / virtualized)"}
    hitm = re.search(r"([\d,]+)\s+mem_load.*remote_hitm", txt)
    cs = re.search(r"([\d,]+)\s+context-switches", txt)
    return {"status": "ok",
            "hitm": hitm.group(1) if hitm else "?",
            "ctx_sw": cs.group(1) if cs else "?"}


# ── F8 gate-5 sub-verdict — per-arm STACK_SLOT_HITS + stack-oracle recovery ────
def f8_gate5(sysb, files, reps):
    out = {}
    for arm in ("f8_serial", "f8_parallel"):
        # per-arm STACK_SLOT_HITS: serial-compilation (NO_LENIENT) vs lenient, and
        # the direct stack-oracle allocs recovery (stack-ON vs NO_STACK_ALLOC).
        c_serial_on = counts(sysb, files[arm], counts_env(serial=True))
        c_serial_off = counts(sysb, files[arm], counts_env(serial=True, no_stack=True))
        c_par_on = counts(sysb, files[arm], counts_env(serial=False))
        # wall net-recovery on this arm (stack ON vs OFF), counter-off
        w_on, _ = timed_wall(sysb, files[arm], wall_env(serial=True), reps)
        w_off, _ = timed_wall(sysb, files[arm], wall_env(serial=True, no_stack=True), reps)
        out[arm] = dict(
            stack_serial=(c_serial_on or {}).get("stack_slot"),
            stack_parallel=(c_par_on or {}).get("stack_slot"),
            allocs_stackon=(c_serial_on or {}).get("allocs"),
            allocs_nostack=(c_serial_off or {}).get("allocs"),
            wall_stackon=w_on, wall_nostack=w_off)
    return out


# ── attribution vector + gate verdict (§6) ────────────────────────────────────
def fmt_wall(w):
    return "%.3fs" % w if isinstance(w, float) else str(w)


def emit_gate(fx, fac, I, fn, sw, sysc_par, hw, cnts):
    ser, rows, ceiling = sw
    print(f"\n[S105-GATE fixture={fx}]")
    # residual: parallel(T=nproc) − serial
    par = next((w for (T, w, _, st) in rows if T == NPROC and st == "ok" and w), None)
    if ser and par:
        print("  residual (parallel@%d − serial): %.3f − %.3f = %+.3fs (%.2fx)" % (
            NPROC, par, ser, par - ser, par / ser if ser else 0))
    else:
        print("  residual: serial=%s parallel@%d=%s" % (fmt_wall(ser), NPROC, fmt_wall(par)))
    b = fine.__doc__ and None
    base = fn["baseline"]
    def rec(name):
        v = fn.get(name)
        if not v or v[1] is None:
            return "n/a (%s)" % (v[2] if v else "—")
        return "%+.3fs" % v[1]
    print("  attribution vector (oracle-bounded direct-oracle net-recovery):")
    print("    scheduler-spread     : sweep-ceiling %s (I5); syscall sched-share %s%%" % (
        ("%.2fx" % ceiling if ceiling else "?"),
        (sysc_par.get("sched_share") if sysc_par.get("status") == "ok" else "UNAVAIL")))
    print("    (a)-allocation       : %s via NO_STACK_ALLOC(fine); 2x2 ¬a=%s  [allocs=%s bytes=%s]" % (
        rec("no_stack_alloc"), fmt_wall(fac["¬a"][0]),
        (cnts or {}).get("allocs"), (cnts or {}).get("alloc_bytes")))
    print("    residual-atomic-RC   : %s via NONATOMIC_RC(fine) + %s via CAPTURE_BORROW  [rc_atomic=%s]" % (
        rec("nonatomic_rc"), rec("capture_borrow"), (cnts or {}).get("rc_atomic")))
    print("    unavailable-parallel : speedup ceiling %s at T≤%d (I5)" % (
        ("%.2fx" % ceiling if ceiling else "?"), NPROC))
    print("    COARSE ceiling       : NO_OWNERSHIP net %s (all-memory-model-addressable bound, §3-R3)" % (
        rec("no_ownership(CEILING)")))
    print("    I (a/b coupling)     : %s  [NAMED joint term, not folded — §2-R1]" % (
        ("%+.3fs" % I) if I is not None else "n/a"))
    if hw.get("status") == "ok":
        print("    HITM (I4)            : %s remote-hitm, %s ctx-sw" % (hw["hitm"], hw["ctx_sw"]))
    else:
        print("    HITM (I4)            : %s → (b) rests on NONATOMIC_RC alone (scope-gap #3)" % hw["status"])


def report_fixture(fx, sysb, mib, files, reps, threads):
    print("\n" + "=" * 78)
    print("### %s" % fx)
    clf = files[fx]
    cnts = counts(sysb, clf, counts_env())             # separate counts run (G-separate)
    fac, I = factorial(sysb, mib, clf, reps)
    print("  2×2 factorial (counter-off walls, G-two-build):")
    for k in ("baseline", "¬a", "¬b", "¬a∧¬b"):
        w, meta = fac[k]
        print("    %-6s %-10s [%s]" % (k, fmt_wall(w), meta.get("status")))
    print("    I = baseline − ¬a − ¬b + ¬a∧¬b = %s" % (("%+.3fs" % I) if I is not None else "n/a"))
    fn = fine(sysb, clf, reps)
    print("  fine-probe direct-oracle net-recovery (base=%s):" % fmt_wall(fn["baseline"]))
    for name in ("no_stack_alloc", "nonatomic_rc", "capture_borrow", "no_ownership(CEILING)"):
        w, r, st = fn[name]
        print("    %-22s wall=%-8s net-recovery=%-9s [%s]" % (
            name, fmt_wall(w), ("%+.3fs" % r) if r is not None else "n/a", st))
    sw = sweep(sysb, clf, reps, threads)
    ser, rows, ceiling = sw
    print("  core-count sweep (serial=%s, speedup=serial/wall(T)):" % fmt_wall(ser))
    for (T, w, sp, st) in rows:
        print("    T=%-2d wall=%-8s speedup=%-6s [%s]" % (
            T, fmt_wall(w), ("%.2fx" % sp) if sp else "?", st))
    print("    speedup CEILING = %s" % (("%.2fx" % ceiling) if ceiling else "?"))
    sysc_par = syscall_profile(sysb, clf, serial=False)
    print("  syscall profile (strace -c, parallel, EXTERNAL): %s" % (
        ("sched=%s%% alloc=%s%% [futex=%s yield=%s brk=%s mmap=%s]" % (
            sysc_par["sched_share"], sysc_par["alloc_share"], sysc_par["futex"],
            sysc_par["sched_yield"], sysc_par["brk"], sysc_par["mmap"]))
        if sysc_par.get("status") == "ok" else sysc_par["status"]))
    hw = hw_hitm(sysb, clf)
    emit_gate(fx, fac, I, fn, sw, sysc_par, hw, cnts)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", default="all",
                    choices=["all", "factorial", "fine", "sweep", "syscall", "hw", "stack", "gate"])
    ap.add_argument("--fixtures",
                    default="f4_hard,f3_inverted_search,f7_alloc,f8_stack_witness")
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--threads", default="1,2,4,6,8,10")
    args = ap.parse_args()

    sysb = os.environ.get("SYS_BIN")
    mib = os.environ.get("MI_BIN")
    if not sysb or not os.path.exists(sysb):
        print("SYS_BIN unset/missing (system release build)", file=sys.stderr); sys.exit(2)
    if not mib or not os.path.exists(mib):
        print("MI_BIN unset/missing (--features thread-caching-alloc build)", file=sys.stderr); sys.exit(2)
    threads = [int(x) for x in args.threads.split(",")]

    files = make_fixtures()
    print("# S105 attribution harness  (nproc=%d, reps=%d)" % (NPROC, args.reps))
    print("# SYS_BIN=%s\n# MI_BIN=%s" % (sysb, mib))
    print("# start busy_cores=%.2f  load1=%.2f" % (s104.busy_cores(), os.getloadavg()[0]))
    print("# DOCTRINE: walls counter-OFF; counts separate run; idle out-of-band "
          "(INVALID-not-benign); HW external.")

    if args.mode in ("all", "stack", "gate"):
        print("\n" + "=" * 78)
        print("## F8 gate-5 sub-verdict — per-arm STACK_SLOT_HITS + stack-oracle recovery (§5.2)")
        g = f8_gate5(sysb, files, args.reps)
        for arm in ("f8_serial", "f8_parallel"):
            d = g[arm]
            print("  %-12s stack_slot[serial-compile]=%s  stack_slot[lenient]=%s" % (
                arm, d["stack_serial"], d["stack_parallel"]))
            print("               allocs[stackON]=%s allocs[NO_STACK_ALLOC]=%s  "
                  "→ heap-alloc recovery=%s" % (
                d["allocs_stackon"], d["allocs_nostack"],
                (d["allocs_nostack"] - d["allocs_stackon"])
                if None not in (d["allocs_nostack"], d["allocs_stackon"]) else "?"))
            print("               wall[stackON]=%s wall[NO_STACK_ALLOC]=%s" % (
                fmt_wall(d["wall_stackon"]), fmt_wall(d["wall_nostack"])))
        sh = g["f8_serial"]["stack_serial"]; ph = g["f8_parallel"]["stack_serial"]
        pl = g["f8_parallel"]["stack_parallel"]
        print("  SUB-VERDICT: serial-arm hits=%s (>0 expected), parallel-arm hits=%s/%s "
              "(serial-compile/lenient; =0 expected ⇒ (a) on the parallel path is behind "
              "gate 3+5 — the stack lever does NOT recover it)" % (sh, ph, pl))

    if args.mode in ("all", "gate", "factorial", "fine", "sweep", "syscall", "hw"):
        for fx in args.fixtures.split(","):
            if fx not in files:
                print("\n### %s — UNKNOWN FIXTURE" % fx); continue
            report_fixture(fx, sysb, mib, files, args.reps, threads)


if __name__ == "__main__":
    main()
