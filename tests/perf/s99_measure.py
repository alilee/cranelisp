#!/usr/bin/env python3
"""Sprint 99 Wave 0.3 measurement harness — decompose the parallel "10×".

Drives the four free-standing fixtures in tests/fixtures/s99/ across the
config × allocator × RC-atomicity matrix, collecting wall/user/sys (via
/usr/bin/time) and RC-op/alloc counts (via CRANELISP_RC_STATS). Median of N
reps. NOT part of the canonical `cargo nextest run` — a perf harness.

Knobs used (all from Wave 0.1/0.2, committed):
  CRANELISP_NO_LENIENT=1   genuinely serial (no sparks)
  RAYON_NUM_THREADS=1      single rayon worker (+ main thread)
  RAYON_NUM_THREADS unset  full N-worker pool
  CRANELISP_NONATOMIC_RC=1 plain load/add/store RC (UNSOUND >1 worker; 1-worker only)
  CRANELISP_RC_STATS=1     prints [RC_STATS] rc_inc/rc_dec/allocs/deallocs at exit
  --features thread-caching-alloc  mimalloc #[global_allocator] (separate binary)

Alloc/RC counts are PROCESS-WIDE (no reset_counts seam on --run); we subtract a
no-op --run baseline to isolate program-attributable counts.

Usage:
  SYS_BIN=/path/to/cranelisp-system MI_BIN=/path/to/cranelisp-mimalloc \
      python3 tests/perf/s99_measure.py [--reps 3] [--quick]
If SYS_BIN/MI_BIN unset, builds them with cargo.
"""
import os, sys, subprocess, re, statistics, tempfile, argparse, json, shutil

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
FIX = os.path.join(ROOT, "tests", "fixtures", "s99")
WORK = tempfile.mkdtemp(prefix="s99-measure-")

# Scale for the tunable synthetic fixtures (F1/F2/F3): serial ~0.7s, N-worker ~2.2s.
LEAVES, COPIES = 8192, 256
# COMMITTED must match the committed f4_sudoku.cl puzzle (a solved grid — fast,
# no search). The harness substitutes it for the two timing instances below.
COMMITTED = "483921657967345821251876493548132976729564138136798245372689514814253769695417382"
# EASY: propagation-dominated, light search.
EASY = "003020600900305001001806400008102900700000008006708200002609500800203009005010300"
# HARD requires deep backtracking → exercises the speculative search + contention.
HARD = "800000000003600000070090200050007000000045700000100030001000068008500010090000400"

TIME_RE = re.compile(r"wall=([\d.]+) user=([\d.]+) sys=([\d.]+)")
RC_RE = re.compile(r"\[RC_STATS\] rc_inc=(\d+) rc_dec=(\d+) allocs=(\d+) deallocs=(\d+)")


def scale_synth(src, leaves, copies):
    s = open(src).read()
    s = s.replace("(defn leaves [] 64)", f"(defn leaves [] {leaves})")
    s = s.replace("(defn copies [] 4)", f"(defn copies [] {copies})")
    return s


def gen_fixtures():
    files = {}
    for name in ("f1_machinery", "f2_contention", "f3_inverted_search"):
        p = os.path.join(WORK, name + ".cl")
        open(p, "w").write(scale_synth(os.path.join(FIX, name + ".cl"), LEAVES, COPIES))
        files[name] = p
    # F4: committed fixture ships a solved grid; substitute EASY / HARD for timing.
    f4 = open(os.path.join(FIX, "f4_sudoku.cl")).read()
    pe = os.path.join(WORK, "f4_easy.cl"); open(pe, "w").write(f4.replace(COMMITTED, EASY)); files["f4_easy"] = pe
    ph = os.path.join(WORK, "f4_hard.cl"); open(ph, "w").write(f4.replace(COMMITTED, HARD)); files["f4_hard"] = ph
    # no-op baseline for count subtraction
    pn = os.path.join(WORK, "noop.cl")
    open(pn, "w").write("(import [primitives [*]])\n(defn main [] (Pure 0))\n")
    files["noop"] = pn
    return files


def env_for(config, nonatomic=False, rc_stats=False):
    e = dict(os.environ)
    for k in ("CRANELISP_NO_LENIENT", "RAYON_NUM_THREADS", "CRANELISP_NONATOMIC_RC", "CRANELISP_RC_STATS"):
        e.pop(k, None)
    if config == "serial":
        e["CRANELISP_NO_LENIENT"] = "1"
    elif config == "1worker":
        e["RAYON_NUM_THREADS"] = "1"
    # Nworker: leave rayon default
    if nonatomic:
        e["CRANELISP_NONATOMIC_RC"] = "1"
    if rc_stats:
        e["CRANELISP_RC_STATS"] = "1"
    return e


def time_run(binp, clfile, config, nonatomic=False):
    e = env_for(config, nonatomic=nonatomic)
    cmd = ["/usr/bin/time", "-f", "wall=%e user=%U sys=%S", binp, clfile, "--run"]
    r = subprocess.run(cmd, env=e, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    m = TIME_RE.search(r.stderr.decode())
    if not m:
        raise RuntimeError("no time parse: " + r.stderr.decode()[-300:])
    return float(m.group(1)), float(m.group(2)), float(m.group(3)), r.returncode


def median_time(binp, clfile, config, reps, nonatomic=False):
    walls, users, syss, rc = [], [], [], None
    for _ in range(reps):
        w, u, s, code = time_run(binp, clfile, config, nonatomic)
        walls.append(w); users.append(u); syss.append(s); rc = code
    return (statistics.median(walls), statistics.median(users), statistics.median(syss), rc)


def count_run(binp, clfile, config):
    e = env_for(config, rc_stats=True)
    r = subprocess.run([binp, clfile, "--run"], env=e, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    m = RC_RE.search(r.stderr.decode())
    if not m:
        raise RuntimeError("no rc parse: " + r.stderr.decode()[-300:])
    return tuple(int(m.group(i)) for i in range(1, 5))  # inc,dec,allocs,deallocs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--quick", action="store_true", help="skip F4-hard N-worker system (the slow ~20s cell)")
    args = ap.parse_args()

    sysb = os.environ.get("SYS_BIN")
    mib = os.environ.get("MI_BIN")
    if not sysb or not mib:
        print("SYS_BIN/MI_BIN not set; build them first (cargo build --release [--features thread-caching-alloc])")
        sys.exit(2)

    files = gen_fixtures()
    fixtures = ["f1_machinery", "f2_contention", "f3_inverted_search", "f4_easy", "f4_hard"]
    configs = ["serial", "1worker", "Nworker"]
    allocs = [("system", sysb), ("mimalloc", mib)]

    results = {}
    print(f"# S99 measurement  (LEAVES={LEAVES} COPIES={COPIES}, reps={args.reps}, nproc={os.cpu_count()})\n")
    print("## Timing matrix (median wall / user / sys, seconds)\n")
    hdr = f"{'fixture':<20} {'alloc':<9} {'config':<8} {'wall':>8} {'user':>8} {'sys':>8}  exit"
    print(hdr); print("-" * len(hdr))
    for fx in fixtures:
        for aname, binp in allocs:
            for cfg in configs:
                if args.quick and fx == "f4_hard" and cfg == "Nworker" and aname == "system":
                    continue
                reps = 3 if (fx == "f4_hard" and cfg == "Nworker") else args.reps
                w, u, s, code = median_time(binp, files[fx], cfg, reps)
                results[(fx, aname, cfg, "atomic")] = (w, u, s, code)
                print(f"{fx:<20} {aname:<9} {cfg:<8} {w:>8.2f} {u:>8.2f} {s:>8.2f}  {code}")
        print()

    print("## Non-atomic RC @ 1-worker (system alloc; INDICATIVE — main+1worker) vs atomic\n")
    print(f"{'fixture':<20} {'rc':<10} {'wall':>8} {'user':>8} {'sys':>8}")
    for fx in fixtures:
        wa, ua, sa, _ = median_time(sysb, files[fx], "1worker", args.reps, nonatomic=False)
        wn, un, sn, _ = median_time(sysb, files[fx], "1worker", args.reps, nonatomic=True)
        results[(fx, "system", "1worker", "nonatomic")] = (wn, un, sn, 0)
        print(f"{fx:<20} {'atomic':<10} {wa:>8.2f} {ua:>8.2f} {sa:>8.2f}")
        print(f"{fx:<20} {'nonatomic':<10} {wn:>8.2f} {un:>8.2f} {sn:>8.2f}")
    print()

    print("## RC-op + alloc counts (system alloc, serial; program-attributable = raw − noop baseline)\n")
    base = count_run(sysb, files["noop"], "serial")
    print(f"noop baseline: rc_inc={base[0]} rc_dec={base[1]} allocs={base[2]} deallocs={base[3]}\n")
    print(f"{'fixture':<20} {'rc_inc':>12} {'rc_dec':>12} {'allocs':>12} {'deallocs':>12}")
    for fx in fixtures:
        c = count_run(sysb, files[fx], "serial")
        prog = tuple(c[i] - base[i] for i in range(4))
        results[(fx, "counts")] = prog
        print(f"{fx:<20} {prog[0]:>12} {prog[1]:>12} {prog[2]:>12} {prog[3]:>12}")
    print()

    json.dump({str(k): v for k, v in results.items()},
              open(os.path.join(WORK, "results.json"), "w"), indent=2)
    print("raw results:", os.path.join(WORK, "results.json"))


if __name__ == "__main__":
    main()
