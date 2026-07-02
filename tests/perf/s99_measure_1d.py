#!/usr/bin/env python3
"""Sprint 99 Wave 1d — mimalloc (a)-cure ablation + combined shippable stack.

Mirrors tests/perf/s99_measure.py and scratchpad/ablation_1c.py, adds the
system-vs-mimalloc allocator axis AND the CRANELISP_SATURATION_GATE axis so we
can report:

  §10.1  clean (a) recovery: F1-F4, system vs mimalloc, N-worker.
         LEAD WITH SYS TIME (the clean attributable (a) signal, immune to the
         F4 search-path variance that burned two false-greens). Full per-rep
         min/med/max spread. Also report whether mimalloc moves user-time.
  §10.2  combined shippable stack: baseline (system alloc, default create-gate)
         vs mimalloc + CRANELISP_SATURATION_GATE=1, F4 + F2, wall/user/sys.
  §10.3  floor: after mimalloc+gate, how far is parallel from serial on F2/F4?

Two binaries required (build both first):
  cargo build --release                              -> SYS_BIN
  cargo build --release --features thread-caching-alloc -> MI_BIN
The saturation gate is a runtime env toggle compiled into BOTH binaries
(byte-identical-off), so it composes with either allocator.

Usage:
  SYS_BIN=/abs/cranelisp-system MI_BIN=/abs/cranelisp-mimalloc \
      python3 tests/perf/s99_measure_1d.py [reps]
"""
import os, sys, subprocess, re, statistics, tempfile

ROOT = "/home/alilee/cranelisp"
FIX = os.path.join(ROOT, "tests", "fixtures", "s99")
WORK = tempfile.mkdtemp(prefix="s99-1d-")

LEAVES, COPIES = 8192, 256
COMMITTED = "483921657967345821251876493548132976729564138136798245372689514814253769695417382"
HARD = "800000000003600000070090200050007000000045700000100030001000068008500010090000400"

TIME_RE = re.compile(r"wall=([\d.]+) user=([\d.]+) sys=([\d.]+)")
RC_RE = re.compile(r"\[RC_STATS\] rc_inc=(\d+) rc_dec=(\d+) allocs=(\d+) deallocs=(\d+)")

SYS_BIN = os.environ["SYS_BIN"]
MI_BIN = os.environ["MI_BIN"]


def scale_synth(src, leaves, copies):
    s = open(src).read()
    s = s.replace("(defn leaves [] 64)", f"(defn leaves [] {leaves})")
    s = s.replace("(defn copies [] 4)", f"(defn copies [] {copies})")
    return s


def gen():
    files = {}
    for name in ("f1_machinery", "f2_contention", "f3_inverted_search"):
        p = os.path.join(WORK, name + ".cl")
        open(p, "w").write(scale_synth(os.path.join(FIX, name + ".cl"), LEAVES, COPIES))
        files[name] = p
    f4 = open(os.path.join(FIX, "f4_sudoku.cl")).read()
    ph = os.path.join(WORK, "f4_hard.cl")
    open(ph, "w").write(f4.replace(COMMITTED, HARD))
    files["f4_hard"] = ph
    return files


def env_for(config, gate=False, rc_stats=False):
    e = dict(os.environ)
    for k in ("CRANELISP_NO_LENIENT", "RAYON_NUM_THREADS",
              "CRANELISP_SATURATION_GATE", "CRANELISP_CAPTURE_BORROW",
              "CRANELISP_RC_STATS"):
        e.pop(k, None)
    if config == "serial":
        e["CRANELISP_NO_LENIENT"] = "1"
    elif config == "1worker":
        e["RAYON_NUM_THREADS"] = "1"
    # Nworker: rayon default
    if gate:
        e["CRANELISP_SATURATION_GATE"] = "1"
    if rc_stats:
        e["CRANELISP_RC_STATS"] = "1"
    return e


def one(binp, clfile, config, gate=False):
    e = env_for(config, gate=gate)
    cmd = ["/usr/bin/time", "-f", "wall=%e user=%U sys=%S", binp, clfile, "--run"]
    r = subprocess.run(cmd, env=e, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    m = TIME_RE.search(r.stderr.decode())
    if not m:
        raise RuntimeError("no time parse: " + r.stderr.decode()[-300:])
    return float(m.group(1)), float(m.group(2)), float(m.group(3)), r.returncode


def series(binp, clfile, config, reps, gate=False):
    W, U, S, codes = [], [], [], []
    for _ in range(reps):
        w, u, s, c = one(binp, clfile, config, gate=gate)
        W.append(w); U.append(u); S.append(s); codes.append(c)
    return W, U, S, codes


def fmt(xs):
    return f"{min(xs):5.2f}/{statistics.median(xs):5.2f}/{max(xs):5.2f}"


def med(xs):
    return statistics.median(xs)


def main():
    reps = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    files = gen()
    fixtures = ["f1_machinery", "f2_contention", "f3_inverted_search", "f4_hard"]
    print(f"# S99 Wave 1d — mimalloc (a)-cure ablation "
          f"(LEAVES={LEAVES} COPIES={COPIES}, reps={reps}, nproc={os.cpu_count()})")
    print(f"# spread shown as min/med/max\n")

    store = {}

    # ---- §10.1  system vs mimalloc, all configs ----
    print("## §10.1  clean (a) recovery — system vs mimalloc")
    print(f"{'fixture':<18} {'alloc':<9} {'config':<9} {'wall(min/med/max)':>20} "
          f"{'user':>20} {'sys':>20} exit")
    for fx in fixtures:
        for aname, binp in (("system", SYS_BIN), ("mimalloc", MI_BIN)):
            for cfg in ("serial", "Nworker"):
                W, U, S, c = series(binp, files[fx], cfg, reps)
                store[(fx, aname, cfg, "nogate")] = (W, U, S, c)
                print(f"{fx:<18} {aname:<9} {cfg:<9} {fmt(W):>20} {fmt(U):>20} "
                      f"{fmt(S):>20} {set(c)}")
        print()

    # ---- §10.2  combined shippable stack ----
    print("## §10.2  combined stack — baseline(system,no-gate) vs mimalloc+gate")
    print(f"{'fixture':<18} {'stack':<22} {'wall(min/med/max)':>20} "
          f"{'user':>20} {'sys':>20} exit")
    for fx in ("f2_contention", "f4_hard"):
        # baseline already measured (system, Nworker, nogate)
        bW, bU, bS, bc = store[(fx, "system", "Nworker", "nogate")]
        print(f"{fx:<18} {'system,no-gate':<22} {fmt(bW):>20} {fmt(bU):>20} "
              f"{fmt(bS):>20} {set(bc)}")
        # mimalloc + gate
        mW, mU, mS, mc = series(MI_BIN, files[fx], "Nworker", reps, gate=True)
        store[(fx, "mimalloc", "Nworker", "gate")] = (mW, mU, mS, mc)
        print(f"{fx:<18} {'mimalloc+gate':<22} {fmt(mW):>20} {fmt(mU):>20} "
              f"{fmt(mS):>20} {set(mc)}")
        # also mimalloc-alone Nworker gate for isolation of the gate contribution
        print()

    # ---- §10.3  floor: parallel-vs-serial after combined stack ----
    print("## §10.3  floor — combined(mimalloc+gate) N-worker vs serial")
    print(f"{'fixture':<18} {'serial wall/user/sys(med)':>28} "
          f"{'combined wall/user/sys(med)':>30}  slowdown(wall/user/sys)")
    for fx in ("f2_contention", "f4_hard"):
        sW, sU, sS, _ = store[(fx, "system", "serial", "nogate")]
        cW, cU, cS, _ = store[(fx, "mimalloc", "Nworker", "gate")]
        ser = f"{med(sW):.2f}/{med(sU):.2f}/{med(sS):.2f}"
        comb = f"{med(cW):.2f}/{med(cU):.2f}/{med(cS):.2f}"
        sd = (f"{med(cW)/med(sW):.1f}x/"
              f"{med(cU)/med(sU):.1f}x/"
              f"{med(cS)/max(med(sS),0.01):.1f}x")
        print(f"{fx:<18} {ser:>28} {comb:>30}  {sd}")
    print()

    # ---- derived headline reductions ----
    print("## derived — (a) sys recovery + combined recovery (medians)")
    for fx in fixtures:
        sysW, sysU, sysS, _ = store[(fx, "system", "Nworker", "nogate")]
        miW, miU, miS, _ = store[(fx, "mimalloc", "Nworker", "nogate")]
        print(f"{fx}:  Nworker sys-time  system {med(sysS):.2f} -> mimalloc "
              f"{med(miS):.2f}  ({med(sysS)/max(med(miS),0.01):.1f}x)   "
              f"user {med(sysU):.2f}->{med(miU):.2f}  "
              f"wall {med(sysW):.2f}->{med(miW):.2f}")


if __name__ == "__main__":
    main()
