# S105 residual-attribution — RESULTS + decision-gate verdict (Wave 1)

**Author:** `/qa` · **Date:** 2026-07-07 (Phase-5 Wave-1) ·
**Instrument:** `tests/perf/s105_attribution.py` (Wave-0, this sprint) ·
**Plan:** `tests/plan/s105-residual-attribution.md` (the Phase-3 spec this executes) ·
**Binaries:** two release builds — system allocator + `--features thread-caching-alloc`
(mimalloc); nproc=10.

> **Bottom line (decision gate).** The F4-hard parallel residual (the named
> primary target, ~2.7×) is **unavailable-parallelism → accept-done**. Every
> memory-lever direct oracle is flat or **negative** on F4-hard, the coarse
> `NO_OWNERSHIP` ceiling is **negative**, and the core-count speedup ceiling is
> **1.02×** and *degrades* with cores (0.36× at T=10). Near-serial IS correct for
> the low-exploitable class (S104's own north-star). **Selected lever: accept-done
> → pivot to `--release`; NO memory lever is built.**
>
> **Honest caveat for the `/sprint`+user gate.** F3 (the other residual fixture,
> ~8×) carries a **large residual-atomic-RC term** — the FINE `NONATOMIC_RC` probe
> recovers ~76% of its parallel wall. IF the goal were to make F3's *parallel* path
> competitive, the evidence selects **0526/0528 confinement precision**, not stack
> allocation. But F3-serial is already **8× faster than F3-parallel**, so there is
> no practical win to recover — the same accept-done conclusion holds. The lever
> choice is therefore not ambiguous for the *stated* target (F4-hard); the only
> judgement call is whether to fund F3-parallel competitiveness as a *new* goal.

---

## §1. Measurement conditions + doctrine-guard status

- **Walls counter-OFF** (G-wall-off): every graded wall ran with all stats/trace
  env unset; no `[INVALID: stats-on]` row.
- **Counts from a SEPARATE run** (G-separate): the `[RC_STATS]`/`[RC_SITE_STATS]`
  lines are read on distinct invocations, never off a timed run.
- **Idle out-of-band** (G-idle-oob): per-rep instantaneous `/proc/stat` busy-cores
  probe; **no cell tripped INVALID**. ⚠️ Caveat: `load1=3.41` at start (1-min avg,
  decaying from the harness's own build); the instantaneous busy-cores gate held,
  so walls are accepted as **order-of-magnitude** per §0.6. Directional findings
  (oracle *signs*, ceiling *shape*, counts) are robust; absolute wall deltas carry
  ±10–20%.
- **HW external** (G-hw-external): `strace -c` ran externally per graded cell.
- **I4 HITM = UNAVAILABLE** (scope-gap #3): `perf stat` is blocked on this VM
  (`perf_event_paranoid`). The (b) attribution rests on `NONATOMIC_RC` (I3) alone,
  exactly as the plan anticipated.
- **N2 descoped** (per Wave-0 `9b343c4`): (a)-on-parallel-branch attribution rides
  I1 syscall-share + F7 allocator-swap + F8 `STACK_SLOT_HITS`, not a per-branch
  alloc counter. N1 (`alloc_bytes`), N3 (`[RC_SITE_STATS]`), N4
  (`CRANELISP_NO_STACK_ALLOC`) all confirmed LIVE and used below.

---

## §2. Per-fixture attribution vectors (oracle-bounded direct-oracle net-recovery)

Net-recovery = `baseline − probe_wall` on the system build (a **positive** number
means the probe made it *faster* ⇒ that mechanism is a live cost). Reps=3.

### F4-hard — the primary residual → **unavailable-parallelism**
```
residual (parallel@10 − serial):   2.540 − 0.927 = +1.613s (2.74×)
  scheduler-spread     : ceiling 1.02× (I5); syscall sched-share 6.0% [futex=109 yield=6323]
  (a)-allocation       : +0.054s via NO_STACK_ALLOC(fine);  mimalloc ¬a=2.388 (recovers 0.042, ~2%)
                         [allocs=12,764,633  bytes=459,302,480]   ← huge alloc VOLUME, ~0 recovery
  residual-atomic-RC   : −0.031s via NONATOMIC_RC ; −0.043s via CAPTURE_BORROW  [rc_atomic=154]
  unavailable-parallel : speedup ceiling 1.02× @T=1, DEGRADES → 0.36× @T=10
  COARSE ceiling       : NO_OWNERSHIP net = −0.107s  (NEGATIVE — residual NOT memory-model-addressable)
  I (a/b coupling)     : −0.070s
```
**Every memory oracle is flat or NEGATIVE.** 459 MB of allocation, yet neither the
allocator swap (~2%) nor the stack oracle (+0.054s) nor the RC/borrow probes recover
it — because the alloc volume is the Sudoku copy-per-guess vec-COW, which stack-alloc
does not address (vecs decline stack when mutated; ADT-only path) and which mimalloc
does not speed (the cost is memcpy volume + parallel contention, not allocator-lock).
Adding cores makes it strictly *worse*. **Accept-done criterion MET** (ceiling ≤1.2×
AND coarse `NO_OWNERSHIP` recovery ≤0).

### F3-inverted-search — the second residual → **residual-atomic-RC (large), but serial already wins**
```
residual (parallel@10 − serial):   4.387 − 0.532 = +3.855s (8.25×)
  scheduler-spread     : ceiling 0.95× (I5); syscall sched-share 2.3% [futex=55 yield=4303]
  (a)-allocation       : +0.394s via NO_STACK_ALLOC ; mimalloc ¬a=3.528 (recovers 1.287, ~27%)
                         [allocs=4,202,607  bytes=151,261,208]
  residual-atomic-RC   : +3.655s via NONATOMIC_RC (~76% of baseline!) ; +0.269s via CAPTURE_BORROW  [rc_atomic=54]
  unavailable-parallel : speedup ceiling 0.95× (serial IS the ceiling); T=2 = 0.14×
  COARSE ceiling       : NO_OWNERSHIP net = −0.388s (NEGATIVE — confinement already helps; removing it hurts)
  I (a/b coupling)     : −0.269s
```
**`NONATOMIC_RC` recovers ~76%** ⇒ F3's parallel residual is dominated by
atomic-RC cache-line bouncing on the shared search grid. (⚠️ `NONATOMIC_RC` is
**unsound at >1 worker** — this is a *measurement ceiling* for the confinement-
precision lever, not a shippable cure.) A substantial (a) rides alongside (mimalloc
27%), coupled. The COARSE `NO_OWNERSHIP` being **negative** confirms the memory
model's *existing* confinement already helps F3; pushing it further (0526/0528)
would recover more of the atomic share **soundly**. BUT F3-serial (0.532s) beats
F3-parallel (4.387s) **8×** — so the honest disposition is still near-serial.

### F7-alloc — the (a)-ISOLATOR (constructed for this measurement) → confirms (a) is a SMALL term
```
residual (parallel@10 − serial):   0.696 − 0.487 = +0.209s (1.43×)
  (a)-allocation       : +0.016s via NO_STACK_ALLOC ; mimalloc ¬a=0.623 (recovers 0.069, ~10%)
                         [allocs=2,560,029  bytes=102,401,376]   rc_atomic=6  ← RC-LIGHT by design ✓
  residual-atomic-RC   : −0.004s via NONATOMIC_RC (flat — the isolation holds)
  unavailable-parallel : speedup ceiling 1.17× @T=2, DEGRADES → 0.70× @T=10
  COARSE ceiling       : NO_OWNERSHIP net = +0.038s
  I (a/b coupling)     : +0.055s ; syscall alloc-share 0.7%
```
**F7's REQUIRED property holds** (§5.1): 2.56 M allocs, `rc_atomic=6` (RC-light),
`futex/yield` low (scheduler-light) — and under the allocator swap the wall moves
only **~10%** (mimalloc) / **~2%** (stack). ⇒ **(a)-allocator-lock is a small,
un-confounded term post inc-I/II.** The stack-alloc lever's premise (that a large
(a) sits waiting) is *not* supported.

### F8-stack-witness — the gate-5 reachability sub-verdict (§5.2 / §4.1)
```
per-arm STACK_SLOT_HITS (backend-side, §8):
  f8_serial   (non-recursive phi-ADT) : stack_slot = 4 (serial-compile AND lenient)
              allocs stackON=1  vs  NO_STACK_ALLOC=4097   ⇒ stack recovers 4096 heap allocs ✓
  f8_parallel (recursive D&C phi-ADT) : stack_slot = 0 (serial-compile AND lenient)
              allocs stackON=0  vs  NO_STACK_ALLOC=0      ⇒ NOTHING to recover
```
**SUB-VERDICT (load-bearing).** The stack lever fires ONLY on the **non-recursive
in-frame** construction (serial arm, hits=4, the direct oracle recovers 4096 heap
allocs). On the **recursive / spark-bearing parallel-search** shape (the shape the
F3/F4 residual actually lives on) it fires **NEVER** — gate 3 (self-recursion)
declines the recursive bearer, and gate 5 additionally declines any lenient spark
relocation. So **even if (a) dominated, escape∧uniqueness stack allocation would
not reach the parallel residual** without a spark-frame-aware **and** recursion-aware
stack path — a scope increase well beyond increment I (§4.1 / SPRINT Rev-3).

---

## §3. Per-lever direct-oracle net-recovery table (the selection substrate, §4)

Each lever measured by its OWN toggle against the coupled baseline (never a
reconstructed additive split). Values are the F4-hard / F3 / F7 net-recovery.

| Candidate lever | Direct oracle | F4-hard | F3 | F7 | Verdict |
|---|---|---|---|---|---|
| **escape∧uniqueness stack alloc** | `NO_STACK_ALLOC` on parallel arm + F8 gate-5 | +0.054s (~2%) | +0.394s (~8%) | +0.016s (~2%) | **NOT selected** — flat on F4; F8 shows it never reaches the parallel/recursive shape (hits=0) |
| **0528 uniq-preservation / 0526 confinement projection-elision** | `NONATOMIC_RC` + `CAPTURE_BORROW` + N3 site dump | −0.031s / −0.043s | **+3.655s (~76%)** / +0.269s | −0.004s (flat) | **F3-selected IF parallel-F3 is a goal**; irrelevant to F4 |
| **0535 density-aware depth** | `SPARK_BUDGET`/depth; park-signature | sched 6.0%, ceiling 1.02× | sched 2.3%, ceiling 0.95× | sched 14.2%, ceiling 1.17× | **NOT selected** — sched-share small; not the dominant term anywhere |
| **accept-done → `--release`** | core-sweep ceiling + coarse `NO_OWNERSHIP` | **ceiling 1.02×, coarse −0.107s** | ceiling 0.95×, coarse −0.388s | ceiling 1.17×, coarse +0.038s | **SELECTED (F4-hard, primary)** — both accept-done conditions met |
| **allocator swap (mimalloc, the (a) axis)** | 2×2 ¬a | 2.430→2.388 (~2%) | 4.815→3.528 (~27%) | 0.692→0.623 (~10%) | (a)-lock is small/coupled; not a standalone lever in scope |

**Cross-cutting fact:** *all four fixtures show NEGATIVE parallel scaling* (speedup
ceiling ≤1.17×, degrading with cores). The parallel path is slower than serial and
gets worse with more cores — the low-exploitable-class signature. This is the
structural fact behind the accept-done verdict.

---

## §4. The decision-gate verdict (§6)

```
[S105-GATE — PRIMARY TARGET = F4-hard]
  DOMINANT TERM: unavailable-parallelism
    (every memory oracle flat/negative; coarse NO_OWNERSHIP negative; speedup
     ceiling 1.02× degrading to 0.36× @T=10)
  BUILD LEVER  : ACCEPT-DONE → pivot to `--release` (LLVM tier)
    — near-serial is correct for the low-exploitable class; no memory lever is
      built. Gate-5 rider: even the (a) lever would not reach the parallel path
      (F8 sub-verdict hits=0) — so it is doubly not selected.
  CONFIDENCE   : HIGH (four independent oracles agree; ceiling shape unambiguous)

[S105-GATE — SECONDARY FINDING = F3-inverted-search]
  DOMINANT TERM: residual-atomic-RC (NONATOMIC_RC recovers ~76%, sound-cure ceiling)
  BUILD LEVER  : 0526/0528 confinement precision — SELECTED ONLY IF the user funds
                 F3-*parallel* competitiveness as a NEW goal (not the stated F4
                 target). F3-serial already beats F3-parallel 8×, so there is no
                 practical win; default disposition is accept-done (run serial).
  CONFIDENCE   : the (b)-term MEASUREMENT is HIGH; the lever's WORTH is LOW
                 (unsound NONATOMIC ceiling; serial already dominates)
```

**Mapping to the SPRINT build-phase table:** dominant term **unavailable-parallelism**
→ **"Declare the parallel story settled; pivot to `--release` mainline."** No Wave-2
build. The T1-residue track proceeds independently.

### Judgement call surfaced for `/sprint`+user
The evidence is **unambiguous for the stated target** (F4-hard → accept-done). The
only open decision is a *scoping* one: **do we fund F3's parallel competitiveness?**
If yes, the evidence selects **0526/0528 confinement precision** (76% direct-oracle
ceiling), *not* stack allocation — and it must be a *sound* confinement improvement,
since the blanket `NONATOMIC_RC` that produced the 76% is unsound at >1 worker. Given
F3-serial already wins 8×, `/qa`'s recommendation is **accept-done** and record the
F3 atomic-RC finding as the durable RED guard (below) for a future sprint.

---

## §5. INVALID / UNAVAILABLE rows (honest gaps)

| Row | Status | Consequence |
|---|---|---|
| I4 HW HITM (`perf stat` remote-hitm / ctx-sw) | **UNAVAILABLE — host PMU** (`perf_event_paranoid`) | (b) attribution rests on `NONATOMIC_RC` (I3) alone — as scope-gap #3 anticipated. The 76% NONATOMIC recovery IS the (b) witness; HITM would have corroborated the cache-line mechanism but is not load-bearing for the verdict. |
| N2 per-branch alloc attribution | **DESCOPED** (Wave-0 `9b343c4`) | (a)-on-parallel-path rides I1 syscall-share (alloc 0.4–0.7% on F3/F4) + F7 swap (10%) + F8 `STACK_SLOT_HITS` (0). All three agree (a) is small/unreachable — the descope did not weaken the verdict. |
| `NONATOMIC_RC` net-recovery | **CEILING, not cure** | Unsound at >1 worker; the +3.655s (F3) is the confinement-precision *upper bound*, not a shippable delta. |
| Absolute walls | **order-of-magnitude** | `load1=3.41` at start (decaying); busy-cores gate held (no INVALID), but exact deltas ±10–20%. The verdict rests on oracle *signs* + ceiling *shape*, which are robust. |

---

## §6. Committed suite guards (perf-lane behavioural, §9.1)

`tests/s105_residual_attribution.rs` — 5 tests, polarity confirmed on the debug binary:

**GREEN (correctness + control):**
- `f7_alloc_parallel_serial_exit_match`, `f8_stack_witness_parallel_serial_exit_match`
  — the fixtures' durable parallel≡serial correctness record (§9.1 last para).
- `f8_serial_arm_stack_allocates` — positive control: stack-alloc CAN fire on the
  in-frame phi-ADT (`stack_slot=4`).

**RED (failing-not-ignored — the durable attribution records):**
- `f8_gate5_parallel_arm_stack_alloc_reachable` (§9.1.1) — the 0525 gate-5
  parallel-residual reachability gap; RED until a spark-frame-aware + recursion-aware
  stack path lands. `FIXME(/backend)`.
- `f3_shared_read_residual_atomic_rc_confined` (§9.1.2) — the F3 dominant term
  (shared-read parallel reduce emits `rc_atomic=18`; the N3 site dump attributes it
  to `build-grid class=Crossing`); RED until 0526/0528 confinement precision proves
  the shared reads Confined. `FIXME(/typecheck+/backend)`.

These add **2** to the suite's intentional failing-not-ignored count (22 → **24**);
they are known-defect/gap guards, not regressions. Owners + rationale recorded in
`tests/plan/ledger.md`.

---

## §7. What the phase confirmed vs the S104-close assertion

S104's close asserted the F3/F4 residual is "the alloc/RC-contention class." The
measure-first phase **refutes that for F4-hard** (alloc/RC oracles flat/negative;
it is unavailable-parallelism) and **partly confirms it for F3** (a real ~76%
atomic-RC term) — but shows even F3's cure is not worth building because serial
already wins 8×. The key structural discovery the assertion missed: **the compiler's
own inc-I/II optimizations (stack-alloc, reuse, confinement) already eliminate the
RC-light allocation class** (F7: 2.56 M allocs recover only ~10% under mimalloc;
scalar ADTs SROA to `allocs=0`), so the (a) term barely exists in isolation — and
the residual that remains is **negative parallel scaling**, not a memory term.
