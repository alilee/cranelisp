;; f6_parwin.cl — Sprint 104 Wave-2c fixture F6: the HEAVY Regime-A speedup witness.
;;
;; Purpose: a divide-and-conquer over ~nproc genuinely-independent, HEAVY, pure
;; integer-compute leaves — sized so that dispatching the coarse strands across
;; the cores must beat serial by ≈N× on an N-core machine. This is the positive
;; "cores doing useful work, faster" witness the utilization thesis needs.
;;
;; Why F5 (`f5_compute.cl`) was inadequate. F5's leaves are naive `fib 32/33` —
;; only ~a few ms each, so the whole D&C runs in ~0.7s serial and is DOMINATED by
;; JIT/startup + IVar-force overhead. Parallelizing it only *ties* serial: the
;; per-leaf work is below the threshold where a filled core recovers its share of
;; the wall. F5 can validate parallel≡serial *correctness*, but it cannot exhibit
;; a *speedup*, so it cannot witness the thesis's positive claim (Regime A: cores
;; busy AND wall → serial/N). F6 fixes exactly that: each leaf is ~100–150ms of
;; pure sequential integer compute (well above the ~13µs spawn cost and far above
;; startup noise), and the leaves are BALANCED, so a clean ~N× win is the
;; expected outcome once the coarse strands land on distinct cores.
;;
;; Shape (mirrors F1/F5's `reduce-tree` D&C):
;;   • 16 leaves → a perfectly balanced binary D&C tree of depth 4. The two
;;     recursive halves of `reduce-tree` are the independent apply-args of
;;     `add-i64` and auto-spark under lenient eval. reduce-tree is NON-tail
;;     recursive at every level (args of add-i64), so M-static's `scc ∧ ¬tail`
;;     signal ADMITS the coarse forks all the way down — the utilization
;;     mechanism can fill up to 16 coarse strands across the cores.
;;   • Each leaf is `spin` — a TAIL-recursive LCG integer loop (40M iterations).
;;     Being tail-recursive, M-static DECLINES to spark inside it (tail calls are
;;     not admitted), so the leaf is a clean sequential compute unit with NO
;;     internal sparks and NO heap allocation / RC traffic. The ONLY sparking is
;;     at the coarse reduce-tree level. This deliberately avoids the F2/F3
;;     allocation-contention class — the sole question F6 poses is "does filling
;;     cores with independent pure compute beat serial?".
;;   • Leaves are BALANCED: every leaf runs the SAME iteration count (40M); only
;;     the LCG seed varies by leaf index, so results differ (no CSE fold to one
;;     constant) while per-leaf wall is identical. Balanced leaves ⇒ parallel
;;     wall ≈ serial/N (a clean N× win), unlike F4/F5's unbalanced/light shapes.
;;
;; Correctness guard (exit-code checksum, like F4/F5). All branches are pure and
;; combined with commutative `add-i64`, so the reduced value is deterministic and
;; order-independent: the auto-sparked (parallel) reduce returns the identical
;; sum a serial (CRANELISP_NO_LENIENT=1) reduce does. The exit code is a checksum
;; (reduced value mod 251) and MUST be identical under default and
;; CRANELISP_NO_LENIENT=1 — the committed parallel≡serial guard for the heavy
;; compute D&C path.
;;
;; Free-standing: bare primitives only, no stdlib, no prelude.
;; A/B: default = lenient/parallel; CRANELISP_NO_LENIENT=1 = serial. Same result.

(import [primitives [*]])

;; ── Size knobs ──
;; leaves = coarse parallelism (# independent heavy strands). 16 = a full
;; balanced binary tree (depth 4); on a 10-core host the utilization mechanism
;; can keep every core busy (2 waves of ~8), so parallel wall ≈ serial/10-ish.
(defn leaves [] 16)              ;;S99-KNOB-LEAVES  tree width (leaf count)
;; iters = per-leaf compute weight. 40M LCG steps ≈ ~120ms sequential on this
;; host (~3ns/step), decisively above the ~13µs spawn cost and startup noise.
(defn iters [] 40000000)         ;;S99-KNOB-ITERS   per-leaf loop length

(defn rem-i64 [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))
(defn mid-of [lo hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

;; Heavy leaf: a TAIL-recursive LCG integer loop. Pure (no alloc, no shared
;; state), tail-recursive (so M-static declines to spark inside it), deterministic
;; for a given seed. This is the ~120ms sequential compute unit.
(defn spin [i n acc]
  (if (ge-i64 i n)
    acc
    (spin (add-i64 i 1)
          n
          (rem-i64 (add-i64 (mul-i64 acc 1103515245) 12345) 2147483647))))

;; Leaf: identical iteration count for every leaf (balanced), seed varies by leaf
;; index so leaves don't fold to a single CSE'd constant. Result mod 251 keeps the
;; per-leaf contribution bounded; the D&C sum is then taken mod 251 for the exit.
(defn leaf-work [lo] (rem-i64 (spin 0 (iters) (add-i64 7 lo)) 251))

;; Divide-and-conquer reduce: the two recursive halves are the independent
;; apply-args of add-i64 and auto-spark. NON-tail recursive at every level, so
;; M-static admits the coarse forks; balanced halves ⇒ balanced strands.
(defn reduce-tree [lo hi]
  (if (le-i64 (sub-i64 hi lo) 1)
    (leaf-work lo)
    (add-i64 (reduce-tree lo (mid-of lo hi))
             (reduce-tree (mid-of lo hi) hi))))

(defn main []
  (Pure (rem-i64 (reduce-tree 0 (leaves)) 251)))
