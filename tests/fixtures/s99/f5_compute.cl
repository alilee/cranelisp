;; f5_compute.cl — Sprint 104 Stage-0 fixture F5: the Regime-A positive witness.
;;
;; A ~nproc-leaf divide-and-conquer over HEAVY PURE COMPUTE (naive recursive
;; `fib`), with NO heap allocation in the leaf and NO shared-cell contention.
;; This is the clean "populate the cores, each runs an efficient sequential
;; path, and beat serial by ≈T" witness the utilization thesis needs to be
;; *validated* (F4-hard can only falsify the over-sparking side).
;;
;; Shape (mirrors F1's `reduce-tree` D&C exactly, but the leaf is compute-heavy
;; instead of a trivial read): the two recursive halves of `reduce-tree` are the
;; independent apply-args of `add-i64` and auto-spark (lenient eval). Each of the
;; ~nproc coarse strands runs a naive `fib` — tens of ms of pure sequential
;; integer compute, well above the ~13µs spawn cost — so a handful of coarse
;; strands each running forward serially must beat serial by ≈T once M-dynamic
;; (Wave 3) dispatches ~2/core coarse strands and then inlines the rest.
;;
;; Why F1 is inadequate and F5 is needed: F1's leaves only *read* shared cells
;; (near-zero per-leaf work), so its coarse-parallel win is startup/JIT-dominated
;; and not decisively measurable above noise (S102 had to move F1 timing to
;; report-only <60ms). F5's per-leaf compute is heavy and pure, decoupling the
;; Regime-A win from allocation/contention entirely.
;;
;; Correctness guard: pure branches → the parallel (auto-sparked) reduce returns
;; the identical sum a serial (CRANELISP_NO_LENIENT=1) reduce does, so the exit
;; code (a checksum of the reduced value) MUST be identical under default and
;; CRANELISP_NO_LENIENT=1. That is the committed parallel≡serial correctness
;; guard for the compute D&C path.
;;
;; Free-standing: bare primitives only, no stdlib, no prelude.
;; A/B: default = lenient/parallel; CRANELISP_NO_LENIENT=1 = serial. Same result.

(import [primitives [*]])

;; ── Harness-tunable size knob (leaf count = coarse parallelism) ──
;; NOTE: F5 is generated UNSCALED by the harness — its fib depth must stay small
;; (heavy but bounded), so it does NOT reuse the F1/F2/F3 COPIES=256 synth knob.
(defn leaves [] 64)   ;;S99-KNOB-LEAVES  tree width (leaf count = # coarse strands)

(defn rem-i64 [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))
(defn mid-of [lo hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

;; Naive recursive fib — heavy PURE compute (no alloc, no shared state). Its own
;; two recursive apply-args also auto-spark under the syntactic filter (the
;; fib-explosion shape); the utilization model's job is to let the coarse
;; `reduce-tree` strands dispatch while these inline serially once the pool is
;; busy (M-dynamic, Wave 3).
(defn fib [n]
  (if (lt-i64 n 2) n
    (add-i64 (fib (sub-i64 n 1)) (fib (sub-i64 n 2)))))

;; Leaf: tens of ms of sequential compute. Slight per-leaf variation (fib 31/32)
;; keeps the leaves from folding to one CSE'd constant.
(defn leaf-work [lo] (fib (add-i64 32 (rem-i64 lo 2))))

;; Divide-and-conquer reduce: the two recursive halves are the independent
;; apply-args of add-i64 and auto-spark. All branch results are consumed.
(defn reduce-tree [lo hi]
  (if (le-i64 (sub-i64 hi lo) 1)
    (leaf-work lo)
    (add-i64 (reduce-tree lo (mid-of lo hi))
             (reduce-tree (mid-of lo hi) hi))))

(defn main []
  (Pure (rem-i64 (reduce-tree 0 (leaves)) 251)))
