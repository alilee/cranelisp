;; f1_machinery.cl — Sprint 99 Wave 0.3 fixture F1: pure machinery tax.
;;
;; A divide-and-conquer REDUCE over a Vec of heap-allocated ADT `Cell`s.
;; Every internal node is `(add-i64 (recur left) (recur right))` whose two
;; independent recursive apply-args auto-spark (lenient eval, examples/30).
;; The leaf work is DELIBERATELY TRIVIAL — it only *reads* cells from the
;; shared grid (`vec-get` + `match`), doing NO copy and NO allocation.
;;
;; Purpose: isolate the pure spark/IVar/rayon-pool MACHINERY TAX. Because the
;; tree shape (and thus the spark count) is IDENTICAL to F2 (f2_contention.cl)
;; but the per-leaf memory work is near-zero, the subtraction
;;   (F2 − F1) at N-workers  =  the copy/alloc/atomic-RC CONTENTION term.
;; F1 alone (1-worker − serial) = machinery with zero cross-core contention.
;;
;; "branching-factor-1 / naked-singles" reading: every leaf commits the single
;; forced value with no speculation and no real parallel benefit (work too
;; cheap to overlap) — the tree still exercises the full spark machinery.
;;
;; Free-standing: bare primitives only, no stdlib, no prelude.
;; A/B: default = lenient/parallel; CRANELISP_NO_LENIENT=1 = serial. Same result.

(import [primitives [*]])

(deftype Cell (Given [:Int given-value]) (Solved [:Int solved-value]))

(defn cell-value [c] (match c [(Given v) v  (Solved v) v]))

;; ── Harness-tunable size knobs (rewritten by the measurement harness) ──
(defn leaves [] 64)   ;;S99-KNOB-LEAVES  tree width (leaf count = parallelism)
(defn copies [] 4)    ;;S99-KNOB-COPIES  work repetitions per leaf

(defn rem-i64 [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))
(defn mid-of [lo hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

;; Build the shared grid: a Vec of N heap-allocated Cell ADTs.
(defn build-grid [v i n]
  (if (eq-i64 i n) v
    (build-grid (vec-push v (Given (add-i64 (rem-i64 i 9) 1))) (add-i64 i 1) n)))

;; F1 leaf work: read one shared cell K times. No copy, no alloc — machinery only.
(defn read-work [g i k acc]
  (if (le-i64 k 0) acc
    (read-work g i (sub-i64 k 1)
      (add-i64 acc (cell-value (vec-get g i))))))

(defn leaf-work [g lo]
  (read-work g (rem-i64 lo (vec-len g)) (copies) 0))

;; Divide-and-conquer reduce: the two recursive halves are the independent
;; apply-args of add-i64 and auto-spark. All branch results are consumed.
(defn reduce-tree [g lo hi]
  (if (le-i64 (sub-i64 hi lo) 1)
    (leaf-work g lo)
    (add-i64 (reduce-tree g lo (mid-of lo hi))
             (reduce-tree g (mid-of lo hi) hi))))

(defn main []
  (let [g (build-grid [] 0 81)]
    (Pure (rem-i64 (reduce-tree g 0 (leaves)) 251))))
