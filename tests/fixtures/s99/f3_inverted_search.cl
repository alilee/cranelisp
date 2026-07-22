;; f3_inverted_search.cl — Sprint 99 Wave 0.3 fixture F3: best-case parallel upside.
;;
;; A first-success divide-and-conquer SEARCH over the same shared-grid copy work
;; as F2, but combined with `first-success` (identity `Miss`) and arranged so the
;; ONLY winning leaf is the LAST one a left-to-right serial walk would reach.
;; Every leaf does the identical heavy copy work (so branches are equal-cost),
;; and both the Hit and Miss arms embed that work (so it is never dead-code
;; eliminated on the losing branches).
;;
;; Purpose: measure BEST-CASE PARALLEL UPSIDE. A serial (lenient-OFF or 1-worker)
;; walk does every branch one after another → wall ≈ sum of all branch costs. An
;; N-worker walk overlaps the independent siblings → wall ≈ longest branch. So
;;   (serial wall / N-worker wall) on F3  =  the realized parallel speedup,
;; bounded by cores and eroded by contention.
;;
;; KEY (falsification) NOTE: Cranelisp's speculative eval FORCES BOTH args of
;; `first-success` before the call — there is NO early exit. So the answer's
;; LOCATION does not change total work: serial-lenient and parallel-lenient both
;; evaluate ALL branches. "serial luck" (a real early-exit backtracker stopping
;; at the first success) is therefore NOT available in this model and cannot be
;; a term in the lenient-vs-serial ratio. F3 exists to make that visible and to
;; measure the pure overlap upside on equal-cost independent work.
;;
;; Free-standing: bare primitives only, no stdlib, no prelude.

(import [primitives [*]])

(deftype Cell (Given [:Int given-value]) (Solved [:Int solved-value]))
(deftype Found (Hit [:Int v]) (Miss [:Int w]))

(defn cell-value [c] (match c [(Given v) v  (Solved v) v]))

;; The associative reduce combiner: first success wins, else the second.
(defn first-success [a b]
  (match a [(Hit v) (Hit v)  (Miss _) b]))

;; ── Harness-tunable size knobs (rewritten by the measurement harness) ──
(defn leaves [] 64)   ;;S99-KNOB-LEAVES  tree width (leaf count = parallelism)
(defn copies [] 4)    ;;S99-KNOB-COPIES  shared-grid copies per leaf

(defn rem-i64 [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))
(defn mid-of [lo hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

(defn build-grid [v i n]
  (if (eq-i64 i n) v
    (build-grid (vec-push v (Given (add-i64 (rem-i64 i 9) 1))) (add-i64 i 1) n)))

;; Identical heavy shared-copy work to F2's copy-work.
(defn copy-work [g i k acc]
  (if (le-i64 k 0) acc
    (let [g2 (vec-set g i (Solved k))]
      (copy-work g i (sub-i64 k 1)
        (add-i64 acc (cell-value (vec-get g2 i)))))))

;; Leaf: do the heavy work, then WIN iff this is the last leaf. Both arms use
;; the work value `w` so the losing branches' work is not elided.
(defn search-leaf [g lo]
  (let [w (copy-work g (rem-i64 lo (vec-len g)) (copies) 0)]
    (if (eq-i64 lo (sub-i64 (leaves) 1))
      (Hit (add-i64 lo w))
      (Miss w))))

;; First-success D&C: the two recursive halves are the independent apply-args of
;; first-success and auto-spark.
(defn search-tree [g lo hi]
  (if (le-i64 (sub-i64 hi lo) 1)
    (search-leaf g lo)
    (first-success (search-tree g lo (mid-of lo hi))
                   (search-tree g (mid-of lo hi) hi))))

(defn main []
  (let [g (build-grid [] 0 81)]
    (match (search-tree g 0 (leaves))
      [(Hit v)  (Pure (rem-i64 v 251))
       (Miss _) (Pure 0)])))
