;; f2_contention.cl — Sprint 99 Wave 0.3 fixture F2: clean contention probe.
;;
;; IDENTICAL divide-and-conquer REDUCE tree to F1 (f1_machinery.cl) — same
;; shape, same spark count, same "all results consumed" (no speculative waste
;; on either side). The ONLY difference is the leaf work: each leaf performs
;; the characteristic Sudoku copy-per-guess — `vec-set` on the SHARED grid,
;; which copy-on-write COPIES the whole N-cell Vec (rc>1) and allocates a fresh
;; heap `Cell`, incrementing the refcount of every retained cell. Under N
;; workers, all leaves copy the SAME shared grid concurrently, so g's Vec-header
;; refcount and every cell's refcount bounce across cores.
;;
;; Purpose: the CLEAN CONTENTION probe and the honest "slight discount per core"
;; witness. Both serial and parallel do identical total work → any N-worker
;; slowdown over 1-worker is contention (allocator-lock + atomic-RC bouncing).
;;   (F2 − F1) at N-workers  =  the contention term, isolated.
;;   user-vs-sys split of that delta  =  (b) atomic-RC (user) vs (a) alloc (sys).
;;
;; This directly exercises the "~N RC bumps + fresh cells per copy per node"
;; volume claim — CRANELISP_RC_STATS reports it.
;;
;; Free-standing: bare primitives only, no stdlib, no prelude.
;; A/B: default = lenient/parallel; CRANELISP_NO_LENIENT=1 = serial. Same result.

(import [primitives [*]])

(deftype Cell (Given [:Int value]) (Solved [:Int value]))

(defn cell-value [c] (match c [(Given v) v  (Solved v) v]))

;; ── Harness-tunable size knobs (rewritten by the measurement harness) ──
(defn leaves [] 64)   ;;S99-KNOB-LEAVES  tree width (leaf count = parallelism)
(defn copies [] 4)    ;;S99-KNOB-COPIES  shared-grid copies per leaf

(defn rem-i64 [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))
(defn mid-of [lo hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

(defn build-grid [v i n]
  (if (eq-i64 i n) v
    (build-grid (vec-push v (Given (add-i64 (rem-i64 i 9) 1))) (add-i64 i 1) n)))

;; F2 leaf work: copy the SHARED grid K times. Each `(vec-set g i ...)` copies
;; the whole N-cell Vec (g is shared, rc>1) + allocates a Cell + bumps every
;; retained cell's refcount. Note we always copy the ORIGINAL shared `g` (never
;; the freshly-owned `g2`), so every iteration is a real shared-copy, not a
;; cheap COW-in-place mutation.
(defn copy-work [g i k acc]
  (if (le-i64 k 0) acc
    (let [g2 (vec-set g i (Solved k))]
      (copy-work g i (sub-i64 k 1)
        (add-i64 acc (cell-value (vec-get g2 i)))))))

(defn leaf-work [g lo]
  (copy-work g (rem-i64 lo (vec-len g)) (copies) 0))

;; Same D&C reduce as F1 — independent apply-arg halves auto-spark.
(defn reduce-tree [g lo hi]
  (if (le-i64 (sub-i64 hi lo) 1)
    (leaf-work g lo)
    (add-i64 (reduce-tree g lo (mid-of lo hi))
             (reduce-tree g (mid-of lo hi) hi))))

(defn main []
  (let [g (build-grid [] 0 81)]
    (Pure (rem-i64 (reduce-tree g 0 (leaves)) 251))))
