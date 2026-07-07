;; f7_alloc.cl — Sprint 105 fixture F7: the (a)-allocation-isolating fixture.
;;
;; PURPOSE (plan §5.1): put the allocator term on its OWN axis — alloc-heavy,
;; RC-light, scheduler-light — so the mimalloc-vs-system allocator-swap oracle (I2)
;; and the 2×2 (a)-axis read the allocator contribution UN-confounded by atomic-RC
;; contention (b) or spark/scheduler spread.
;;
;; SHAPE: a SHALLOW coarse divide-and-conquer reduce (few strands, well above spawn
;; cost, well below the fib-explosion — scheduler-light), whose leaf builds MANY
;; fresh fixed-size Int vecs. Each vec is born, summed, and dropped within the leaf,
;; ESCAPING across the `one`→`sum-vec` call boundary just enough to force a genuine
;; heap allocation (defeating the increment-II in-place reuse that would eat a purely
;; frame-local build). Because each vec is single-owner (rc==1, never shared across
;; strands, never COW'd), the residual ATOMIC-RC traffic is ~0 (RC-light: I3 reads
;; rc_atomic≈6), which is exactly what isolates (a) from (b).
;;
;; REQUIRED property (plan §5.1): under the allocator swap (mimalloc vs system),
;; F7's wall must move MEASURABLY while its rc_atomic and futex share stay flat —
;; that separation is what makes it the (a)-isolator. If mimalloc does NOT move F7's
;; wall, (a)-allocator-lock is not a live term and the stack-alloc lever's premise
;; weakens (surfaced at the gate).
;;
;; Free-standing: bare primitives only, no stdlib, no prelude.
;; A/B: default = lenient/parallel; CRANELISP_NO_LENIENT=1 = serial. Same result.

(import [primitives [*]])

;; ── Harness-tunable size knobs ──
;; NB: F7 is deliberately SCHEDULER-LIGHT, so the harness copies it VERBATIM (it
;; does NOT run the s104 scale_synth blow-up that would drive `leaves` to 8192 and
;; make the tree spark-heavy). `leaves` sets the (shallow) strand count; `copies`
;; sets the per-leaf allocation volume — that is the (a) magnitude knob.
(defn leaves [] 64)     ;;S99-KNOB-LEAVES  shallow tree width (strand count)
(defn copies [] 40000)  ;;S99-KNOB-COPIES  fresh-vec allocations per leaf (the (a) volume)

(defn rmod [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))
(defn mid-of [lo hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

(defn build-vec [v i n]
  (if (eq-i64 i n) v (build-vec (vec-push v (add-i64 i 1)) (add-i64 i 1) n)))
(defn sum-vec [v i n acc]
  (if (eq-i64 i n) acc (sum-vec v (add-i64 i 1) n (add-i64 acc (vec-get v i)))))

;; One fresh 32-element vec: built, then it escapes into `sum-vec` across the call
;; boundary (a genuine heap allocation, single-owner ⇒ RC-light), summed, dropped.
(defn one [n] (sum-vec (build-vec [] 0 32) 0 32 0))

(defn leaf-work [lo k acc]
  (if (le-i64 k 0) acc (leaf-work lo (sub-i64 k 1) (add-i64 acc (one (add-i64 lo k))))))

;; Shallow coarse D&C — the two recursive halves are the independent apply-args of
;; add-i64 and auto-spark. Only `leaves` strands, so the spark/scheduler term is
;; negligible relative to the per-leaf allocation volume.
(defn reduce-tree [lo hi]
  (if (le-i64 (sub-i64 hi lo) 1)
    (leaf-work lo (copies) 0)
    (add-i64 (reduce-tree lo (mid-of lo hi)) (reduce-tree (mid-of lo hi) hi))))

(defn main [] (Pure (rmod (reduce-tree 0 (leaves)) 251)))
