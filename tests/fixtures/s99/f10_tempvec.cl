;; f10_tempvec.cl — Sprint 105 Phase-5 Wave-1b (acid test) fixture F10.
;;
;; PURPOSE (acid §(ii) opportunity ceiling): a realistic SERIAL temp-aggregate.
;; Builds a NON-SCALAR unique non-escaping aggregate (a fresh Int Vec), computes
;; over it (sum), and discards it within one frame. This is the delta's REAL
;; target — the "escape∧uniqueness stack allocation" hypothesis's intended class,
;; which increment-II reuse tokens do NOT stack-allocate today (they remove the
;; COPY when unique but still malloc/free the buffer).
;;
;; As-built, this NEVER stack-allocs: a Vec's payload is a heap buffer (non-scalar,
;; dynamically-sized) ⇒ it fails gate 2 (all-scalar-payload) regardless of shape.
;; So the delta isn't built for it — this fixture measures the OPPORTUNITY CEILING
;; the delta could recover: alloc_bytes / allocs (N1), the N3 Confined/Crossing
;; classification (delta-eligible ⇔ Confined+unique), the mimalloc-vs-system wall
;; delta, and the strace brk/mmap share.
;;
;; Two arms (sliced by the harness on region markers), matching the §(i) reach split:
;;   SL   — construction in a NON-recursive helper `one`, loop-driven for volume.
;;          Delta-recoverable IF the delta lifted gate 2 (the helper frame is
;;          non-recursive ⇒ gate 3 clear).
;;   LOOP — construction INLINE in the tail loop body. NOT delta-recoverable: gate 3
;;          declines it (the delta lifts gate 2, not gate 3), same as f9_loop.
;; Identical alloc volume; the arms differ only in delta-eligibility.
;;
;; Free-standing: bare primitives only, no stdlib, no prelude.
;; A/B: default = lenient; CRANELISP_NO_LENIENT=1 = serial. Same result.

(import [primitives [*]])

(defn iters [] 2000000)   ;;S99-KNOB-ITERS  temp-vec construction count (the (a) volume)
(defn width [] 32)        ;;S99-KNOB-WIDTH  elements per temp vec

(defn rmod [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))

(defn build-vec [v i n]
  (if (eq-i64 i n) v (build-vec (vec-push v (add-i64 i 1)) (add-i64 i 1) n)))
(defn sum-vec [v i n acc]
  (if (eq-i64 i n) acc (sum-vec v (add-i64 i 1) n (add-i64 acc (vec-get v i)))))

;;S105-F10-SL-BEGIN
;; SL arm: one fresh temp vec built + summed + discarded in a NON-recursive helper.
;; The vec escapes only across the `build-vec`→`sum-vec` boundary (single-owner,
;; Confined), then dies. gate 3 is clear for `one`.
(defn one [n] (sum-vec (build-vec [] 0 (width)) 0 (width) 0))

(defn drive-sl [k acc]
  (if (le-i64 k 0) acc (drive-sl (sub-i64 k 1) (add-i64 acc (one k)))))
;;S105-F10-SL-END

;;S105-F10-LOOP-BEGIN
;; LOOP arm: the SAME temp vec built + summed + discarded INLINE in the tail loop
;; body. `drive-loop` contains a self-call ⇒ gate 3 (would) decline even under the
;; delta. Same alloc volume, but not delta-recoverable.
(defn drive-loop [k acc]
  (if (le-i64 k 0) acc
    (let [v (build-vec [] 0 (width))
          s (sum-vec v 0 (width) 0)]
      (drive-loop (sub-i64 k 1) (add-i64 acc s)))))
;;S105-F10-LOOP-END

;;S105-F10-MAIN-BOTH
(defn main []
  (Pure (rmod (add-i64 (drive-sl (iters) 0) (drive-loop (iters) 0)) 251)))
;;S105-F10-MAIN-BOTH-END
;;S105-F10-MAIN-SL   (defn main [] (Pure (rmod (drive-sl (iters) 0) 251)))
;;S105-F10-MAIN-LOOP   (defn main [] (Pure (rmod (drive-loop (iters) 0) 251)))
