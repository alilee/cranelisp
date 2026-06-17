;; 30-parallel-map-reduce.cl -- Map-reduce over a Vec that parallelises itself
;;
;; This is the headline payoff of lenient evaluation (first introduced in
;; 28-parallel.cl): you write an ORDINARY map-reduce over a Vec in terms of
;; `let`, and the compiler automatically runs the independent halves on a
;; thread pool. No `par-let`, no `spawn`, no threads in the source — just
;; pure code and `let`.
;;
;; The idea: instead of folding the Vec left-to-right (which is inherently
;; sequential), we express the reduction as DIVIDE-AND-CONQUER over an index
;; range [lo, hi). Each call splits the range in half, reduces each half
;; recursively, then combines the two results. Because the two halves are
;; INDEPENDENT pure computations, the compiler sparks them in parallel.
;;
;; Measured wall-clock (8 leaves, each a fib(38) ~= 39,088,169):
;;
;;     cargo run -- --run examples/30-parallel-map-reduce.cl
;;         lenient ON  : ~0.30 s   <- two halves run in parallel
;;     CRANELISP_NO_LENIENT=1 cargo run -- --run examples/30-parallel-map-reduce.cl
;;         lenient OFF : ~1.07 s   <- halves run sequentially
;;
;;     => ~3.6x speedup, same result, zero source changes. A/B it yourself
;;        with the CRANELISP_NO_LENIENT=1 env var.
;;
;; ---------------------------------------------------------------------------
;; THE SPARKABILITY RULE (the one subtle thing to get right)
;;
;; A `let` binding is sparked onto the thread pool only if it is INDEPENDENT
;; of every EARLIER binding in the SAME `let` block — i.e. its right-hand
;; side references no name bound above it in that block. (Cheap builtins like
;; + - * / and the comparisons are never sparked; only real work is.)
;;
;; So to make the two halves spark, BOTH halves must be binding right-hand
;; sides, and neither may depend on the other. The natural temptation is to
;; compute the split point ONCE and bind it first:
;;
;;     (let [mid   (split lo hi)         ;; <-- DON'T: now `mid` is an
;;           left  (reduce-range v lo mid)    ;;     earlier binding, so both
;;           right (reduce-range v mid hi)]   ;;     halves DEPEND on it and
;;       (combine left right))                ;;     CANNOT be sparked!
;;
;; That keeps `left` and `right` sequential. The fix is to INLINE the split
;; point into each half so the only thing each half closes over is the
;; function's PARAMETERS (`v`, `lo`, `hi`) -- parameters are not same-block
;; `let` bindings, so referencing them in both halves is fine:
;;
;;     (let [left  (reduce-range v lo (split lo hi))
;;           right (reduce-range v (split lo hi) hi)]
;;       (combine left right))            ;; <-- left and right are now
;;                                        ;;     independent => both spark.
;;
;; Recomputing `split` twice is cheap (it's just integer arithmetic); the
;; cost we care about is the two recursive halves, and those now run in
;; parallel.
;; ---------------------------------------------------------------------------

;; --- The per-element "map": an expensive pure computation ------------------
;; fib is deliberately costly so that each leaf is real work worth sparking.
(defn fib [:Int n]
  (if (lt-i64 n 2)
      n
      (add-i64 (fib (sub-i64 n 1))
               (fib (sub-i64 n 2)))))

;; --- The split point: midpoint of the half-open range [lo, hi) ------------
;; Pure integer arithmetic. Cheap, so it is never sparked -- and because it
;; is cheap, we can safely recompute it in each half (see the rule above)
;; rather than binding it once and serialising the halves.
(defn mid-of [:Int lo :Int hi]
  (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

;; --- The parallel map-reduce ----------------------------------------------
;; Reduce v[lo..hi) by mapping `fib` over each element and summing.
;;
;;   - Leaf case (1 element): map -> fib of that single element.
;;   - Otherwise: split the range, reduce each half, add the two results.
;;
;; v, lo and hi are PARAMETERS, not same-block `let` bindings, so both
;; halves may freely reference them. The two halves are the only `let`
;; bindings here and neither depends on the other => the compiler sparks
;; `left` and `right` in parallel.
(defn par-map-reduce [v :Int lo :Int hi]
  (if (le-i64 (sub-i64 hi lo) 1)
      (fib (vec-get v lo))                                  ;; leaf: map one element
      (let [left  (par-map-reduce v lo (mid-of lo hi))      ;; sparkable: indep half
            right (par-map-reduce v (mid-of lo hi) hi)]     ;; sparkable: indep half
        (add-i64 left right))))                             ;; combine (barrier here)

;; --- Driver ---------------------------------------------------------------
;; Map fib over eight 38s and sum them: 8 * fib(38) = 8 * 39,088,169
;; = 312,705,352. Scaled down by 1,000,000 to a small exit code (312).
;; The result is identical with lenient eval on or off -- parallelism is
;; semantically transparent because the code is pure.
(defn main []
  (let [v [38 38 38 38 38 38 38 38]]
    (Pure (div-i64 (par-map-reduce v 0 (vec-len v)) 1000000))))
