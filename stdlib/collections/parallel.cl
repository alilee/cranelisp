;; collections/parallel.cl — Parallel map / reduce / map-reduce over a Vec
;;
;; `par-map`, `par-reduce`, and `par-map-reduce` are ORDINARY library
;; functions — NOT compiler primitives and NOT new syntax. They add zero
;; language surface (arch ruling, design/arch/effect-concurrency.md §7,
;; FIXME 0424). What makes them parallel is the inferred lenient-evaluation
;; sparking substrate (design/backend/lenient-eval.md): independent,
;; individually-expensive work sparks automatically onto the thread pool.
;; A reader can open this file and see ordinary divide-and-conquer recursion
;; over half-open index ranges — there is nothing magic.
;;
;; HOW THEY SPARK (the divide-and-conquer shape, lenient-eval.md §2.1):
;;   Each function splits [lo, hi) at the midpoint into two halves and recurses
;;   on each. The two recursive calls are bound to INDEPENDENT `let` bindings
;;   (`left` / `right`) — neither references the other, and the midpoint is
;;   recomputed inline (via `par-mid`) rather than shared as a binding, so the
;;   independence check (§2.1) admits BOTH halves and they spark in parallel.
;;   This is the ENTIRE source of parallelism: two independent sparkable
;;   bindings per node.
;;   The combine is the `let` BODY (`(vec-concat left right)` / `(f left right)`
;;   / `(redf left right)`), NOT a third binding. It runs AFTER the let barrier
;;   has forced both halves, so it is plain post-barrier code — never sparked.
;;   This is deliberate (review S94 finding I4): a combine bound as a separate
;;   `let` binding would be an INERT §2.6.2 dependent spark — it blocks
;;   immediately on forcing both halves with zero independent sub-work, adding
;;   no concurrency, while consuming a third create-gate permit per node (n=3
;;   reserved vs 2) that starves the productive `left`/`right` sparks. Keeping
;;   the combine in the body extracts the same parallelism with two permits.
;;   The shared ≥2-candidate gate, the cost heuristic, and the global
;;   in-flight-spark create-gate (which keeps deep recursion from exploding and
;;   preserves the never-slower-than-serial floor) all carry over unchanged.
;;
;; CORRECTNESS IS THE CONTRACT; PARALLELISM IS A PERFORMANCE PROPERTY.
;;   These produce results IDENTICAL to their sequential counterparts —
;;   `par-map`        == `vec-map`,
;;   `par-reduce`     == `vec-reduce`     (for an ASSOCIATIVE `f` with `init`
;;                                         its identity),
;;   `par-map-reduce` == `vec-reduce ∘ vec-map`.
;;   Because the language is pure, evaluation order does not change results;
;;   CRANELISP_NO_LENIENT=1 / CRANELISP_SPARK_BUDGET=0 force everything serial
;;   and produce the same answers.
;;
;; Spec: 12-runtime.md §12.4.3 (lenient evaluation); plan-stdlib.md §3.3

(import [prelude []])
(import [primitives [Int vec-len vec-get add-i64 sub-i64 div-i64 le-i64 lt-i64]])
(import [collections.vec [vec-concat]])

;; Midpoint of the half-open range [lo, hi). Pure integer arithmetic — cheap,
;; so never sparked, and safely RECOMPUTED in each half (kept OUT of a shared
;; `let` binding on purpose: a shared cheap binding would make both halves
;; "depend on an earlier non-sparked binding" and the §2.1 independence check
;; would then refuse to spark them).
(defn- par-mid "Midpoint of the half-open range [lo, hi)"
  [:Int lo :Int hi] :Int
  (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

;; ── par-map ──────────────────────────────────────────────────────────
;; Map `f` over every element of `v`, returning a new Vec — every per-element
;; application running in parallel. Result is element-for-element identical to
;; `(vec-map f v)`, order preserved (the left half is always concatenated
;; before the right).

(defn par-map "Parallel map: apply f to each element of v (== vec-map, in parallel)"
  [f v]
  (par-map-range f v 0 (vec-len v)))

(defn- par-map-range "Divide-and-conquer par-map over the half-open range [lo, hi)"
  [f v :Int lo :Int hi]
  (if (le-i64 (sub-i64 hi lo) 1)
      (if (lt-i64 lo hi) [(f (vec-get v lo))] [])   ;; leaf: 1 element, or empty
      (let [left   (par-map-range f v lo (par-mid lo hi))   ;; independent spark
            right  (par-map-range f v (par-mid lo hi) hi)]  ;; independent spark
        (vec-concat left right))))                          ;; combine = let body (post-barrier, no spark)

;; ── par-reduce ───────────────────────────────────────────────────────
;; Reduce `v` with the ASSOCIATIVE binary function `f`, divide-and-conquer.
;; `init` must be the identity of `f` (it is the result for an empty Vec).
;; Under that contract the result is identical to the sequential left fold
;; `(vec-reduce f init v)`. NOTE: unlike `vec-reduce`, `f` here combines two
;; PARTIAL RESULTS of the same type — `(Fn [a a] a)` — and must be associative;
;; a non-associative `f` (e.g. subtraction) is a misuse, not supported.

(defn par-reduce "Parallel reduce with an ASSOCIATIVE f and identity init (== vec-reduce)"
  [f init v]
  (par-reduce-range f init v 0 (vec-len v)))

(defn- par-reduce-range "Divide-and-conquer par-reduce over the half-open range [lo, hi)"
  [f init v :Int lo :Int hi]
  (if (le-i64 (sub-i64 hi lo) 1)
      (if (lt-i64 lo hi) (vec-get v lo) init)   ;; leaf: 1 element, or identity
      (let [left   (par-reduce-range f init v lo (par-mid lo hi))    ;; independent spark
            right  (par-reduce-range f init v (par-mid lo hi) hi)]   ;; independent spark
        (f left right))))                                           ;; combine = let body (post-barrier, no spark)

;; ── par-map-reduce ───────────────────────────────────────────────────
;; Fused parallel map-then-reduce: apply `mapf` to each element, then combine
;; with the ASSOCIATIVE `redf` (identity `init`). Identical to
;; `(vec-reduce redf init (vec-map mapf v))`, but fused (no intermediate Vec)
;; and parallel. This is the canonical divide-and-conquer map-reduce.

(defn par-map-reduce "Parallel map-then-reduce: map mapf, combine with associative redf"
  [mapf redf init v]
  (par-map-reduce-range mapf redf init v 0 (vec-len v)))

(defn- par-map-reduce-range "Divide-and-conquer par-map-reduce over [lo, hi)"
  [mapf redf init v :Int lo :Int hi]
  (if (le-i64 (sub-i64 hi lo) 1)
      (if (lt-i64 lo hi) (mapf (vec-get v lo)) init)   ;; leaf: mapf one element, or identity
      (let [left   (par-map-reduce-range mapf redf init v lo (par-mid lo hi))    ;; independent spark
            right  (par-map-reduce-range mapf redf init v (par-mid lo hi) hi)]   ;; independent spark
        (redf left right))))                                                    ;; combine = let body (post-barrier, no spark)

;; ── Self-tests ───────────────────────────────────────────────────────
;; `(mod test)` — backing file collections/parallel/test.cl (extraction-stable
;; per spec §8.2.5). The tests assert sequential-identity against vec-map /
;; vec-reduce: parallelism is transparent, so correctness is checkable serially.

(mod test)
