;; 30-parallel-map-reduce.cl -- Toward a parallel `par-map` over a Functor
;;
;; Example 28 introduced lenient evaluation: INDEPENDENT `let` bindings are
;; sparked onto a thread pool automatically, with no `par-let`, no `spawn`,
;; no threads in the source. This example pushes that building block as far
;; as it goes today -- a self-parallelising map-reduce over a Vec -- and then
;; is HONEST about where the road currently ends: a fully general `par-map`
;; (map a function over a collection, every application in parallel) is NOT
;; yet expressible, because of two concrete limits in the current analysis.
;; We name both, show what `par-map` over a Functor WOULD look like, and show
;; the manual workaround the let-spark building block does support.
;;
;; ---------------------------------------------------------------------------
;; WHAT ACTUALLY SPARKS TODAY (verified against the compiler, not assumed)
;;
;; The sparkability pass (cranelisp-backend control_flow/sparkability.rs)
;; sparks a binding only when ALL of these hold:
;;
;;   * It is a `let` binding. ONLY `let` bindings are analysed. Arguments to
;;     an apply are NOT sparked -- `(f a b)` does NOT evaluate `a` and `b`
;;     in parallel, even when they are independent and expensive. (Limit #2.)
;;
;;   * Its right-hand side does NOT reference any name bound EARLIER in the
;;     same `let` block. A binding that depends on an earlier one is left
;;     SERIAL. (Limit #1.) This is a CONSERVATIVE-ANALYSIS limit, not a hard
;;     semantic one: the underlying IVar machinery could spark the dependent
;;     binding and force the dependency on demand. The analysis simply
;;     chooses not to today.
;;
;;   * It is non-trivial: cheap builtins (+ - * / and the comparisons) and
;;     bare constructors/var-refs are never sparked -- only real work is.
;;
;;   * At least TWO bindings in the block qualify (one spark buys nothing).
;;
;; A/B any timing claim yourself with the CRANELISP_NO_LENIENT=1 env var,
;; which forces every binding serial.
;; ---------------------------------------------------------------------------

;; --- The per-element "map" function: an expensive pure computation ---------
;; fib is deliberately costly so that each application is real work worth
;; sparking. This is the function we want to map over a collection.
(defn fib [:Int n]
  (if (lt-i64 n 2)
      n
      (add-i64 (fib (sub-i64 n 1))
               (fib (sub-i64 n 2)))))

;; --- Cheap split point: midpoint of the half-open range [lo, hi) ----------
;; Pure integer arithmetic -- never sparked, and because it is cheap we can
;; safely RECOMPUTE it in each half rather than binding it once (which would
;; make both halves depend on it and serialise them -- Limit #1).
(defn mid-of [:Int lo :Int hi]
  (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

;; ===========================================================================
;; STAGE 1 -- The building block: a self-parallelising map-reduce on a Vec
;; ===========================================================================
;;
;; We cannot spark apply-arguments, so we cannot write the obvious
;; `(combine (recur left) (recur right))` and expect the two recursions to
;; run in parallel -- they are apply-args, and apply-args don't spark
;; (Limit #2). The standard workaround is DIVIDE-AND-CONQUER expressed with
;; `let`: bind each half to a `let` name, and the two halves spark because
;; they are independent let bindings.
;;
;; v, lo and hi are PARAMETERS, not same-block `let` bindings, so both halves
;; may freely reference them without triggering Limit #1. The two halves are
;; the only `let` bindings here and neither depends on the other => both
;; spark.
(defn par-map-reduce [v :Int lo :Int hi]
  (if (le-i64 (sub-i64 hi lo) 1)
      (fib (vec-get v lo))                                 ;; leaf: map one element
      (let [left  (par-map-reduce v lo (mid-of lo hi))     ;; sparkable: indep half
            right (par-map-reduce v (mid-of lo hi) hi)]    ;; sparkable: indep half
        (add-i64 left right))))                            ;; combine (barrier here)

;; Wall-clock A/B (8 leaves, each fib(38) ~= 39,088,169):
;;     lenient ON  : two halves at each level run in parallel
;;     lenient OFF : halves run sequentially  (CRANELISP_NO_LENIENT=1)
;; Same result either way -- parallelism is semantically transparent because
;; the code is pure.

;; ===========================================================================
;; STAGE 2 -- What a general `par-map` over a Functor WOULD look like
;; ===========================================================================
;;
;; The natural generalisation is `par-map`: map a function over ANY container
;; (a Functor), running every application in parallel. We define the Functor
;; shape inline (free-standing -- no stdlib) over a small fixed-size box so
;; the example stays self-contained.

;; A 2-cell container we can be a Functor over.
(deftype (Pair a) (Pair [:a fst :a snd]))

;; The Functor trait: fmap applies a function inside the container,
;; preserving its structure (same shape introduced in example 26).
(deftrait (Functor f)
  (fmap [:(Fn [a] b) func :(f a) x] (f b)))

;; SERIAL fmap for Pair. Note the two applications `(func a)` and `(func b)`
;; are APPLY-ARGUMENTS to the `Pair` constructor -- so even though they are
;; independent and (with `fib`) expensive, they do NOT spark. This is the
;; honest current state: `fmap` here is sequential.
(impl Functor Pair
  (defn fmap [func p]
    (match p
      [(Pair a b) (Pair (func a) (func b))])))            ;; <- apply-args: NOT sparked

;; The general `par-map` we WANT is just `fmap` of an expensive function:
;;
;;     (par-map fib some-functor)   ;; every application in parallel
;;
;; For this to be PARALLEL, the language would need either
;;   (i)  sparking of independent APPLY-ARGUMENTS (so `(Pair (fib a) (fib b))`
;;        sparks both fibs -- lifting Limit #2), or
;;   (ii) a dedicated `par-map` / parallel-fmap primitive that the runtime
;;        sparks element-wise.
;; Neither exists today, so `fmap fib` is correct but SERIAL.

;; --- The manual workaround: lift the applications into independent lets -----
;; We can recover parallelism for a KNOWN-ARITY container by hand: bind each
;; element-application to its own independent `let` name (Stage-1 trick), then
;; rebuild the container. This is a manual, per-shape `par-map` -- it works,
;; but it does not generalise to arbitrary collections, which is exactly the
;; gap a real `par-map` would close.
(defn par-fmap-pair [func p]
  (match p
    [(Pair a b)
     (let [fa (func a)                                     ;; sparkable: indep
           fb (func b)]                                    ;; sparkable: indep
       (Pair fa fb))]))                                    ;; rebuild (barrier)

(defn pair-sum [p]
  (match p [(Pair a b) (add-i64 a b)]))

;; Demonstrate the manual par-map: map fib over a Pair of 38s, in parallel.
;; 2 * fib(38) = 2 * 39,088,169 = 78,176,338.
(defn manual-par-map-pair []
  (pair-sum (par-fmap-pair fib (Pair 38 38))))            ;; -> 78,176,338

;; ===========================================================================
;; Driver
;; ===========================================================================
;; Stage 1: map fib over eight 38s via divide-and-conquer and sum them:
;;   8 * fib(38) = 8 * 39,088,169 = 312,705,352.
;; Cross-check against the manual Pair par-map (Stage 2): four Pairs of 38s
;; mapped in parallel also total 8 * fib(38). We assert the two agree, then
;; scale the Stage-1 total down to a small exit code:
;;   312,705,352 / 1,000,000 = 312  (exit byte 56).
(defn main []
  (let [v          [38 38 38 38 38 38 38 38]
        dc-total   (par-map-reduce v 0 (vec-len v))        ;; sparkable: indep
        pair-total (mul-i64 (manual-par-map-pair) 4)]      ;; sparkable: indep
    ;; The divide-and-conquer reduce and the manual Pair par-map must agree.
    (if (eq-i64 dc-total pair-total)
        (Pure (div-i64 dc-total 1000000))                  ;; -> 312  (exit 56)
        (Pure 0))))
