;; 30-parallel-map-reduce.cl -- A general parallel `par-map` over a Functor
;;
;; Example 28 introduced lenient evaluation: INDEPENDENT `let` bindings are
;; sparked onto a thread pool automatically -- no `par-let`, no `spawn`, no
;; threads in the source. This example shows the building block in its full
;; reach: lenient evaluation also sparks independent, individually-expensive
;; **arguments of a function application**. That single widening is enough to
;; make a fully general parallel `par-map` (map a function over a collection,
;; every application running in parallel) just `fmap` of an expensive function
;; -- no manual per-shape workaround required.
;;
;; ---------------------------------------------------------------------------
;; WHAT SPARKS TODAY (verified against the compiler, not assumed)
;;
;; The sparkability pass (cranelisp-backend control_flow/sparkability.rs) runs
;; at TWO call sites with one shared cost heuristic:
;;
;;   * `let` bindings -- an independent, non-trivial binding sparks (example 28).
;;
;;   * apply ARGUMENTS -- in `(f a b)`, each argument that is itself a
;;     non-trivial call sparks. Arguments share no binding scope, so they are
;;     mutually independent by construction. This means:
;;       - `(combine (recur left) (recur right))` runs both recursions in
;;         PARALLEL -- the obvious divide-and-conquer form, no `let` lifting.
;;       - `(Pair (func a) (func b))` runs both applications in PARALLEL --
;;         so `fmap` of an expensive function IS a parallel map.
;;
;; The shared gates (both sites):
;;   * Non-trivial: cheap builtins (+ - * / and the comparisons) and bare
;;     constructors / var-refs / literals are never sparked -- only real calls.
;;   * At least TWO candidates at the site (one spark buys nothing).
;;   * A tail self-call is left to TCO and never sparked -- so a tail-recursive
;;     accumulator loop does its work serially in-place (this is exactly why the
;;     `work` leaf below is a safe, non-over-sparking unit of parallel work).
;;
;; Runtime safety net: a global in-flight-spark budget (default 4x threads,
;; override with CRANELISP_SPARK_BUDGET=N) caps how many sparks are live at
;; once -- over-budget sites resolve inline, so deep recursion can't explode.
;;
;; A/B any timing claim yourself: CRANELISP_NO_LENIENT=1 forces every binding
;; AND every argument serial; CRANELISP_SPARK_BUDGET=0 is the equivalent
;; runtime escape hatch for an already-compiled binary. Same result either way
;; -- parallelism is semantically transparent because the code is pure.
;; ---------------------------------------------------------------------------

;; --- The per-element work leaf: real work, single tail-recursive self-call ---
;; `work` is a tail-recursive accumulator: it burns `n` iterations of genuine
;; work and returns the count. Because its self-call is in TAIL position it is
;; left to TCO and never sparks internally -- so it is a clean unit of parallel
;; work, with NO internal over-spark. The top-level divide-and-conquer is the
;; only source of parallelism, which is exactly the teaching signal.
(defn work [:Int n :Int acc]
  (if (le-i64 n 0)
      acc
      (work (sub-i64 n 1) (add-i64 acc 1))))

;; `heavy` is an EXPENSIVE IDENTITY: it does ~1,000,000 iterations of real work
;; via `work`, then returns its argument unchanged (it adds the work result and
;; subtracts the same constant back out). This separates "real work worth
;; running in parallel" from "the value", so the arithmetic below stays simple
;; and the parallel result is trivially checkable: `heavy x == x`, always.
(defn heavy [:Int x]
  (add-i64 x (sub-i64 (work 1000000 0) 1000000)))       ;; -> x, after real work

;; --- Cheap split point: midpoint of the half-open range [lo, hi) ------------
;; Pure integer arithmetic -- cheap, so never sparked, and safely RECOMPUTED in
;; each half rather than bound once.
(defn mid-of [:Int lo :Int hi]
  (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

;; ===========================================================================
;; STAGE 1 -- Recursive divide-and-conquer map-reduce on a Vec
;; ===========================================================================
;;
;; The OBVIOUS recursive form now parallelises directly: the two recursive
;; halves are arguments to `add-i64`, and independent apply-arguments spark.
;; No `let` lifting, no manual workaround -- `(add-i64 (recur left)
;; (recur right))` runs the two halves in parallel automatically.
(defn par-map-reduce [v :Int lo :Int hi]
  (if (le-i64 (sub-i64 hi lo) 1)
      (heavy (vec-get v lo))                              ;; leaf: map one element
      (add-i64 (par-map-reduce v lo (mid-of lo hi))       ;; sparked apply-arg
               (par-map-reduce v (mid-of lo hi) hi))))    ;; sparked apply-arg

;; Wall-clock A/B (8 leaves, ~1,000,000 work iterations each):
;;     lenient ON  : the two halves at each level run in parallel
;;     lenient OFF : halves run sequentially  (CRANELISP_NO_LENIENT=1)
;; Same RESULT either way -- parallelism is semantically transparent (pure code).
;;
;; HONESTY ON SPEED -- parallel is NOT an unconditional win. Sparking costs real
;; overhead (per-branch IVar/thunk allocation + atomic RC + allocator contention
;; on a shared substrate), so a wall-clock payoff only materialises for coarse,
;; compute-bound branches. Even THIS pure-compute workload measured only
;; break-even-to-slightly-slower at this granularity (S94 /port: ~1.3s parallel
;; vs ~0.9s serial). The guarantee is "never DRAMATICALLY slower than serial",
;; not "always faster"; for allocation-/RC-heavy work parallel can be much slower
;; until the contention-aware gate lands (design/arch/effect-concurrency.md §3.1).
;; The teaching signal here is the SHAPE -- independent work sparks with zero
;; thread plumbing in the source -- not a promised speedup.

;; ===========================================================================
;; STAGE 2 -- A general `par-map` over a Functor
;; ===========================================================================
;;
;; The natural generalisation is `par-map`: map a function over ANY container
;; (a Functor), running every application in parallel. Because independent
;; apply-arguments spark, this is simply `fmap` of an expensive function -- no
;; dedicated primitive, no per-shape workaround. We define the Functor inline
;; (free-standing -- no stdlib) over a small fixed-size box.

;; A 2-cell container we can be a Functor over.
(deftype (Pair a) (Pair [:a fst :a snd]))

;; The Functor trait: fmap applies a function inside the container, preserving
;; its structure (same shape introduced in example 26).
(deftrait (Functor f)
  (fmap [:(Fn [a] b) func :(f a) x] (f b)))

;; Functor for Pair. The body `(Pair (func a) (func b))` has TWO independent
;; apply-arguments -- `(func a)` and `(func b)` -- so both applications spark
;; and run in parallel. This `fmap` IS a parallel map: there is nothing extra
;; to write.
(impl (Functor f) (Functor Pair)
  (defn fmap [func p]
    (match p
      [(Pair a b) (Pair (func a) (func b))])))           ;; both apps spark

;; A general `par-map` is therefore just `fmap` of an expensive function:
;;
;;     (fmap heavy some-functor)   ;; every application runs in parallel
;;
;; (If an explicit-`let` spelling is ever preferred for a known-arity shape,
;;  `(let [fa (func a) fb (func b)] (Pair fa fb))` is the equivalent that the
;;  example-28 `let`-spark building block already covered -- but it is now
;;  redundant: the direct constructor form above sparks identically.)

(defn pair-sum [p]
  (match p [(Pair a b) (add-i64 a b)]))

;; ===========================================================================
;; Driver
;; ===========================================================================
;; Stage 1: map `heavy` over eight 39s via divide-and-conquer and sum them.
;;   heavy is the identity, so the total is 8 * 39 = 312.
;; Cross-check against the general par-map (Stage 2): `fmap heavy` over a Pair
;; of 39s, summed and scaled by 4, also totals 8 * 39 = 312. We assert the two
;; agree and return the total directly:
;;   312  (exit byte 56).
(defn main []
  (let [v          [39 39 39 39 39 39 39 39]
        dc-total   (par-map-reduce v 0 (vec-len v))       ;; 8 * heavy(39) = 312
        pair-total (mul-i64 (pair-sum (fmap heavy (Pair 39 39))) 4)]  ;; 4*78 = 312
    ;; The recursive divide-and-conquer reduce and the general par-map agree.
    (if (eq-i64 dc-total pair-total)
        (Pure dc-total)                                   ;; -> 312  (exit 56)
        (Pure 0))))
