;; collections/vec.cl — Vec utility functions and construction macro
;;
;; Higher-level operations on Vec, built on the primitives:
;;   vec-len, vec-get, vec-set, vec-push
;;
;; Also provides the `vec` construction macro.
;;
;; Spec: plan-stdlib.md §3.3

(import [prelude []])
(import [primitives [*]])

;; Macro body uses qualified macros/ name so expansion is independent
;; of the call-site's imports (spec §9.1.3).
(defmacro vec "Construct a vec from elements" [&elems]
  (macros/SexpBracket elems))

;; ── Curated Clojure-aligned Vec verbs ────────────────────────────────
;; These wrap the raw `vec-*` primitives behind Clojure names so callers
;; never need the bare primitive. `count`/`get`/`conj` are PROMOTED to the
;; bare prelude (S86 de-leak — the curated surface needs a bare collection
;; path now that the raw `vec-*` re-exports are gone). `assoc` stays
;; module-qualified (reserved for a future Map `assoc`; FIXME 0402). The
;; Phase-H collection trait will subsume `count`/`get`/`conj` under the
;; same bare names.

(defn count "Number of elements in a Vec"
  [v] :Int
  (vec-len v))

(defn get "Element at index i (0-indexed)"
  [v :Int i]
  (vec-get v i))

(defn conj "Return a Vec with x appended (Clojure conj, Vec end)"
  [v x]
  (vec-push v x))

(defn assoc "Return a Vec with index i set to x"
  [v :Int i x]
  (vec-set v i x))

(defn vec-map "Apply a function to each element of a Vec"
  [f v]
  (vec-map-loop f v (vec-len v) 0 []))

(defn- vec-map-loop "Tail-recursive helper for vec-map"
  [f v :Int len :Int i acc]
  (if (ge-i64 i len) acc
    (vec-map-loop f v len (add-i64 i 1) (vec-push acc (f (vec-get v i))))))

(defn vec-filter "Keep only elements satisfying the predicate"
  [pred v]
  (vec-filter-loop pred v (vec-len v) 0 []))

(defn- vec-filter-loop "Tail-recursive helper for vec-filter"
  [pred v :Int len :Int i acc]
  (if (ge-i64 i len) acc
    (let [x (vec-get v i)]
      (if (pred x)
        (vec-filter-loop pred v len (add-i64 i 1) (vec-push acc x))
        (vec-filter-loop pred v len (add-i64 i 1) acc)))))

(defn vec-reduce "Reduce a Vec to a single value with a function and initial accumulator"
  [f init v]
  (vec-reduce-loop f init v (vec-len v) 0))

(defn- vec-reduce-loop "Tail-recursive helper for vec-reduce"
  [f acc v :Int len :Int i]
  (if (ge-i64 i len) acc
    (vec-reduce-loop f (f acc (vec-get v i)) v len (add-i64 i 1))))

(defn vec-reverse "Reverse a Vec"
  [v]
  (vec-reverse-loop v (vec-len v) (sub-i64 (vec-len v) 1) []))

(defn- vec-reverse-loop "Tail-recursive helper for vec-reverse"
  [v :Int len :Int i acc]
  (if (lt-i64 i 0) acc
    (vec-reverse-loop v len (sub-i64 i 1) (vec-push acc (vec-get v i)))))

(defn vec-any? "Test if any element of a Vec satisfies the predicate"
  [pred v]
  (vec-any-loop pred v (vec-len v) 0))

(defn- vec-any-loop "Tail-recursive helper for vec-any?"
  [pred v :Int len :Int i]
  (if (ge-i64 i len) false
    (if (pred (vec-get v i)) true
      (vec-any-loop pred v len (add-i64 i 1)))))

(defn vec-all? "Test if all elements of a Vec satisfy the predicate"
  [pred v]
  (vec-all-loop pred v (vec-len v) 0))

(defn- vec-all-loop "Tail-recursive helper for vec-all?"
  [pred v :Int len :Int i]
  (if (ge-i64 i len) true
    (if (pred (vec-get v i))
      (vec-all-loop pred v len (add-i64 i 1))
      false)))

(defn vec-for-each "Apply a function to each element for side effects, return unit"
  [f v]
  (vec-for-each-loop f v (vec-len v) 0))

(defn- vec-for-each-loop "Tail-recursive helper for vec-for-each"
  [f v :Int len :Int i]
  (if (ge-i64 i len) 0
    (let [_ (f (vec-get v i))]
      (vec-for-each-loop f v len (add-i64 i 1)))))

(defn vec-zip-with "Combine two Vecs element-wise with a function"
  [f va vb]
  (let [len (if (lt-i64 (vec-len va) (vec-len vb)) (vec-len va) (vec-len vb))]
    (vec-zip-loop f va vb len 0 [])))

(defn- vec-zip-loop "Tail-recursive helper for vec-zip-with"
  [f va vb :Int len :Int i acc]
  (if (ge-i64 i len) acc
    (vec-zip-loop f va vb len (add-i64 i 1)
      (vec-push acc (f (vec-get va i) (vec-get vb i))))))

;; NOTE(0488-family, S101 6b): the intended simplification
;; `(vec-reduce vec-push va vb)` (builtin-as-value fold) is HELD. The bare
;; standalone call works with that body, but it poisons COMPOSED use at the
;; consuming turn: with the fold body, `(count (vec-concat [1 2] [3 4 5]))`
;; from user code fails codegen "undefined function: count" (any imported
;; generic applied over the result — `get` likewise). The loop body below
;; composes fine. Re-attempt the fold body when the 0488 generic-value-use
;; mono-instance defect class is fixed; the composed self-test rows in
;; vec/test.cl (test-vec-concat-*) are the guard that will catch it.
;; ALSO (6b follow-up): with the fold body the empty-vec rows
;; (test-vec-concat-empty-*) fail TYPECHECK ("ambiguous type", even with
;; a :(Vec Int) [] pin), which ABORTS cold-cache prelude compile / REPL
;; startup — so a fold-body re-attempt fails loudly at startup, not just
;; on composed calls. See FIXME 0488 §Addendum.
(defn vec-concat "Concatenate two Vecs"
  [va vb]
  (vec-concat-loop va vb (vec-len vb) 0))

(defn- vec-concat-loop "Tail-recursive helper for vec-concat"
  [acc vb :Int len :Int i]
  (if (ge-i64 i len) acc
    (vec-concat-loop (vec-push acc (vec-get vb i)) vb len (add-i64 i 1))))

;; NOTE(0488): vec-flatten is currently UNUSABLE from user code — passing
;; the same-module generic `vec-concat` as a value to `vec-reduce` loses
;; its mono instance at the consuming turn's codegen batch (FIXME 0488,
;; imported/generic value-use; /qa guard in flight). Its self-test is owed
;; and rides 0488's fix — see collections/vec/test.cl.
(defn vec-flatten "Flatten a Vec of Vecs into a single Vec"
  [vv]
  (vec-reduce vec-concat [] vv))

;; ── range (eager) — Stage C.1 gap G3 ─────────────────────────────────
;; `(range lo hi)` builds the eager Vec [lo, lo+1, …, hi-1] — HALF-OPEN
;; (inclusive lo, EXCLUSIVE hi), matching Clojure's `(range start end)`.
;; This is the highest-leverage adequacy gap (G3): it collapses the
;; pervasive hand-threaded `(if (= i N) acc (helper (+ i 1) …))` index
;; recursion in the exemplar into `(vec-reduce f init (range 0 N))` /
;; `(vec-map f (range 0 N))`. `range` is NOT 0402-reserved, but it FEEDS the
;; future collection trait's map/reduce — curating it here does not pull a
;; bare `map`/`reduce` into the prelude (§11.4a caveat). Home: collections.vec
;; (it produces a Vec; lives beside count/get/conj). Empty when hi <= lo.

(defn range "Eager Vec of ints [lo, hi) — inclusive lo, exclusive hi"
  [:Int lo :Int hi] :(Vec Int)
  (range-loop lo hi []))

(defn- range-loop "Tail-recursive helper for range"
  [:Int i :Int hi acc] :(Vec Int)
  (if (ge-i64 i hi) acc
    (range-loop (add-i64 i 1) hi (vec-push acc i))))

;; ── Self-tests ───────────────────────────────────────────────────────
;; `(mod- test …)` submodule (S87 Stage C.2): exercises the curated Clojure
;; verbs (count/get/conj/assoc) and the vec combinators with the harness.
;; Vec values reduce to Int scalars (via count/get/vec-reduce) for assert-eq.

(mod- test)
