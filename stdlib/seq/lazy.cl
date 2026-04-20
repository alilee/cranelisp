;; seq/lazy.cl — Lazy sequence type + operations
;;
;; A lazy sequence uses thunks (zero-argument closures) to defer computation.
;; SeqNil is the empty sequence; SeqCons holds a head value and a thunk that
;; produces the rest of the sequence when forced.
;;
;; Spec: 12-runtime.md §12.4.2, plan-stdlib.md §3.3

;; This module suppresses the implicit prelude glob (per spec §8.3.6) because
;; it is part of the stdlib and a project's custom prelude could re-export
;; from us — that would be a circular dependency. All names must therefore be
;; resolved through explicit imports.

;; ── Seq Type ────────────────────────────────────────────────────────────

(import [prelude []])
(import [primitives [*]])
(import [collections.list [Nil Cons]])
(import [fn.option [None Some]])

(deftype (Seq a) "A lazy sequence with thunked tail"
  SeqNil
  (SeqCons [:a head :(Fn [] (Seq a)) rest]))

;; ── Predicates ──────────────────────────────────────────────────────────

(defn seq-empty? "Test if a lazy sequence is empty"
  [s] :Bool
  (match s
    [SeqNil true
     _ false]))

;; ── Producers ───────────────────────────────────────────────────────────

(defn range-from "Infinite lazy sequence of integers starting at n: n, n+1, n+2, ..."
  [:Int n]
  (SeqCons n (fn [] (range-from (add-i64 n 1)))))

(defn iterate "Infinite lazy sequence: x, (f x), (f (f x)), ..."
  [f x]
  (SeqCons x (fn [] (iterate f (f x)))))

(defn repeat "Infinite lazy sequence of a constant value"
  [x]
  (SeqCons x (fn [] (repeat x))))

(defn cycle "Infinite lazy sequence cycling through elements of a Vec"
  [v]
  (cycle-from v 0))

(defn- cycle-from "Helper: cycle from index i through a Vec"
  [v :Int i]
  (if (ge-i64 (vec-len v) 1)
    (let [idx (if (ge-i64 i (vec-len v)) 0 i)]
      (SeqCons (vec-get v idx) (fn [] (cycle-from v (add-i64 idx 1)))))
    SeqNil))

;; ── Core Lazy Operations ────────────────────────────────────────────────

(defn seq-map "Apply a function to each element of a lazy sequence"
  [f s]
  (match s
    [SeqNil SeqNil
     (SeqCons h t) (SeqCons (f h) (fn [] (seq-map f (t))))]))

(defn seq-filter "Keep elements of a lazy sequence that satisfy the predicate"
  [pred s]
  (match s
    [SeqNil SeqNil
     (SeqCons h t)
       (if (pred h)
         (SeqCons h (fn [] (seq-filter pred (t))))
         (seq-filter pred (t)))]))

(defn seq-reduce "Left fold over a lazy sequence"
  [f init s]
  (match s
    [SeqNil init
     (SeqCons h t) (seq-reduce f (f init h) (t))]))

;; ── Consumers ───────────────────────────────────────────────────────────

(defn seq-take "Take the first n elements of a lazy sequence, returning a Vec"
  [:Int n s]
  (seq-take-acc n s []))

(defn- seq-take-acc "Tail-recursive helper for seq-take"
  [:Int n s acc]
  (if (le-i64 n 0) acc
    (match s
      [SeqNil acc
       (SeqCons h t) (seq-take-acc (sub-i64 n 1) (t) (vec-push acc h))])))

(defn seq-drop "Drop the first n elements of a lazy sequence"
  [:Int n s]
  (if (le-i64 n 0) s
    (match s
      [SeqNil SeqNil
       (SeqCons _ t) (seq-drop (sub-i64 n 1) (t))])))

(defn seq-nth "Get the nth element of a lazy sequence (0-indexed), or None"
  [:Int n s]
  (match s
    [SeqNil None
     (SeqCons h t)
       (if (eq-i64 n 0) (Some h) (seq-nth (sub-i64 n 1) (t)))]))

(defn take-while "Take elements from a lazy sequence while predicate holds"
  [pred s]
  (match s
    [SeqNil SeqNil
     (SeqCons h t)
       (if (pred h)
         (SeqCons h (fn [] (take-while pred (t))))
         SeqNil)]))

(defn drop-while "Drop elements from a lazy sequence while predicate holds"
  [pred s]
  (match s
    [SeqNil SeqNil
     (SeqCons h t)
       (if (pred h)
         (drop-while pred (t))
         s)]))

(defn to-list "Force an entire lazy sequence into a List (caution: infinite seqs will loop)"
  [s]
  (to-list-helper (to-vec s)))

(defn- to-list-helper "Build a list from a vec by iterating from end to start"
  [v]
  (vec-to-list-rev v (sub-i64 (vec-len v) 1)))

(defn- vec-to-list-rev "Build list from vec indices in reverse"
  [v :Int i]
  (if (lt-i64 i 0) Nil
    (Cons (vec-get v i) (vec-to-list-rev v (sub-i64 i 1)))))

(defn to-vec "Force an entire lazy sequence into a Vec (caution: infinite seqs will loop)"
  [s]
  (to-vec-acc s []))

(defn- to-vec-acc "Tail-recursive helper for to-vec"
  [s acc]
  (match s
    [SeqNil acc
     (SeqCons h t) (to-vec-acc (t) (vec-push acc h))]))

;; ── Convenience Aliases ──────────────────────────────────────────────

(defn take "Take the first n elements of a lazy sequence, returning a Vec"
  [:Int n s]
  (seq-take n s))

(defn drop "Drop the first n elements of a lazy sequence"
  [:Int n s]
  (seq-drop n s))

(defn seq-zip-with "Combine two lazy sequences element-wise with a function"
  [f sa sb]
  (match sa
    [SeqNil SeqNil
     (SeqCons ha ta)
       (match sb
         [SeqNil SeqNil
          (SeqCons hb tb)
            (SeqCons (f ha hb) (fn [] (seq-zip-with f (ta) (tb))))])]))
