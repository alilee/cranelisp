;; collections/list.cl — List type (singly-linked immutable list)
;;
;; A recursive algebraic data type providing a classic functional list.
;; Constructors: Nil (empty list), Cons (head element + tail list).
;;
;; Also provides the `list` construction macro.
;;
;; Spec: 06-adt.md §6.1, plan-stdlib.md §3.3

(import [prelude []])
(import [primitives [*]])

;; `Option`/`Some`/`None` come in via the `primitives` glob above (primitives
;; seeds the canonical `Option` ADT, which `fn.option` re-exports). Importing
;; them again from `fn.option` would bring the SAME names from a second
;; immediate source and collide (spec §8.6.4) — so we rely on the glob.
(import [macros [SexpSym SexpList SCons SNil Sexp SList]])

(defmacro list "Construct a list from elements"
  ([] `Nil)
  ([x &rest] `(Cons ~x (list ~@rest))))

(deftype (List a) Nil (Cons [:a head :(List a) tail]))

(defn empty? "Test if a list is empty"
  [xs] :Bool
  (match xs
    [Nil true
     _ false]))

(defn length "Count the number of elements in a list"
  [xs] :Int
  (length-acc xs 0))

(defn- length-acc "Tail-recursive length accumulator"
  [xs :Int acc] :Int
  (match xs
    [Nil acc
     (Cons _ t) (length-acc t (add-i64 acc 1))]))

;; `first`/`rest` are the Clojure-aligned list accessors (renamed from the
;; S82 `head-of`/`tail-of`, per FIXME 0402). They are reached as
;; `collections.list/first` / `collections.list/rest` or via explicit
;; import — NOT bare prelude (the bare names are reserved for the Phase-H
;; seq trait, and pair `first` coexists in `collections.pair`; FIXME 0402).

(defn first "Get the first element of a list, or None if empty"
  [xs]
  (match xs
    [Nil None
     (Cons h _) (Some h)]))

(defn rest "Get all but the first element, or None if empty"
  [xs]
  (match xs
    [Nil None
     (Cons _ t) (Some t)]))

(defn fold "Left fold over a list: (fold f init [a b c]) = (f (f (f init a) b) c)"
  [f init xs]
  (match xs
    [Nil init
     (Cons h t) (fold f (f init h) t)]))

(defn foldr "Right fold over a list: (foldr f init [a b c]) = (f a (f b (f c init)))"
  [f init xs]
  (match xs
    [Nil init
     (Cons h t) (f h (foldr f init t))]))

(defn reverse "Reverse a list"
  [xs]
  (fold (fn [acc x] (Cons x acc)) Nil xs))

(defn map-list "Apply a function to each element of a list"
  [f xs]
  (foldr (fn [x acc] (Cons (f x) acc)) Nil xs))

(defn filter-list "Keep only elements satisfying the predicate"
  [pred xs]
  (foldr (fn [x acc] (if (pred x) (Cons x acc) acc)) Nil xs))

(defn append "Concatenate two lists"
  [xs ys]
  (foldr (fn [x acc] (Cons x acc)) ys xs))

(defn nth "Get the nth element of a list (0-indexed), or None if out of bounds"
  [:Int n xs]
  (match xs
    [Nil None
     (Cons h t)
     (if (eq-i64 n 0) (Some h) (nth (sub-i64 n 1) t))]))

(defn take-list "Take the first n elements of a list"
  [:Int n xs]
  (if (le-i64 n 0) Nil
    (match xs
      [Nil Nil
       (Cons h t) (Cons h (take-list (sub-i64 n 1) t))])))

(defn drop-list "Drop the first n elements of a list"
  [:Int n xs]
  (if (le-i64 n 0) xs
    (match xs
      [Nil Nil
       (Cons _ t) (drop-list (sub-i64 n 1) t)])))

(defn any? "Test if any element satisfies the predicate"
  [pred xs]
  (match xs
    [Nil false
     (Cons h t) (if (pred h) true (any? pred t))]))

(defn all? "Test if all elements satisfy the predicate"
  [pred xs]
  (match xs
    [Nil true
     (Cons h t) (if (pred h) (all? pred t) false)]))

(defn zip-with "Combine two lists element-wise with a function"
  [f xs ys]
  (match xs
    [Nil Nil
     (Cons xh xt)
     (match ys
       [Nil Nil
        (Cons yh yt) (Cons (f xh yh) (zip-with f xt yt))])]))

;; ── Self-tests ───────────────────────────────────────────────────────
;; `(mod- test …)` submodule (S87 Stage C.2): exercises the list operations
;; with the in-language harness. Tests reduce list values to Int/Bool first
;; (via `length`/`empty?`/`fold`) so assert-eq compares scalars.

(mod- test)
