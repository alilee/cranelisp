;; Test prelude: minimal standard library for compiler tests.
;;
;; This is NOT the standard library. It contains only what the test suite
;; needs to bootstrap type/trait/function contexts. Macros and macro helpers
;; are excluded (parse_program filters defmacro; macro compilation uses
;; the disk-based module graph).
;;
;; If tests need new stdlib features, add them here — but prefer keeping
;; this file small to keep tests fast.

;; ── IO ─────────────────────────────────────────────

(defn pure "Lift a value into IO" [x] (IOVal x))
(defn bind "Chain IO actions" [io cont]
  (match io [(IOVal v) (cont v)]))

;; ── Core Data Types ──────────────────────────────────

(deftype (Option a) "An optional value, either None or Some"
  (None "Represents absence of a value")
  (Some "Wraps a present value" [:a val]))

(deftype (List a) "A singly-linked immutable list"
  (Nil "The empty list")
  (Cons "A list node with head element and tail" [:a head :(List a) tail]))

;; ── Trait Declarations ──────────────────────────────

(deftrait Num "Numeric arithmetic operations"
  (+ "Add two values" [self self] self)
  (- "Subtract two values" [self self] self)
  (* "Multiply two values" [self self] self)
  (/ "Divide two values" [self self] self))

(deftrait Eq "Equality comparison"
  (= "Test equality" [self self] Bool))

(deftrait Ord "Ordering comparisons"
  (< "Test less-than" [self self] Bool)
  (> "Test greater-than" [self self] Bool)
  (<= "Test less-than-or-equal" [self self] Bool)
  (>= "Test greater-than-or-equal" [self self] Bool))

(deftrait Display "Convert to string representation"
  (show "Convert value to string" [self] String))

(deftrait (Functor f) "Mappable container"
  (fmap "Apply function to values inside container" [(Fn [a] b) (f a)] (f b)))

;; ── Int ─────────────────────────────────────────────

(impl Num Int
  (defn + [x y] (add-i64 x y))
  (defn - [x y] (sub-i64 x y))
  (defn * [x y] (mul-i64 x y))
  (defn / [x y] (div-i64 x y)))

(impl Eq Int
  (defn = [x y] (eq-i64 x y)))

(impl Ord Int
  (defn < [x y] (lt-i64 x y))
  (defn > [x y] (gt-i64 x y))
  (defn <= [x y] (le-i64 x y))
  (defn >= [x y] (ge-i64 x y)))

(impl Display Int
  (defn show [x] (int-to-string x)))

(defn inc "Increment by one" [:Int x] (+ x 1))

;; ── Float ───────────────────────────────────────────

(impl Num Float
  (defn + [x y] (add-f64 x y))
  (defn - [x y] (sub-f64 x y))
  (defn * [x y] (mul-f64 x y))
  (defn / [x y] (div-f64 x y)))

(impl Eq Float
  (defn = [x y] (eq-f64 x y)))

(impl Ord Float
  (defn < [x y] (lt-f64 x y))
  (defn > [x y] (gt-f64 x y))
  (defn <= [x y] (le-f64 x y))
  (defn >= [x y] (ge-f64 x y)))

(impl Display Float
  (defn show [x] (float-to-string x)))

;; ── Bool & String ───────────────────────────────────

(impl Display Bool
  (defn show [x] (bool-to-string x)))

(impl Display String
  (defn show [x] (string-identity x)))

;; ── Option ──────────────────────────────────────────

(impl Functor Option
  (defn fmap [f opt]
    (match opt
      [None None
       (Some x) (Some (f x))])))

;; ── List ────────────────────────────────────────────

(defn empty? "Returns true if list is empty" [xs]
  (match xs
    [Nil true
     _ false]))

(defn concat "Concatenate two lists" [xs ys]
  (match xs
    [Nil ys
     (Cons h t) (Cons h (concat t ys))]))

(defn list-reduce "Reduce a list with function and initial accumulator" [f init xs]
  (match xs
    [Nil init
     (Cons h t) (list-reduce f (f init h) t)]))

(impl Functor List
  (defn fmap [f lst]
    (match lst
      [Nil Nil
       (Cons h t) (Cons (f h) (fmap f t))])))

(defn reverse "Reverse a list" [xs]
  (list-reduce (fn [acc x] (Cons x acc)) Nil xs))

;; ── Lazy Sequences ──────────────────────────────────

(deftype (Seq a) "A lazy sequence with thunked tail"
  (SeqNil "Empty lazy sequence")
  (SeqCons "Lazy sequence node with head and thunked rest" [:a head :(Fn [] (Seq a)) rest]))

(impl Functor Seq
  (defn fmap [f s]
    (match s
      [SeqNil SeqNil
       (SeqCons h t) (SeqCons (f h) (fn [] (fmap f (t))))])))

(defn lazy-filter "Filter a lazy sequence by predicate" [pred s]
  (match s
    [SeqNil SeqNil
     (SeqCons h t)
      (if (pred h)
        (SeqCons h (fn [] (lazy-filter pred (t))))
        (lazy-filter pred (t)))]))

(defn lazy-take "Take first n elements from lazy sequence" [:Int n s]
  (if (<= n 0) SeqNil
    (match s
      [SeqNil SeqNil
       (SeqCons h t) (SeqCons h (fn [] (lazy-take (- n 1) (t))))])))

(defn lazy-drop "Drop first n elements from lazy sequence" [:Int n s]
  (if (<= n 0) s
    (match s
      [SeqNil SeqNil
       (SeqCons h t) (lazy-drop (- n 1) (t))])))

(defn lazy-reduce "Reduce a lazy sequence with function and initial accumulator" [f init s]
  (match s
    [SeqNil init
     (SeqCons h t) (lazy-reduce f (f init h) (t))]))

(defn range-from "Infinite lazy sequence starting at n" [:Int n]
  (SeqCons n (fn [] (range-from (+ n 1)))))

(defn iterate "Infinite lazy sequence: x, (f x), (f (f x)), ..." [f x]
  (SeqCons x (fn [] (iterate f (f x)))))

(defn repeat "Infinite lazy sequence of x" [x]
  (SeqCons x (fn [] (repeat x))))

(defn to-list "Force entire lazy sequence into a list" [s]
  (match s
    [SeqNil Nil
     (SeqCons h t) (Cons h (to-list (t)))]))

;; ── Collection API ──────────────────────────────────

(defn vec-to-seq "Convert vec to lazy sequence starting at index" [:Int idx v]
  (if (>= idx (vec-len v)) SeqNil
    (SeqCons (vec-get v idx) (fn [] (vec-to-seq (+ idx 1) v)))))

(defn list-to-seq "Convert list to lazy sequence" [xs]
  (match xs
    [Nil SeqNil
     (Cons h t) (SeqCons h (fn [] (list-to-seq t)))]))

(defn seq "Convert collection to lazy sequence"
  ([v] (vec-to-seq 0 v))
  ([l] (list-to-seq l)))

(defn map "Apply function to each element, returning lazy sequence"
  ([f v] (fmap f (vec-to-seq 0 v)))
  ([f l] (fmap f (list-to-seq l)))
  ([f s] (match s
           [SeqNil (fmap f SeqNil)
            _ (fmap f s)])))

(defn filter "Return lazy sequence of elements matching predicate"
  ([pred v] (lazy-filter pred (vec-to-seq 0 v)))
  ([pred l] (lazy-filter pred (list-to-seq l)))
  ([pred s] (lazy-filter pred s)))

(defn take "Take first n elements as lazy sequence"
  ([:Int n v] (lazy-take n (vec-to-seq 0 v)))
  ([:Int n l] (lazy-take n (list-to-seq l)))
  ([:Int n s] (lazy-take n s)))

(defn drop "Drop first n elements, return rest as lazy sequence"
  ([:Int n v] (lazy-drop n (vec-to-seq 0 v)))
  ([:Int n l] (lazy-drop n (list-to-seq l)))
  ([:Int n s] (lazy-drop n s)))

(defn reduce "Reduce collection to single value with function and initial accumulator"
  ([f init v] (lazy-reduce f init (vec-to-seq 0 v)))
  ([f init l] (lazy-reduce f init (list-to-seq l)))
  ([f init s] (lazy-reduce f init s)))
