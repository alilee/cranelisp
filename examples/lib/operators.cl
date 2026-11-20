;; Arithmetic, equality and ordering traits earned by 15-traits.cl.
;; Import explicitly, for example (import [operators [Num + *]]).
;; This module uses the mechanism taught there, with explicit implementations
;; of Ord's <= and >= where 15 demonstrates default method bodies.
;; It is an examples-local recap, not the standard library. See README.md.

;; --- Num: the four arithmetic operators (15-traits.cl) ----------------

(deftrait Num
  (+ [a b] self)
  (- [a b] self)
  (* [a b] self)
  (/ [a b] self))

(impl Num Int
  (defn + [a b] (add-i64 a b))
  (defn - [a b] (sub-i64 a b))
  (defn * [a b] (mul-i64 a b))
  (defn / [a b] (div-i64 a b)))

(impl Num Float
  (defn + [a b] (add-f64 a b))
  (defn - [a b] (sub-f64 a b))
  (defn * [a b] (mul-f64 a b))
  (defn / [a b] (div-f64 a b)))

;; --- Eq: equality, dispatched by type (15-traits.cl) ------------------

(deftrait Eq
  (= [a b] Bool)
  (!= [a b] Bool))

(impl Eq Int
  (defn = [a b] (eq-i64 a b))
  (defn != [a b] (not (eq-i64 a b))))

(impl Eq Float
  (defn = [a b] (eq-f64 a b))
  (defn != [a b] (not (eq-f64 a b))))

(impl Eq Bool
  (defn = [a b] (eq-bool a b))
  (defn != [a b] (not (eq-bool a b))))

(impl Eq String
  (defn = [a b] (str-eq a b))
  (defn != [a b] (not (str-eq a b))))

;; --- Ord: ordering (15-traits.cl) -------------------------------------

(deftrait Ord
  (< [a b] Bool)
  (> [a b] Bool)
  (<= [a b] Bool)
  (>= [a b] Bool))

(impl Ord Int
  (defn < [a b] (lt-i64 a b))
  (defn > [a b] (lt-i64 b a))
  (defn <= [a b] (not (lt-i64 b a)))
  (defn >= [a b] (not (lt-i64 a b))))

(impl Ord Float
  (defn < [a b] (lt-f64 a b))
  (defn > [a b] (lt-f64 b a))
  (defn <= [a b] (not (lt-f64 b a)))
  (defn >= [a b] (not (lt-f64 a b))))
