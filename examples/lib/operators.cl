;; examples/lib/operators.cl — the arithmetic/equality/ordering operator
;; traits, as an examples-local library module.
;;
;; EARNED BY: 15-traits.cl.
;;
;; This file is part of the examples-local library (see
;; `examples/lib/README.md`). It exists so that an example ABOUT
;; something else does not have to re-teach traits before it can write
;; `+`. Nothing here is new language surface: every declaration below is
;; exactly what 15-traits.cl builds from scratch, in front of the reader,
;; using only `deftrait`, `impl`, and the arithmetic primitives of 01/08.
;;
;; So: read 15 first. After 15, `(import [operators [Num + *]])` is a
;; shorthand for a lesson you have already had — not a new dependency and
;; not a standard library. (For the real standard library, and the far
;; larger vocabulary it provides, read the stdlib docs; this sequence
;; teaches the language.)
;;
;; Unlike `prelude.cl`, this module is NOT implicitly in scope. An
;; example must import it by name. That is deliberate: the import line is
;; the reader's cue that this example is standing on lesson 15.

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
