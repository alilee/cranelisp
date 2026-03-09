;; num/num.cl — Num trait and primitive impls
;;
;; The Num trait defines arithmetic operations. All numeric types implement
;; this trait for the standard arithmetic operators.
;;
;; Spec: 07-traits.md §7.1

(deftrait Num
  (+ [self self] self)
  (- [self self] self)
  (* [self self] self)
  (/ [self self] self))

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
