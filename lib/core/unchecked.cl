(import [primitives [*]])

;; Unchecked arithmetic: wraps on overflow, traps on div-by-zero.
;; NOT in the prelude — users must explicitly import:
;;   (import [core/unchecked [Unchecked]])

(deftrait Unchecked "Unchecked arithmetic (wraps on overflow, traps on div-by-zero)"
  (+ "Unchecked addition" [self self] self)
  (- "Unchecked subtraction" [self self] self)
  (* "Unchecked multiplication" [self self] self)
  (/ "Unchecked division" [self self] self))

(impl Unchecked Int
  (defn + [x y] (add-i64 x y))
  (defn - [x y] (sub-i64 x y))
  (defn * [x y] (mul-i64 x y))
  (defn / [x y] (div-i64 x y)))

(impl Unchecked Float
  (defn + [x y] (add-f64 x y))
  (defn - [x y] (sub-f64 x y))
  (defn * [x y] (mul-f64 x y))
  (defn / [x y] (div-f64 x y)))
