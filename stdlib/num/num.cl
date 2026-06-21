;; num/num.cl — Num trait and primitive impls
;;
;; The Num trait defines arithmetic operations. All numeric types implement
;; this trait for the standard arithmetic operators.
;;
;; Spec: 07-traits.md §7.1

(import [prelude []])
(import [primitives [*]])

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

;; ── Self-tests ───────────────────────────────────────────────────────
;; `(mod test …)` submodule (S87 Stage C.2): super-imports the Num operators
;; and checks Int arithmetic with assert-eq (Int has Eq + Display).

(mod test)
