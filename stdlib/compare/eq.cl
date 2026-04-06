;; compare/eq.cl — Eq trait and primitive impls
;;
;; The Eq trait defines equality comparison. All types that support equality
;; testing implement this trait.
;;
;; Spec: 07-traits.md §7.1

(import [prelude []])
(import [primitives [*]])

(deftrait Eq
  (= [self self] Bool)
  (!= [self self] Bool))

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
