;; compare/ord.cl — Ord trait and primitive impls
;;
;; The Ord trait defines ordering comparisons. Types that support ordering
;; (less-than, greater-than, etc.) implement this trait.
;;
;; Spec: 07-traits.md §7.1

(import [prelude []])
(import [primitives [*]])

(deftrait Ord
  (< [a b] Bool)
  (> [a b] Bool)
  (<= [a b] Bool)
  (>= [a b] Bool))

(impl Ord Int
  (defn < [a b] (lt-i64 a b))
  (defn > [a b] (gt-i64 a b))
  (defn <= [a b] (le-i64 a b))
  (defn >= [a b] (ge-i64 a b)))

(impl Ord Float
  (defn < [a b] (lt-f64 a b))
  (defn > [a b] (gt-f64 a b))
  (defn <= [a b] (le-f64 a b))
  (defn >= [a b] (ge-f64 a b)))
