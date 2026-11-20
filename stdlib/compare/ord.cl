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

;; Bool ordering: false < true (the conventional total order on Bool).
(impl Ord Bool
  (defn < [a b] (if a false b))
  (defn > [a b] (if b false a))
  (defn <= [a b] (if a b true))
  (defn >= [a b] (if b a true)))

;; ── The seeded data types ─────────────────────────────────────────────
;; `Option`, `Result` and `Pair` are seeded by `primitives`, so their impls
;; live with the trait. As with `derive-Ord`, constructor declaration order is
;; the order (`None` < `Some`, `Ok` < `Err`), payloads of one constructor
;; compare by their own `<`, and a `Pair` compares lexicographically. Only `<`
;; is structural; the other three are expressed in terms of it, so they cannot
;; disagree with it and no `Eq` impl is required.

(impl Ord (Option :Ord a)
  (defn < [x y]
    (match x
      [None (match y [None false _ true])
       (Some u) (match y [(Some v) (< u v) _ false])]))
  (defn > [x y] (< y x))
  (defn <= [x y] (if (< y x) false true))
  (defn >= [x y] (if (< x y) false true)))

(impl Ord (Result :Ord a :Ord e)
  (defn < [x y]
    (match x
      [(Ok u) (match y [(Ok v) (< u v) _ true])
       (Err u) (match y [(Err v) (< u v) _ false])]))
  (defn > [x y] (< y x))
  (defn <= [x y] (if (< y x) false true))
  (defn >= [x y] (if (< x y) false true)))

(impl Ord (Pair :Ord a :Ord b)
  (defn < [x y]
    (match x
      [(Pair x1 x2)
       (match y
         [(Pair y1 y2) (if (< x1 y1) true (if (< y1 x1) false (< x2 y2)))])]))
  (defn > [x y] (< y x))
  (defn <= [x y] (if (< y x) false true))
  (defn >= [x y] (if (< x y) false true)))

;; ── Self-tests ───────────────────────────────────────────────────────
;; `(mod- test …)` submodule (S87 Stage C.2): super-imports the Ord methods
;; and exercises Int + Bool ordering. (String ordering is omitted by design,
;; see the note below, so there is no String self-test.)

(mod- test)

;; NOTE: `Ord String` is intentionally NOT implemented. Lexicographic
;; string ordering needs a code-point comparison primitive (a `char→int`
;; or `str-lt` style code-unit test). The string primitive surface
;; (`char-at`/`substring`/`str-eq`/`str-len`/`starts-with?`/`contains?` …)
;; can test character EQUALITY but has no way to order two differing
;; characters. `Eq String` (in compare/eq.cl) covers equality; ordering of
;; strings is blocked on a missing primitive — tracked as a usability
;; finding (see plan-stdlib.md §"Known blockers"). Adding a bogus
;; substring-based order would be silently wrong, so it is omitted.
