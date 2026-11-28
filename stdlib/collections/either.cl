;; collections/either.cl — Either type
;;
;; A generic two-way sum type. Left and Right carry values of different types.
;; Used when a function can produce one of two unrelated result types.
;;
;; Spec: plan-stdlib.md §3.3

(import [prelude []])
(import [primitives [str-concat]])
(import [compare.eq [Eq =]])
(import [compare.ord [Ord <]])
(import [text.display [Display show]])

(deftype (Either a b) (Left [:a left-val]) (Right [:b right-val]))

(defn is-left? "Test if an Either is Left" [e]
  (match e
    [(Left _) true
     (Right _) false]))

(defn is-right? "Test if an Either is Right" [e]
  (match e
    [(Left _) false
     (Right _) true]))

(defn from-left "Extract Left value or return default" [default e]
  (match e
    [(Left v) v
     (Right _) default]))

(defn from-right "Extract Right value or return default" [default e]
  (match e
    [(Left _) default
     (Right v) v]))

(defn map-left "Apply function to Left value, pass through Right" [f e]
  (match e
    [(Left v) (Left (f v))
     (Right v) (Right v)]))

(defn map-right "Apply function to Right value, pass through Left" [f e]
  (match e
    [(Left v) (Left v)
     (Right v) (Right (f v))]))

(defn either "Eliminate an Either: apply f to Left or g to Right" [f g e]
  (match e
    [(Left v) (f v)
     (Right v) (g v)]))

;; ── Trait impls ──────────────────────────────────────────────────────
;; As with `derive`: same constructor and equal payloads for `=`; declaration
;; order (`Left` < `Right`) then the payload's `<` for `Ord`; and `Left(1)` /
;; `Right(a)` for `show`.

(impl Eq (Either :Eq a :Eq b)
  (defn = [x y]
    (match x
      [(Left u) (match y [(Left v) (= u v) _ false])
       (Right u) (match y [(Right v) (= u v) _ false])]))
  (defn != [x y] (if (= x y) false true)))

(impl Ord (Either :Ord a :Ord b)
  (defn < [x y]
    (match x
      [(Left u) (match y [(Left v) (< u v) _ true])
       (Right u) (match y [(Right v) (< u v) _ false])]))
  (defn > [x y] (< y x))
  (defn <= [x y] (if (< y x) false true))
  (defn >= [x y] (if (< x y) false true)))

(impl Display (Either :Display a :Display b)
  (defn show [self]
    (match self
      [(Left u) (str-concat "Left(" (str-concat (show u) ")"))
       (Right u) (str-concat "Right(" (str-concat (show u) ")"))])))

;; ── Self-tests ───────────────────────────────────────────────────────
;; Backing file `collections/either/test.cl`: exercises the Either eliminators
;; with the in-language harness.

(mod- test)  ;; body in either/test.cl (extraction-stable backing file, spec §8.2.5)
