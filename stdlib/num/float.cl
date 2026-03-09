;; num/float.cl — Float operations
;;
;; Float-specific functions built on Ring 0/1 primitives.
;; No floor/ceil/round primitives exist yet — these would require
;; runtime extern functions. This module provides what can be built
;; from existing primitives.
;;
;; Spec: plan-stdlib.md §3.3

(defn abs-float "Absolute value of a float"
  [:Float x] :Float
  (if (lt-f64 x 0.0) (sub-f64 0.0 x) x))

(defn sign-float "Sign of a float: -1.0, 0.0, or 1.0"
  [:Float x] :Float
  (if (lt-f64 x 0.0) -1.0
    (if (gt-f64 x 0.0) 1.0 0.0)))

(defn negate-float "Negate a float"
  [:Float x] :Float
  (sub-f64 0.0 x))

(defn min-float "Return the smaller of two floats"
  [:Float a :Float b] :Float
  (if (lt-f64 a b) a b))

(defn max-float "Return the larger of two floats"
  [:Float a :Float b] :Float
  (if (gt-f64 a b) a b))

(defn clamp-float "Clamp a float to the range [lo, hi]"
  [:Float x :Float lo :Float hi] :Float
  (if (lt-f64 x lo) lo
    (if (gt-f64 x hi) hi x)))
