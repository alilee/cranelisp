;; math.cl -- A helper module providing arithmetic utilities
;;
;; This module is loaded by main.cl via (mod math).
;; All public functions are accessible as math/name from main.

;; Double a value
(defn double [x] (mul-i64 x 2))

;; Triple a value
(defn triple [x] (mul-i64 x 3))

;; Square a value
(defn square [x] (mul-i64 x x))

;; Absolute value
(defn abs [x]
  (if (lt-i64 x 0) (sub-i64 0 x) x))

;; Sum of squares
(defn sum-of-squares [a b]
  (add-i64 (mul-i64 a a) (mul-i64 b b)))
