;; main/math.cl -- A helper module providing arithmetic utilities
;;
;; This file is the nested child main/math.cl, so its module identity is
;; "main.math" (per spec/08-modules.md §8.2.5). It is loaded by main.cl
;; via (mod math). All public functions are accessible as main.math/name.
;;
;; A submodule does not inherit the entry module's prelude exports, so it
;; imports the primitives it uses explicitly (per spec/08-modules.md §8.3).
(import [primitives [mul-i64 add-i64 sub-i64 lt-i64]])

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
