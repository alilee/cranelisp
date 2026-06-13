;; 08-floats.cl -- Float literals and arithmetic
;;
;; Cranelisp floats are IEEE 754 double-precision (64-bit) values.
;; Ring 0 uses monomorphic named primitives for float operations:
;;   add-f64, sub-f64, mul-f64, div-f64
;;   eq-f64, lt-f64, gt-f64, le-f64, ge-f64
;;
;; Int and Float are separate types. You cannot mix them in the same
;; primitive call -- (add-i64 1 1.5) is a type error.
;;
;; Since Ring 0 batch programs return i64, this example uses float
;; comparisons to produce Bool results, then converts to Int for output.

;; Helper: convert Bool to Int for aggregation
(defn bool-to-int [b] (if b 1 0))

;; Basic float arithmetic checks
;; 1.5 + 2.5 = 4.0, so (eq-f64 (add-f64 1.5 2.5) 4.0) is true
(defn test-add []
  (bool-to-int (eq-f64 (add-f64 1.5 2.5) 4.0)))

;; 10.0 - 3.5 = 6.5
(defn test-sub []
  (bool-to-int (eq-f64 (sub-f64 10.0 3.5) 6.5)))

;; 3.0 * 4.0 = 12.0
(defn test-mul []
  (bool-to-int (eq-f64 (mul-f64 3.0 4.0) 12.0)))

;; 10.0 / 2.0 = 5.0
(defn test-div []
  (bool-to-int (eq-f64 (div-f64 10.0 2.0) 5.0)))

;; Float comparisons
(defn test-lt [] (bool-to-int (lt-f64 1.0 2.0)))
(defn test-gt [] (bool-to-int (gt-f64 3.0 2.0)))
(defn test-le [] (bool-to-int (le-f64 2.0 2.0)))
(defn test-ge [] (bool-to-int (ge-f64 1.0 2.0)))

;; Negation via subtraction from zero (no float-neg primitive)
(defn test-neg []
  (bool-to-int (eq-f64 (sub-f64 0.0 3.14) -3.14)))

;; A float function: compute the area of a circle (pi * r * r)
;; We approximate pi as 3.14159 and check a known case: r=1.0
(defn circle-area [r]
  (mul-f64 3.14159 (mul-f64 r r)))

(defn test-area []
  (bool-to-int (gt-f64 (circle-area 1.0) 3.0)))

;; Expected: 1+1+1+1+1+1+1+0+1+1 = 9
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-add)
      (add-i64 (test-sub)
        (add-i64 (test-mul)
          (add-i64 (test-div)
            (add-i64 (test-lt)
              (add-i64 (test-gt)
                (add-i64 (test-le)
                  (add-i64 (test-ge)
                    (add-i64 (test-neg)
                             (test-area))))))))))))
