;; 02-booleans.cl -- Boolean literals, comparisons, and conditionals
;;
;; Booleans are true or false. Comparison primitives return Bool.
;; Ring 0 comparison primitives:
;;   eq-i64, lt-i64, gt-i64, le-i64, ge-i64  (Int -> Int -> Bool)
;;   not                                      (Bool -> Bool)
;;
;; The if expression: (if condition then-expr else-expr)
;; Both branches must have the same type. Condition must be Bool.

;; Encode booleans as integers for the result (1 = true, 0 = false)
(defn bool-to-int [b] (if b 1 0))

;; Equality
(defn test-eq [] (bool-to-int (eq-i64 5 5)))

;; Inequality (not equal)
(defn test-neq [] (bool-to-int (not (eq-i64 1 2))))

;; Less than
(defn test-lt [] (bool-to-int (lt-i64 2 3)))

;; Greater than
(defn test-gt [] (bool-to-int (gt-i64 5 3)))

;; Less than or equal
(defn test-le [] (bool-to-int (le-i64 3 3)))

;; Greater than or equal
(defn test-ge [] (bool-to-int (ge-i64 4 5)))

;; Nested if: classify a number as positive (1), zero (0), or negative (-1)
(defn sign [n]
  (if (lt-i64 n 0)
    -1
    (if (eq-i64 n 0) 0 1)))

;; Combine results: 1 + 1 + 1 + 1 + 1 + 0 + 1 + 0 + (-1) = 5
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-eq)
      (add-i64 (test-neq)
        (add-i64 (test-lt)
          (add-i64 (test-gt)
            (add-i64 (test-le)
              (add-i64 (test-ge)
                (add-i64 (sign 42)
                  (add-i64 (sign 0)
                           (sign -7)))))))))))
