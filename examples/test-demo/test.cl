(import [super [*]])

(import [testing [*]])

(defn test-add []
  (check (assert-eq 7 (add 3 4)) (assert-eq 0 (add 0 0))
    (assert-eq -1 (add 1 -2))))

(defn test-double []
  (check (assert-eq 10 (double 5)) (assert-eq 0 (double 0))
    (assert-eq -4 (double -2))))
