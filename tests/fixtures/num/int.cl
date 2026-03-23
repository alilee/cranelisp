;; Test fixture: num/int.cl — minimal Int operations for e2e tests.
;; NOT a copy of stdlib/num/int.cl — only provides what tests need.

(defn rem "Integer remainder" [:Int a :Int b] :Int
  (sub-i64 a (mul-i64 (div-i64 a b) b)))

(defn even? "Test if an integer is even" [:Int x] :Bool
  (eq-i64 (rem x 2) 0))

(defn odd? "Test if an integer is odd" [:Int x] :Bool
  (not (eq-i64 (rem x 2) 0)))
