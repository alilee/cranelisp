;; num/int/test.cl — self-tests for num.int (module num.int.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod test)`. Exercises the Int helpers via the in-language harness.

(import [super [rem abs sign negate even? odd? min-int max-int clamp]])
(import [testing.assertions [assert-true assert-false assert-eq]])
(import [primitives [Option String]])

(defn test-rem [] :(Option String)
  (assert-eq 1 (rem 7 3)))

(defn test-abs-neg [] :(Option String)
  (assert-eq 5 (abs -5)))

(defn test-sign-neg [] :(Option String)
  (assert-eq -1 (sign -9)))

(defn test-negate [] :(Option String)
  (assert-eq -4 (negate 4)))

(defn test-even [] :(Option String)
  (assert-true (even? 4)))

(defn test-odd [] :(Option String)
  (assert-true (odd? 7)))

(defn test-not-even [] :(Option String)
  (assert-false (even? 3)))

(defn test-min [] :(Option String)
  (assert-eq 2 (min-int 2 5)))

(defn test-max [] :(Option String)
  (assert-eq 5 (max-int 2 5)))

(defn test-clamp-hi [] :(Option String)
  (assert-eq 9 (clamp 12 0 9)))
