;; num/num/test.cl — self-tests for num.num (module num.num.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`. `num.num` is not a harness dependency, so assert-eq is used
;; (Int has Eq + Display).

(import [super [Num + - * /]])
(import [testing.assertions [assert-eq]])
(import [primitives [Option String]])

(defn test-int-add [] :(Option String)
  (assert-eq 5 (+ 2 3)))

(defn test-int-sub [] :(Option String)
  (assert-eq 1 (- 4 3)))

(defn test-int-mul [] :(Option String)
  (assert-eq 6 (* 2 3)))

(defn test-int-div [] :(Option String)
  (assert-eq 4 (/ 12 3)))
