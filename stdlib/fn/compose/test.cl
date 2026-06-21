;; fn/compose/test.cl — self-tests for fn.compose (module fn.compose.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod test)`. Exercises the combinators via the in-language harness.

(import [super [identity compose pipe flip]])
(import [testing.assertions [assert-eq]])
(import [primitives [Option String Int add-i64 mul-i64 sub-i64]])

(defn- inc [:Int x] :Int (add-i64 x 1))
(defn- dbl [:Int x] :Int (mul-i64 x 2))

(defn test-identity [] :(Option String)
  (assert-eq 7 (identity 7)))

(defn test-compose [] :(Option String)
  ;; (compose inc dbl) 3 = inc(dbl(3)) = 7
  (assert-eq 7 ((compose inc dbl) 3)))

(defn test-pipe [] :(Option String)
  ;; (pipe inc dbl) 3 = dbl(inc(3)) = 8
  (assert-eq 8 ((pipe inc dbl) 3)))

(defn test-flip [] :(Option String)
  ;; (flip sub-i64) 3 10 = sub-i64(10, 3) = 7
  (assert-eq 7 ((flip sub-i64) 3 10)))
