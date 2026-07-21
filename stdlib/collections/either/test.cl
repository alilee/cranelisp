;; collections/either/test.cl — self-tests for collections.either (module
;; collections.either.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`. Exercises the Either eliminators via the in-language harness.
;;
;; RETIRED RECORD (verified S115 6b). This header carried an S87 Stage-C.2
;; defect note: running these tests through the discovery path
;; (`discover-tests` → `run-one`) was said to SIGBUS on `test-is-right` — the
;; `(Either String Int)` `(Right 1)` shape, a heap-ADT with String-then-Int
;; field order — while each test passed when called directly. That crash is
;; GONE: the full module runs 6 passed / 0 failed / 0 panicked through the
;; discovery path, reproducibly. The note is retired rather than left standing,
;; because a stale "this crashes" record on green code teaches the next reader
;; to distrust a working surface. `test-is-right` below IS the standing guard
;; for the shape that used to crash — keep it.

(import [super [Either Left Right is-left? is-right? from-left from-right
                map-left either]])
(import [testing.assertions [assert-true assert-false assert-eq]])
(import [primitives [Option String Int add-i64]])

(defn test-is-left [] :(Option String)
  (assert-true (is-left? :(Either Int String) (Left 1))))

(defn test-is-right [] :(Option String)
  (assert-true (is-right? :(Either String Int) (Right 1))))

(defn test-left-not-right [] :(Option String)
  (assert-false (is-right? :(Either Int String) (Left 1))))

(defn test-from-left [] :(Option String)
  (assert-eq 7 (from-left 0 :(Either Int String) (Left 7))))

(defn test-from-right-default [] :(Option String)
  (assert-eq "d" (from-right "d" :(Either Int String) (Left 7))))

(defn- inc [:Int x] :Int (add-i64 x 1))

(defn test-either-left [] :(Option String)
  (assert-eq 2 (either inc inc :(Either Int Int) (Left 1))))
