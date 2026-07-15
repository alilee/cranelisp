;; collections/either/test.cl — self-tests for collections.either (module
;; collections.either.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`. Exercises the Either eliminators via the in-language harness.
;;
;; DEFECT (S87 Stage C.2): these tests LOAD and TYPECHECK cleanly and each
;; PASSES when called directly, but running them through the test-discovery
;; path (`discover-tests` → `run-one`) SIGBUSes on `test-is-right` — the
;; `(Either String Int)` `(Right 1)` shape (heap-ADT with String-then-Int
;; field order) corrupts in the discover-tests marshaling/GOT path. The other
;; five either tests pass individually through the runner; only the
;; String-first two-param Either shape crashes. This is a language/backend
;; defect (not a stdlib bug) — handed off to /qa for a narrow failing repro →
;; /backend. Recorded in plan-stdlib.md §26.4. The tests are kept as the
;; durable record (correct code; the crash is the compiler's).

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
