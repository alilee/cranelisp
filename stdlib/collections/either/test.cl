;; collections/either/test.cl — self-tests for collections.either (module
;; collections.either.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`. Exercises the Either eliminators via the in-language harness.
;;
;; `test-is-right` guards the `(Either String Int)` `(Right 1)` shape, a heap
;; ADT with String-then-Int field order, through the discovery path; keep it.

(import [super [Either Left Right is-left? is-right? from-left from-right
                map-left either]])
(import [testing.assertions [assert-true assert-false assert-eq]])
(import [compare.eq [= !=]])
(import [compare.ord [< <=]])
(import [text.display [show]])
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

;; ── Trait impls ──────────────────────────────────────────────────────

(defn test-eq-same-side-same-value [] :(Option String)
  (assert-true (= :(Either Int String) (Left 1) (Left 1))))

(defn test-eq-value-differs [] :(Option String)
  (assert-true (!= :(Either Int String) (Right "a") (Right "b"))))

(defn test-eq-side-differs [] :(Option String)
  (assert-false (= :(Either Int Int) (Left 1) (Right 1))))

(defn test-ord-left-lt-right [] :(Option String)
  (assert-true (< :(Either Int Int) (Left 9) (Right 0))))

(defn test-ord-right-not-lt-left [] :(Option String)
  (assert-false (< :(Either Int Int) (Right 0) (Left 9))))

(defn test-ord-payload-decides [] :(Option String)
  (assert-true (< :(Either Int Int) (Right 1) (Right 2))))

(defn test-ord-le-when-equal [] :(Option String)
  (assert-true (<= :(Either Int Int) (Left 3) (Left 3))))

(defn test-show-left [] :(Option String)
  (assert-eq "Left(1)" (show :(Either Int String) (Left 1))))

(defn test-show-right [] :(Option String)
  (assert-eq "Right(a)" (show :(Either Int String) (Right "a"))))
