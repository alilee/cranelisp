;; collections/parallel/test.cl — self-tests for collections.parallel (module
;; collections.parallel.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`. These assert SEQUENTIAL-IDENTITY: par-* must produce the same
;; result as the sequential vec-* counterparts. Because parallelism is
;; semantically transparent (pure code), correctness is checked serially —
;; the result is the contract, the speed-up is a separate, transparent property.
;; Vec results reduce to Int scalars (via count/get/vec-reduce) for assert-eq.

(import [super [par-map par-reduce par-map-reduce]])
(import [collections.vec [count get vec-map vec-reduce]])
(import [testing.assertions [assert-eq]])
(import [primitives [Option String Int add-i64 mul-i64]])

(defn- dbl "double an Int" [:Int x] :Int (mul-i64 x 2))
(defn- add "Int +" [:Int a :Int b] :Int (add-i64 a b))
(defn- mul "Int *" [:Int a :Int b] :Int (mul-i64 a b))

;; ── par-map ──────────────────────────────────────────────────────────
(defn test-par-map-count [] :(Option String)
  (assert-eq 5 (count (par-map dbl [1 2 3 4 5]))))

(defn test-par-map-elements [] :(Option String)
  ;; doubles of [1 2 3 4 5] = [2 4 6 8 10]; check first and last
  (assert-eq 2 (get (par-map dbl [1 2 3 4 5]) 0)))

(defn test-par-map-last [] :(Option String)
  (assert-eq 10 (get (par-map dbl [1 2 3 4 5]) 4)))

(defn test-par-map-empty [] :(Option String)
  (assert-eq 0 (count (par-map dbl []))))

(defn test-par-map-single [] :(Option String)
  (assert-eq 14 (get (par-map dbl [7]) 0)))

(defn test-par-map-matches-vec-map [] :(Option String)
  ;; element-for-element identical to the sequential vec-map at an interior index
  (assert-eq (get (vec-map dbl [3 1 4 1 5 9 2 6]) 5)
             (get (par-map dbl [3 1 4 1 5 9 2 6]) 5)))

;; ── par-reduce ───────────────────────────────────────────────────────
(defn test-par-reduce-sum [] :(Option String)
  (assert-eq 15 (par-reduce add 0 [1 2 3 4 5])))

(defn test-par-reduce-product [] :(Option String)
  ;; identity for * is 1
  (assert-eq 24 (par-reduce mul 1 [1 2 3 4])))

(defn test-par-reduce-empty [] :(Option String)
  (assert-eq 0 (par-reduce add 0 [])))

(defn test-par-reduce-single [] :(Option String)
  (assert-eq 42 (par-reduce add 0 [42])))

(defn test-par-reduce-odd-size [] :(Option String)
  ;; odd length exercises the uneven D&C split
  (assert-eq 28 (par-reduce add 0 [1 2 3 4 5 6 7])))

(defn test-par-reduce-matches-vec-reduce [] :(Option String)
  (assert-eq (vec-reduce add 0 [3 1 4 1 5 9 2 6])
             (par-reduce add 0 [3 1 4 1 5 9 2 6])))

;; ── par-map-reduce ───────────────────────────────────────────────────
(defn test-par-map-reduce-sum-of-doubles [] :(Option String)
  ;; sum of doubles of [1 2 3 4 5] = 2+4+6+8+10 = 30
  (assert-eq 30 (par-map-reduce dbl add 0 [1 2 3 4 5])))

(defn test-par-map-reduce-empty [] :(Option String)
  (assert-eq 0 (par-map-reduce dbl add 0 [])))

(defn test-par-map-reduce-single [] :(Option String)
  (assert-eq 14 (par-map-reduce dbl add 0 [7])))

(defn test-par-map-reduce-matches-seq [] :(Option String)
  ;; identical to the sequential vec-reduce ∘ vec-map composition
  (assert-eq (vec-reduce add 0 (vec-map dbl [3 1 4 1 5 9 2 6]))
             (par-map-reduce dbl add 0 [3 1 4 1 5 9 2 6])))
