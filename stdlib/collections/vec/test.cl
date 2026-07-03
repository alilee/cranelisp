;; collections/vec/test.cl — self-tests for collections.vec (module
;; collections.vec.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod test)`. Exercises the curated Clojure verbs (count/get/conj/assoc),
;; the vec combinators, and the new eager `range` (gap G3). Vec values reduce
;; to Int scalars (count/get/vec-reduce) for assert-eq.

(import [super [count get conj assoc range vec-map vec-filter vec-reduce vec-reverse vec-concat]])
(import [testing.assertions [assert-eq]])
(import [primitives [Option String Int Vec add-i64 mul-i64 eq-i64 gt-i64]])

(defn test-count [] :(Option String)
  (assert-eq 3 (count [1 2 3])))

(defn test-get [] :(Option String)
  (assert-eq 20 (get [10 20 30] 1)))

(defn test-conj-grows [] :(Option String)
  (assert-eq 4 (count (conj [1 2 3] 4))))

(defn test-conj-appends-end [] :(Option String)
  (assert-eq 9 (get (conj [1 2 3] 9) 3)))

(defn test-assoc-sets [] :(Option String)
  (assert-eq 99 (get (assoc [1 2 3] 1 99) 1)))

(defn test-vec-map [] :(Option String)
  (assert-eq 4 (get (vec-map (fn [x] (mul-i64 x 2)) [1 2 3]) 1)))

(defn test-vec-filter [] :(Option String)
  (assert-eq 2 (count (vec-filter (fn [x] (gt-i64 x 1)) [1 2 3]))))

(defn test-vec-reduce [] :(Option String)
  (assert-eq 6 (vec-reduce (fn [acc x] (add-i64 acc x)) 0 [1 2 3])))

(defn test-vec-reverse [] :(Option String)
  (assert-eq 1 (get (vec-reverse [1 2 3]) 2)))

;; vec-concat — S101 6b. The composed shapes (count/get over the result)
;; double as the guard for the held fold-body simplification: with
;; `(vec-reduce vec-push va vb)` as the body they fail codegen
;; ("undefined function: count") — see vec.cl §vec-concat NOTE(0488-family).
;; The empty-vec rows guard harder still: under the fold body they fail
;; TYPECHECK ("ambiguous type", annotation does not pin), aborting cold
;; prelude compile at REPL startup. Under the landed loop body both rows
;; compile cold with OR without the :(Vec Int) pins (the sibling literal
;; unifies `a`); the pins are kept as S84-defensive documentation.
(defn test-vec-concat-length [] :(Option String)
  (assert-eq 5 (count (vec-concat [1 2] [3 4 5]))))

(defn test-vec-concat-order [] :(Option String)
  (assert-eq 3 (get (vec-concat [1 2] [3 4 5]) 2)))

(defn test-vec-concat-empty-left [] :(Option String)
  (assert-eq 7 (get (vec-concat :(Vec Int) [] [7 8]) 0)))

(defn test-vec-concat-empty-right [] :(Option String)
  (assert-eq 2 (count (vec-concat [1 2] :(Vec Int) []))))

;; vec-flatten — self-test OWED, held per the green-self-test convention:
;; vec-flatten is unusable from user code today (FIXME 0488 — same-module
;; generic `vec-concat` passed as a value to `vec-reduce` loses its mono
;; instance at the consuming turn; /qa failing guard is the durable
;; record). Add `test-vec-flatten` rows here when 0488's fix lands.

;; range — G3
(defn test-range-count [] :(Option String)
  (assert-eq 5 (count (range 0 5))))

(defn test-range-exclusive-hi [] :(Option String)
  (assert-eq 4 (get (range 0 5) 4)))

(defn test-range-start-offset [] :(Option String)
  (assert-eq 3 (get (range 3 7) 0)))

(defn test-range-empty [] :(Option String)
  (assert-eq 0 (count (range 5 5))))

(defn test-range-feeds-reduce [] :(Option String)
  (assert-eq 10 (vec-reduce (fn [acc x] (add-i64 acc x)) 0 (range 0 5))))
