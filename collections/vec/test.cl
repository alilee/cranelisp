(import
  [super
   [count get conj assoc range vec-map vec-filter vec-reduce
    vec-reverse]])
(import [testing.assertions [assert-eq]])
(import
  [primitives
   [Option String Int add-i64 mul-i64 eq-i64 gt-i64]])
(defn test-count [] : (Option String)
  (assert-eq 3 (count [1 2 3])))
(defn test-get [] : (Option String)
  (assert-eq 20 (get [10 20 30] 1)))
(defn test-conj-grows [] : (Option String)
  (assert-eq 4 (count (conj [1 2 3] 4))))
(defn test-conj-appends-end [] : (Option String)
  (assert-eq 9 (get (conj [1 2 3] 9) 3)))
(defn test-assoc-sets [] : (Option String)
  (assert-eq 99 (get (assoc [1 2 3] 1 99) 1)))
(defn test-vec-map [] : (Option String)
  (assert-eq 4
    (get (vec-map (fn [x] (mul-i64 x 2)) [1 2 3]) 1)))
(defn test-vec-filter [] : (Option String)
  (assert-eq 2
    (count (vec-filter (fn [x] (gt-i64 x 1)) [1 2 3]))))
(defn test-vec-reduce [] : (Option String)
  (assert-eq 6
    (vec-reduce (fn [acc x] (add-i64 acc x)) 0 [1 2 3])))
(defn test-vec-reverse [] : (Option String)
  (assert-eq 1 (get (vec-reverse [1 2 3]) 2)))
(defn test-range-count [] : (Option String)
  (assert-eq 5 (count (range 0 5))))
(defn test-range-exclusive-hi [] : (Option String)
  (assert-eq 4 (get (range 0 5) 4)))
(defn test-range-start-offset [] : (Option String)
  (assert-eq 3 (get (range 3 7) 0)))
(defn test-range-empty [] : (Option String)
  (assert-eq 0 (count (range 5 5))))
(defn test-range-feeds-reduce [] : (Option String)
  (assert-eq 10
    (vec-reduce (fn [acc x] (add-i64 acc x)) 0 (range 0 5))))