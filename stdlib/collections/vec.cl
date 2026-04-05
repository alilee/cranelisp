;; collections/vec.cl — Vec utility functions and construction macro
;;
;; Higher-level operations on Vec, built on the primitives:
;;   vec-len, vec-get, vec-set, vec-push
;;
;; Also provides the `vec` construction macro.
;;
;; Spec: plan-stdlib.md §3.3

(import [prelude []])

(import [macros [SexpBracket SList]])

(defmacro vec "Construct a vec from elements" [&elems]
  (SexpBracket elems))

(defn vec-map "Apply a function to each element of a Vec"
  [f v]
  (vec-map-loop f v (vec-len v) 0 []))

(defn- vec-map-loop "Tail-recursive helper for vec-map"
  [f v :Int len :Int i acc]
  (if (ge-i64 i len) acc
    (vec-map-loop f v len (add-i64 i 1) (vec-push acc (f (vec-get v i))))))

(defn vec-filter "Keep only elements satisfying the predicate"
  [pred v]
  (vec-filter-loop pred v (vec-len v) 0 []))

(defn- vec-filter-loop "Tail-recursive helper for vec-filter"
  [pred v :Int len :Int i acc]
  (if (ge-i64 i len) acc
    (let [x (vec-get v i)]
      (if (pred x)
        (vec-filter-loop pred v len (add-i64 i 1) (vec-push acc x))
        (vec-filter-loop pred v len (add-i64 i 1) acc)))))

(defn vec-reduce "Reduce a Vec to a single value with a function and initial accumulator"
  [f init v]
  (vec-reduce-loop f init v (vec-len v) 0))

(defn- vec-reduce-loop "Tail-recursive helper for vec-reduce"
  [f acc v :Int len :Int i]
  (if (ge-i64 i len) acc
    (vec-reduce-loop f (f acc (vec-get v i)) v len (add-i64 i 1))))

(defn vec-reverse "Reverse a Vec"
  [v]
  (vec-reverse-loop v (vec-len v) (sub-i64 (vec-len v) 1) []))

(defn- vec-reverse-loop "Tail-recursive helper for vec-reverse"
  [v :Int len :Int i acc]
  (if (lt-i64 i 0) acc
    (vec-reverse-loop v len (sub-i64 i 1) (vec-push acc (vec-get v i)))))

(defn vec-any? "Test if any element of a Vec satisfies the predicate"
  [pred v]
  (vec-any-loop pred v (vec-len v) 0))

(defn- vec-any-loop "Tail-recursive helper for vec-any?"
  [pred v :Int len :Int i]
  (if (ge-i64 i len) false
    (if (pred (vec-get v i)) true
      (vec-any-loop pred v len (add-i64 i 1)))))

(defn vec-all? "Test if all elements of a Vec satisfy the predicate"
  [pred v]
  (vec-all-loop pred v (vec-len v) 0))

(defn- vec-all-loop "Tail-recursive helper for vec-all?"
  [pred v :Int len :Int i]
  (if (ge-i64 i len) true
    (if (pred (vec-get v i))
      (vec-all-loop pred v len (add-i64 i 1))
      false)))

(defn vec-for-each "Apply a function to each element for side effects, return unit"
  [f v]
  (vec-for-each-loop f v (vec-len v) 0))

(defn- vec-for-each-loop "Tail-recursive helper for vec-for-each"
  [f v :Int len :Int i]
  (if (ge-i64 i len) 0
    (let [_ (f (vec-get v i))]
      (vec-for-each-loop f v len (add-i64 i 1)))))

(defn vec-zip-with "Combine two Vecs element-wise with a function"
  [f va vb]
  (let [len (if (lt-i64 (vec-len va) (vec-len vb)) (vec-len va) (vec-len vb))]
    (vec-zip-loop f va vb len 0 [])))

(defn- vec-zip-loop "Tail-recursive helper for vec-zip-with"
  [f va vb :Int len :Int i acc]
  (if (ge-i64 i len) acc
    (vec-zip-loop f va vb len (add-i64 i 1)
      (vec-push acc (f (vec-get va i) (vec-get vb i))))))

(defn vec-concat "Concatenate two Vecs"
  [va vb]
  (vec-concat-loop va vb (vec-len vb) 0))

(defn- vec-concat-loop "Tail-recursive helper for vec-concat"
  [acc vb :Int len :Int i]
  (if (ge-i64 i len) acc
    (vec-concat-loop (vec-push acc (vec-get vb i)) vb len (add-i64 i 1))))

(defn vec-flatten "Flatten a Vec of Vecs into a single Vec"
  [vv]
  (vec-reduce vec-concat [] vv))
