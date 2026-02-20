(mod numerics)
(mod collections)
(import [primitives [*] numerics [*] collections [*]])

;; ── Seq Type ────────────────────────────────────────

(deftype (Seq a) "A lazy sequence with thunked tail"
  (SeqNil "Empty lazy sequence")
  (SeqCons "Lazy sequence node with head and thunked rest" [:a head :(Fn [] (Seq a)) rest]))

(impl Functor Seq
  (defn fmap [f s]
    (match s
      [SeqNil SeqNil
       (SeqCons h t) (SeqCons (f h) (fn [] (fmap f (t))))])))

;; ── Lazy Operations ─────────────────────────────────

(defn lazy-filter "Filter a lazy sequence by predicate" [pred s]
  (match s
    [SeqNil SeqNil
     (SeqCons h t)
      (if (pred h)
        (SeqCons h (fn [] (lazy-filter pred (t))))
        (lazy-filter pred (t)))]))

(defn lazy-take "Take first n elements from lazy sequence" [:Int n s]
  (if (<= n 0) SeqNil
    (match s
      [SeqNil SeqNil
       (SeqCons h t) (SeqCons h (fn [] (lazy-take (- n 1) (t))))])))

(defn lazy-drop "Drop first n elements from lazy sequence" [:Int n s]
  (if (<= n 0) s
    (match s
      [SeqNil SeqNil
       (SeqCons h t) (lazy-drop (- n 1) (t))])))

(defn lazy-reduce "Reduce a lazy sequence with function and initial accumulator" [f init s]
  (match s
    [SeqNil init
     (SeqCons h t) (lazy-reduce f (f init h) (t))]))

;; ── Producers ───────────────────────────────────────

(defn range-from "Infinite lazy sequence starting at n" [:Int n]
  (SeqCons n (fn [] (range-from (+ n 1)))))

(defn iterate "Infinite lazy sequence: x, (f x), (f (f x)), ..." [f x]
  (SeqCons x (fn [] (iterate f (f x)))))

(defn repeat "Infinite lazy sequence of x" [x]
  (SeqCons x (fn [] (repeat x))))

;; ── Conversions ─────────────────────────────────────

(defn to-list "Force entire lazy sequence into a list" [s]
  (match s
    [SeqNil Nil
     (SeqCons h t) (Cons h (to-list (t)))]))

(defn vec-to-seq "Convert vec to lazy sequence starting at index" [:Int idx v]
  (if (>= idx (vec-len v)) SeqNil
    (SeqCons (vec-get v idx) (fn [] (vec-to-seq (+ idx 1) v)))))

(defn list-to-seq "Convert list to lazy sequence" [xs]
  (match xs
    [Nil SeqNil
     (Cons h t) (SeqCons h (fn [] (list-to-seq t)))]))

(defn seq "Convert collection to lazy sequence"
  ([v] (vec-to-seq 0 v))
  ([l] (list-to-seq l)))

;; ── Unified API ─────────────────────────────────────

(defn map "Apply function to each element, returning lazy sequence"
  ([f v] (fmap f (vec-to-seq 0 v)))
  ([f l] (fmap f (list-to-seq l)))
  ([f s] (match s
           [SeqNil (fmap f SeqNil)
            _ (fmap f s)])))

(defn filter "Return lazy sequence of elements matching predicate"
  ([pred v] (lazy-filter pred (vec-to-seq 0 v)))
  ([pred l] (lazy-filter pred (list-to-seq l)))
  ([pred s] (lazy-filter pred s)))

(defn take "Take first n elements as lazy sequence"
  ([:Int n v] (lazy-take n (vec-to-seq 0 v)))
  ([:Int n l] (lazy-take n (list-to-seq l)))
  ([:Int n s] (lazy-take n s)))

(defn drop "Drop first n elements, return rest as lazy sequence"
  ([:Int n v] (lazy-drop n (vec-to-seq 0 v)))
  ([:Int n l] (lazy-drop n (list-to-seq l)))
  ([:Int n s] (lazy-drop n s)))

(defn reduce "Reduce collection to single value with function and initial accumulator"
  ([f init v] (lazy-reduce f init (vec-to-seq 0 v)))
  ([f init l] (lazy-reduce f init (list-to-seq l)))
  ([f init s] (lazy-reduce f init s)))
