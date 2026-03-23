;; 27-lazy-seq.cl -- Lazy sequences with thunked tails
;;
;; A lazy sequence defers computation using thunks (zero-argument
;; closures). The Seq type has two constructors:
;;
;;   SeqNil                          -- empty sequence
;;   (SeqCons head (fn [] ...rest))  -- head value + thunked tail
;;
;; The tail is a closure that produces the next Seq when called.
;; This means infinite sequences are representable -- only the
;; elements you consume are ever computed.
;;
;; Producers create lazy sequences:
;;   range-from n    -- n, n+1, n+2, ... (infinite)
;;   iterate f x     -- x, (f x), (f (f x)), ... (infinite)
;;   repeat x        -- x, x, x, ... (infinite)
;;
;; Consumers force evaluation:
;;   seq-take n s    -- collect first n elements into a Vec
;;   seq-reduce f init s  -- left fold over a finite sequence
;;
;; This example defines the Seq type and operations inline.
;; The standard library provides these in the seq module.

;; --- The Seq type ---

(deftype (Seq a)
  SeqNil
  (SeqCons [:a head :(Fn [] (Seq a)) rest]))

;; --- Producers ---

;; Infinite sequence of integers: n, n+1, n+2, ...
(defn range-from [:Int n]
  (SeqCons n (fn [] (range-from (add-i64 n 1)))))

;; Infinite sequence: x, (f x), (f (f x)), ...
(defn iterate [f x]
  (SeqCons x (fn [] (iterate f (f x)))))

;; Infinite constant sequence: x, x, x, ...
(defn repeat [x]
  (SeqCons x (fn [] (repeat x))))

;; --- Consumers ---

;; Take the first n elements into a Vec
(defn seq-take [:Int n s]
  (seq-take-acc n s []))

(defn seq-take-acc [:Int n s acc]
  (if (le-i64 n 0) acc
    (match s
      [SeqNil acc
       (SeqCons h t) (seq-take-acc (sub-i64 n 1) (t) (vec-push acc h))])))

;; Left fold over a (finite) lazy sequence
(defn seq-reduce [f init s]
  (match s
    [SeqNil init
     (SeqCons h t) (seq-reduce f (f init h) (t))]))

;; Drop the first n elements
(defn seq-drop [:Int n s]
  (if (le-i64 n 0) s
    (match s
      [SeqNil SeqNil
       (SeqCons _ t) (seq-drop (sub-i64 n 1) (t))])))

;; Get the nth element (0-indexed)
(defn seq-nth [:Int n s]
  (match s
    [SeqNil (sub-i64 0 1)
     (SeqCons h t) (if (eq-i64 n 0) h (seq-nth (sub-i64 n 1) (t)))]))

;; Apply a function to each element (lazy)
(defn seq-map [f s]
  (match s
    [SeqNil SeqNil
     (SeqCons h t) (SeqCons (f h) (fn [] (seq-map f (t))))]))

;; --- Tests ---

;; Take 5 from range-from 0: [0, 1, 2, 3, 4]
;; Sum = 0+1+2+3+4 = 10
(defn test-range-take []
  (let [v (seq-take 5 (range-from 0))]
    (add-i64 (vec-get v 0)
      (add-i64 (vec-get v 1)
        (add-i64 (vec-get v 2)
          (add-i64 (vec-get v 3)
                   (vec-get v 4)))))))                      ;; -> 10

;; Sum first 10 integers (1..10) via reduce
;; 1+2+3+4+5+6+7+8+9+10 = 55
(defn test-range-reduce []
  (seq-reduce (fn [acc x] (add-i64 acc x)) 0
    (seq-take-as-seq 10 (range-from 1))))                   ;; -> 55

;; Helper: take n elements but return as a Seq (not Vec)
(defn seq-take-as-seq [:Int n s]
  (if (le-i64 n 0) SeqNil
    (match s
      [SeqNil SeqNil
       (SeqCons h t) (SeqCons h (fn [] (seq-take-as-seq (sub-i64 n 1) (t))))])))

;; iterate: powers of 2 (1, 2, 4, 8, 16, 32, ...)
;; 6th element (index 5) = 32
(defn test-iterate []
  (seq-nth 5 (iterate (fn [x] (mul-i64 x 2)) 1)))          ;; -> 32

;; repeat: constant sequence
;; Take 3 of (repeat 7), sum = 21
(defn test-repeat []
  (let [v (seq-take 3 (repeat 7))]
    (add-i64 (vec-get v 0)
      (add-i64 (vec-get v 1)
               (vec-get v 2)))))                            ;; -> 21

;; seq-map: double each element of range
;; range-from 1 => 1,2,3,4,5,...
;; seq-map double => 2,4,6,8,10,...
;; take 4 => [2,4,6,8], sum = 20
(defn test-seq-map []
  (let [doubled (seq-map (fn [x] (mul-i64 x 2)) (range-from 1))
        v (seq-take 4 doubled)]
    (add-i64 (vec-get v 0)
      (add-i64 (vec-get v 1)
        (add-i64 (vec-get v 2)
                 (vec-get v 3))))))                         ;; -> 20

;; seq-drop: skip first 5, then take element
;; range-from 0 => 0,1,2,3,4,5,6,...
;; drop 5 => 5,6,7,...
;; nth 0 => 5
(defn test-drop []
  (seq-nth 0 (seq-drop 5 (range-from 0))))                 ;; -> 5

;; Composition: map then take
;; iterate (* 3) from 1 => 1, 3, 9, 27, 81, ...
;; take 4 => [1, 3, 9, 27], sum = 40
(defn test-compose []
  (let [powers (iterate (fn [x] (mul-i64 x 3)) 1)
        v (seq-take 4 powers)]
    (add-i64 (vec-get v 0)
      (add-i64 (vec-get v 1)
        (add-i64 (vec-get v 2)
                 (vec-get v 3))))))                         ;; -> 40

;; Expected: 10 + 55 + 32 + 21 + 20 + 5 + 40 = 183
(defn main []
  (add-i64 (test-range-take)
    (add-i64 (test-range-reduce)
      (add-i64 (test-iterate)
        (add-i64 (test-repeat)
          (add-i64 (test-seq-map)
            (add-i64 (test-drop)
                     (test-compose))))))))
