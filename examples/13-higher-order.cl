;; 13-higher-order.cl -- Functions taking and returning functions
;;
;; A higher-order function is one that takes a function as a parameter
;; or returns a function as its result (or both). This is the key
;; pattern for abstraction in functional programming.
;;
;; Taking a function as a parameter:
;;   (defn apply-fn [f x] (f x))
;;   Here f is a function parameter -- its type is inferred from use.
;;
;; Returning a function:
;;   (defn make-adder [n] (fn [x] (add-i64 n x)))
;;   Returns a closure that captures n.
;;
;; Combining both: compose takes two functions, returns a new one:
;;   (defn compose [f g] (fn [x] (f (g x))))
;;   The result applies g first, then f.
;;
;; Named functions can be passed as values too:
;;   (defn inc [x] (add-i64 x 1))
;;   (apply-fn inc 41)    ;; -> 42

;; --- Functions as arguments ---

;; Apply a function to a value
(defn apply-fn [f x] (f x))

(defn check-apply-fn []
  (apply-fn (fn [x] (mul-i64 x 2)) 21))

;; Apply a function twice
(defn apply-twice [f x] (f (f x)))

(defn check-apply-twice []
  (apply-twice (fn [x] (add-i64 x 1)) 0))

;; Apply a function n times using recursion
(defn repeat-fn [f n x]
  (if (eq-i64 n 0)
    x
    (repeat-fn f (sub-i64 n 1) (f x))))

(defn check-repeat-fn []
  (repeat-fn (fn [x] (add-i64 x 1)) 5 0))

;; --- Named functions as values ---

;; Named functions can be passed directly to higher-order functions
(defn inc [x] (add-i64 x 1))
(defn double [x] (mul-i64 x 2))

(defn check-named-as-value []
  (add-i64 (apply-fn inc 41)
           (apply-twice double 3)))

;; --- Functions returning functions ---

;; A function factory: creates adders
(defn make-adder [n]
  (fn [x] (add-i64 n x)))

;; A function factory: creates multipliers
(defn make-multiplier [n]
  (fn [x] (mul-i64 n x)))

(defn check-factories []
  (let [add5  (make-adder 5)
        mul3  (make-multiplier 3)]
    (add-i64 (add5 10) (mul3 10))))

;; --- Function composition ---

;; Compose two functions: first apply g, then f
(defn compose [f g]
  (fn [x] (f (g x))))

;; inc-then-double: first add 1, then multiply by 2
(defn check-compose []
  (let [inc-then-double (compose (fn [x] (mul-i64 x 2))
                                 (fn [x] (add-i64 x 1)))]
    (inc-then-double 5)))

;; Compose named functions
(defn check-compose-named []
  ((compose inc double) 10))

;; --- Combining patterns ---

;; Apply a transformation and a predicate check
(defn transform-and-check [transform check x]
  (let [result (transform x)]
    (if (check result) result 0)))

(defn check-transform-check []
  (let [tripled (transform-and-check
                  (fn [x] (mul-i64 x 3))
                  (fn [x] (gt-i64 x 10))
                  5)]
    tripled))

;; Build a pipeline: apply three functions in sequence
(defn pipeline3 [f g h x]
  (h (g (f x))))

(defn check-pipeline []
  (pipeline3 (fn [x] (add-i64 x 1))    ;; 4 -> 5
             (fn [x] (mul-i64 x 2))    ;; 5 -> 10
             (fn [x] (sub-i64 x 3))    ;; 10 -> 7
             4))

;; Expected: 42 + 2 + 5 + 54 + 45 + 12 + 21 + 15 + 7 = 203
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (check-apply-fn)
      (add-i64 (check-apply-twice)
        (add-i64 (check-repeat-fn)
          (add-i64 (check-named-as-value)
            (add-i64 (check-factories)
              (add-i64 (check-compose)
                (add-i64 (check-compose-named)
                  (add-i64 (check-transform-check)
                           (check-pipeline)))))))))))
