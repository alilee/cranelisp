;; 25-curry.cl -- Auto-currying and partial application
;;
;; In Cranelisp, calling a function with fewer arguments than it
;; expects returns a new function that waits for the remaining args.
;; This is called auto-currying.
;;
;; For example, a three-argument function:
;;   (defn add3 [a b c] (add-i64 a (add-i64 b c)))
;;
;; Can be partially applied:
;;   (add3 10)       ;; returns (Fn [Int Int] Int) that adds 10 to sum of two args
;;   (add3 10 20)    ;; returns (Fn [Int] Int) that adds 30 to its arg
;;
;; This enables a point-free style of programming where you build
;; specialised functions from general ones without writing lambdas.

;; --- Basic partial application ---

;; A two-argument function
(defn add [a b] (add-i64 a b))

;; Partially apply to create increment
(defn test-inc []
  (let [inc (add 1)]
    (inc 41)))

;; A three-argument function
(defn add3 [a b c] (add-i64 a (add-i64 b c)))

;; Apply one arg: get a two-arg function
(defn test-partial-one []
  (let [add-from-10 (add3 10)]
    (add-from-10 20 12)))

;; Apply two args: get a one-arg function
(defn test-partial-two []
  (let [add-30 (add3 10 20)]
    (add-30 12)))

;; --- Currying with higher-order functions ---

;; apply-twice takes a function and applies it twice
(defn apply-twice [f x] (f (f x)))

;; Use curried add with apply-twice
(defn test-curry-compose []
  (let [add5 (add 5)]
    (apply-twice add5 0)))

;; --- Building specialised functions ---

;; A general scaling function
(defn scale [factor x] (mul-i64 factor x))

;; Create specialised scalers via currying
(defn test-scalers []
  (let [double (scale 2)
        triple (scale 3)]
    (add-i64 (double 7) (triple 7))))

;; --- Curried functions as arguments ---

;; map-pair applies a function to two values and sums results
(defn map-pair [f a b] (add-i64 (f a) (f b)))

(defn test-curry-as-arg []
  (map-pair (add 100) 1 2))

;; Expected: 42 + 42 + 42 + 10 + 35 + 203 = 374
(defn main []
  (add-i64 (test-inc)
    (add-i64 (test-partial-one)
      (add-i64 (test-partial-two)
        (add-i64 (test-curry-compose)
          (add-i64 (test-scalers)
                   (test-curry-as-arg)))))))
