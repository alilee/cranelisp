;; 12-closures.cl -- Anonymous functions and variable capture
;;
;; Anonymous functions (lambdas) are created with fn:
;;   (fn [x] (add-i64 x 1))
;;
;; Unlike defn, fn creates a value -- a function that can be stored
;; in a let binding, passed to another function, or returned as a result.
;;
;; Closures capture variables from their enclosing scope:
;;   (let [y 10] (fn [x] (add-i64 x y)))
;;   This creates a function that adds y (= 10) to its argument.
;;   The captured value lives on the heap alongside the code pointer.
;;
;; Calling a closure uses the same syntax as calling any function:
;;   (let [f (fn [x] (add-i64 x 1))] (f 5))

;; A simple lambda -- no capture, called immediately
(defn test-immediate []
  ((fn [x] (add-i64 x 1)) 5))

;; Lambda stored in a let binding
(defn test-let-lambda []
  (let [double (fn [x] (mul-i64 x 2))]
    (double 21)))

;; Lambda with zero parameters
(defn test-zero-param []
  (let [always-42 (fn [] 42)]
    (always-42)))

;; Lambda with multiple parameters
(defn test-multi-param []
  (let [sum3 (fn [a b c] (add-i64 a (add-i64 b c)))]
    (sum3 1 2 3)))

;; --- Closures: capturing variables ---

;; Capture a single variable
(defn test-capture-one []
  (let [n 10]
    ((fn [x] (add-i64 n x)) 32)))

;; Capture multiple variables
(defn test-capture-many []
  (let [a 1
        b 2
        c 3]
    ((fn [x] (add-i64 a (add-i64 b (add-i64 c x)))) 4)))

;; Capture a boolean and use it in a condition
(defn test-capture-bool []
  (let [flag true]
    ((fn [x] (if flag x 0)) 42)))

;; --- Closures as return values ---

;; A function that returns a closure
(defn make-adder [n]
  (fn [x] (add-i64 n x)))

(defn test-returned-closure []
  (let [add10 (make-adder 10)]
    (add10 32)))

;; Create two different closures from the same factory
(defn test-two-adders []
  (let [add3 (make-adder 3)
        add7 (make-adder 7)]
    (add-i64 (add3 0) (add7 0))))

;; --- Nested closures ---

;; A closure that calls another closure
(defn test-nested-closures []
  (let [a 1]
    (let [f (fn [x] (add-i64 a x))]
      (let [g (fn [y] (f y))]
        (g 9)))))

;; A closure selecting between two behaviors
(defn test-closure-in-if []
  (let [pick true]
    (let [f (if pick
              (fn [x] (add-i64 x 1))
              (fn [x] (sub-i64 x 1)))]
      (f 10))))

;; Expected: 6 + 42 + 42 + 6 + 42 + 10 + 42 + 42 + 10 + 10 + 11 = 263
(defn main []
  (add-i64 (test-immediate)
    (add-i64 (test-let-lambda)
      (add-i64 (test-zero-param)
        (add-i64 (test-multi-param)
          (add-i64 (test-capture-one)
            (add-i64 (test-capture-many)
              (add-i64 (test-capture-bool)
                (add-i64 (test-returned-closure)
                  (add-i64 (test-two-adders)
                    (add-i64 (test-nested-closures)
                             (test-closure-in-if))))))))))))
