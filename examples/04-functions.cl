;; 04-functions.cl -- Named functions with defn
;;
;; (defn name [param1 param2 ...] body)
;;
;; Functions can call other functions (including themselves).
;; Functions are declared before use in batch mode --
;; the compiler sees all definitions before compiling any bodies.
;; Type annotations on parameters are optional: (defn f [:Int x] ...)

;; A function that doubles its argument
(defn double [x] (mul-i64 x 2))

;; A function with two parameters
(defn add [x y] (add-i64 x y))

;; A function using let for intermediate values
(defn sum-of-squares [a b]
  (let [a2 (mul-i64 a a)
        b2 (mul-i64 b b)]
    (add-i64 a2 b2)))

;; Functions can call other functions
(defn quadruple [x] (double (double x)))

;; A function with a type annotation on its parameter
(defn inc [:Int x] (add-i64 x 1))

;; Max of two integers using if
(defn max [a b]
  (if (gt-i64 a b) a b))

;; Min of two integers using if
(defn min [a b]
  (if (lt-i64 a b) a b))

;; Clamp a value to a range [lo, hi]
(defn clamp [val lo hi]
  (min (max val lo) hi))

;; Expected: 42 + 7 + 25 + 40 + 6 + 7 + 3 + 5 = 135
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (double 21)
      (add-i64 (add 3 4)
        (add-i64 (sum-of-squares 3 4)
          (add-i64 (quadruple 10)
            (add-i64 (inc 5)
              (add-i64 (max 3 7)
                (add-i64 (min 3 7)
                         (clamp 5 1 10))))))))))
