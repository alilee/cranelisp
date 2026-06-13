;; 05-recursion.cl -- Self-recursive functions and tail call optimization
;;
;; Functions can call themselves. Cranelisp optimizes self-recursive
;; calls in tail position (TCO) so they don't grow the stack.
;;
;; A call is in tail position when it is the last thing a function does:
;; - The else/then branch of an if in tail position
;; - The body of a let in tail position
;; - A match arm body in tail position
;;
;; Non-tail recursion (like naive factorial) works too, but uses
;; stack space proportional to the depth.

;; Factorial -- NOT tail-recursive (mul-i64 wraps the recursive call)
(defn fact [n]
  (if (eq-i64 n 0)
    1
    (mul-i64 n (fact (sub-i64 n 1)))))

;; Factorial -- tail-recursive with accumulator
;; The recursive call (fact-acc ...) is the last thing computed.
(defn fact-acc [n acc]
  (if (eq-i64 n 0)
    acc
    (fact-acc (sub-i64 n 1) (mul-i64 n acc))))

;; Fibonacci -- non-tail-recursive (two recursive calls)
(defn fib [n]
  (if (le-i64 n 1)
    n
    (add-i64 (fib (sub-i64 n 1)) (fib (sub-i64 n 2)))))

;; GCD -- Euclidean algorithm, naturally tail-recursive
(defn gcd [a b]
  (if (eq-i64 b 0)
    a
    (gcd b (sub-i64 a (mul-i64 (div-i64 a b) b)))))

;; Sum 1..n using tail-recursive accumulator
;; This can handle very large n thanks to TCO.
(defn sum-to [n acc]
  (if (eq-i64 n 0)
    acc
    (sum-to (sub-i64 n 1) (add-i64 acc n))))

;; Power: base^exp via repeated multiplication (tail-recursive)
(defn power [base exp acc]
  (if (eq-i64 exp 0)
    acc
    (power base (sub-i64 exp 1) (mul-i64 acc base))))

;; Expected: 120 + 3628800 + 55 + 6 + 5050 + 1024 = 3635055
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (fact 5)
      (add-i64 (fact-acc 10 1)
        (add-i64 (fib 10)
          (add-i64 (gcd 48 18)
            (add-i64 (sum-to 100 0)
                     (power 2 10 1))))))))
