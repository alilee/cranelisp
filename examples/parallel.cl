; Parallel evaluation with par-let
; Platform IO calls in bind! chains are auto-scheduled in parallel where safe.

(platform stdio)
(import [platform.stdio [*]])

(defn fib [n]
  (if (<= n 1) n (+ (fib (- n 1)) (fib (- n 2)))))

; par-let evaluates pure bindings in parallel
(defn main []
  (bind! [result (pure (par-let [a (fib 20)
                                 b (fib 21)]
                   (+ a b)))]
    (print (show result))))
