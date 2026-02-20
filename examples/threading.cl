(platform stdio)
(import [platform.stdio [*]])

;; Threading macros and conditional macros
;;
;; Demonstrates ->, ->>, cond, case, and vec macros.

(defn main []
  (do
    ;; Thread-first: (-> 5 inc (* 2)) => (* (inc 5) 2) = 12
    (print (show :Int (-> 5 inc (* 2))))

    ;; Thread-last: (->> 2 (* 3) (+ 10)) => (+ 10 (* 3 2)) = 16
    (print (show :Int (->> 2 (* 3) (+ 10))))

    ;; Cond: multi-way conditional with default
    (print (show :Int (cond (< 5 0) -1
                            (= 5 0) 0
                            1)))

    ;; Case: dispatch on value equality with default
    (print (show :Int (case 2 1 10 2 20 0)))

    ;; Vec macro: (vec 1 2 3) => [1 2 3]
    (print (show (vec-len (vec 10 20 30))))))
