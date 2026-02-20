(platform stdio)
(import [platform.stdio [*]])

;; Lazy sequences — thunk-based lazy evaluation

(defn main []
  (do
    ;; take 5 from an infinite range
    (print (show (head (to-list (take 5 (range-from 0))))))

    ;; lazy map + take from infinite sequence
    (print (show (head (to-list (take 3 (map inc (range-from 10)))))))

    ;; reduce over a finite lazy seq
    (print (show :Int (reduce + 0 (lazy-take 5 (range-from 1)))))

    ;; iterate: powers of 2
    (print (show (head (to-list (lazy-drop 5 (lazy-take 10 (iterate (fn [x] (* x 2)) 1)))))))

    ;; filter: only values > 2
    (print (show (head (to-list (filter (fn [x] (> x 2)) [1 2 3 4 5])))))

    ;; repeat
    (print (show (head (to-list (lazy-take 3 (repeat 42))))))))
