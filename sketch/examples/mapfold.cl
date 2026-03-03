(platform stdio)
(import [platform.stdio [*]])

;; Map and reduce over Vec and List

(defn main []
  (let [xs [1 2 3 4 5]]
    (do
      ;; vec-map: square each element
      (print (show (vec-get (vec-map (fn [x] (* x x)) xs) 2)))  ; 9

      ;; vec-reduce: sum all elements
      (print (show (vec-reduce + 0 xs)))                           ; 15

      ;; fmap: double each element of list
      (print (show (head (fmap (fn [x] (* x 2)) (list 3 2 1))))) ; 6

      ;; list-reduce: sum all elements
      (print (show (list-reduce + 0 (list 1 2 3 4 5))))           ; 15

      ;; composition: sum of squares
      (print (show (vec-reduce + 0 (vec-map (fn [x] (* x x)) xs)))))))  ; 55
