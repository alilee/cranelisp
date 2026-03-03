(platform stdio)
(import [platform.stdio [*]])

;; List type — recursive ADT with (list ...) sugar

(defn length [xs]
  (if (empty? xs)
    0
    (+ 1 (length (tail xs)))))

(defn main []
  (do
    (print (show (empty? (list))))
    (print (show (empty? (list 1 2 3))))
    (print (show (head (list 42 99))))
    (print (show (head (tail (list 1 2 3)))))
    (print (show (length (list 1 2 3 4 5))))))
