(platform stdio)
(import [platform.stdio [*]])

(defn make-adder [n] (fn [x] (+ n x)))

(defn apply-fn [f x] (f x))

(defn main []
  (do
    (print (show (apply-fn (make-adder 5) 3)))
    (print (show (apply-fn (make-adder 10) 3)))
    (print (show ((fn [x] (* x x)) 7)))))
