(platform stdio)
(import [platform.stdio [*]])

(defn add
  ([x y] (add-i64 x y))
  ([x y z] (add-i64 x (add-i64 y z))))

(defn apply-fn [f x] (f x))

(defn main []
  (do
    (print (show (add 1 2)))
    (print (show (add 1 2 3)))
    (print (show (apply-fn (add 10) 5)))
    (pure 0)))
