(mod types)
(platform stdio)
(import [types [Point make-point x y]])
(import [platform.stdio [*]])

(defn main []
  (do
    (let [p (make-point 3 4)]
      (do
        (print (show (x p)))
        (print (show (y p)))))))
