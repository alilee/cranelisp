(platform stdio)
(import [platform.stdio [*]])

(defn main []
  (do
    (print (show (+ 1.5 2.5)))
    (print (show (* 3.14 2.0)))
    (pure 0)))
