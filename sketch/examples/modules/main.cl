(mod util)
(mod math)
(platform stdio)
(import [platform.stdio [*]])

(defn main []
  (do
    (print (show (util/helper 42)))
    (print (show (math/double 21)))
    (print (show (math/add-one 99)))))
