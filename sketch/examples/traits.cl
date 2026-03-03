(platform stdio)
(import [platform.stdio [*]])

(deftrait Doubled
  (doubled [self] Int))

(impl Doubled Int
  (defn doubled [x] (* x 2)))

(defn main []
  (print (show (doubled 21))))
