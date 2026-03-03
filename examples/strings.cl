(platform stdio)
(import [platform.stdio [*]])

(defn main []
  (do
    (print "hello, world!")
    (print (show 42))
    (print (show true))))
