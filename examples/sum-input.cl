(platform stdio)
(import [platform.stdio [*]])

(defn read-int []
  (bind! [line (read-line)]
    (pure (parse-int line))))

(defn sum-loop [remaining acc]
  (if (= remaining 0)
    (pure acc)
    (bind! [result (read-int)]
      (match result
        [(Some n) (sum-loop (- remaining 1) (+ acc n))
         None (do
          (print "Invalid number, try again")
          (sum-loop remaining acc))]))))

(defn main []
  (bind! [total (sum-loop 6 0)]
    (print (show total))))
