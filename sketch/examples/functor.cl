(platform stdio)
(import [platform.stdio [*]])

;; Functor — higher-kinded type trait for mapping over containers

(defn double [:Int x] (* x 2))

(defn is-some [opt]
  (match opt
    [None false
     (Some _) true]))

(defn main []
  (do
    ;; fmap over Option — Some case
    (print (show (val (fmap inc (Some 5)))))

    ;; fmap over Option — None case
    (print (show (is-some (fmap double None))))

    ;; fmap over List
    (let [mapped (fmap double (list 1 2 3))]
      (do
        (print (show (head mapped)))
        (print (show (head (tail mapped))))
        (print (show (head (tail (tail mapped)))))))))
