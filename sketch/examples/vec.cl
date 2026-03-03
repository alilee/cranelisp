(platform stdio)
(import [platform.stdio [*]])

(defn main []
  (let [xs [1 2 3 4 5]]
    (do
      (print (show (vec-len xs)))
      (print (show (vec-get xs 2)))
      (let [ys (vec-push xs 6)]
        (do
          (print (show (vec-len ys)))
          (let [zs (vec-set ys 0 99)]
            (pure (vec-get zs 0))))))))
