;; L-B1 golden-CLIF corpus 08 — ADTs stored in a Vec + projection-read loop
;; (the F1-machinery read shape at miniature scale: vec-get + match on a
;; borrowed root — exactly the I-G1 projection-covered class). Free-standing;
;; green by construction.
(import [primitives [*]])

(deftype Cell (Given [:Int value]) (Solved [:Int solved-value]))

(defn cell-value [c] (match c [(Given v) v  (Solved v) v]))

(defn build [v :Int i :Int n]
  (if (eq-i64 i n) v
    (build (vec-push v (Given (add-i64 i 1))) (add-i64 i 1) n)))

(defn total [g :Int i :Int n :Int acc]
  (if (eq-i64 i n) acc
    (total g (add-i64 i 1) n (add-i64 acc (cell-value (vec-get g i))))))

(defn main []
  (let [g (build [] 0 9)]
    (Pure (total g 0 (vec-len g) 0))))
