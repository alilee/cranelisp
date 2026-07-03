;; L-B1 golden-CLIF corpus 03 — auto-curry (partial application wrappers).
;; Free-standing; green by construction.
(import [primitives [*]])

(defn add3 [:Int a :Int b :Int c] (add-i64 a (add-i64 b c)))

(defn main []
  (let [p (add3 1 2)]
    (Pure (p 3))))
