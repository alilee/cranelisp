;; L-B1 golden-CLIF corpus 06 — TCO loop (self-recursive accumulator; the
;; stack-slot TCO back-edge negative's home shape, L-C2(a)). Free-standing;
;; green by construction.
(import [primitives [*]])

(defn spin [:Int n :Int acc]
  (if (eq-i64 n 0) acc
    (spin (sub-i64 n 1) (add-i64 acc n))))

(defn main []
  (Pure (spin 100 0)))
