;; L-B1 golden-CLIF corpus 01 — ADT construct + match projections.
;; Shapes: multi-ctor ADT construction, match with field bindings (projection
;; reads), nested construct-then-project. Free-standing; green by
;; construction (tests/plan/s100-ownership-verification.md §3.1).
(import [primitives [*]])

(deftype Shape (Circle [:Int r]) (Rect [:Int w :Int h]))

(defn area [s]
  (match s
    [(Circle r) (mul-i64 3 (mul-i64 r r))
     (Rect w h) (mul-i64 w h)]))

(defn pick [:Int n]
  (if (eq-i64 n 0) (Circle 2) (Rect 3 4)))

(defn main []
  (Pure (add-i64 (area (pick 0)) (area (pick 1)))))
