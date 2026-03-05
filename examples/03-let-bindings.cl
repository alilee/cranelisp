;; 03-let-bindings.cl -- Local names with let
;;
;; (let [name1 value1 name2 value2 ...] body)
;;
;; Bindings are sequential: later bindings can see earlier ones.
;; Let introduces local scope -- names are not visible outside the let body.
;; Names can be shadowed by inner let bindings.

;; Single binding
(defn single-bind []
  (let [x 5]
    (add-i64 x 1)))

;; Multiple bindings (y uses x)
(defn multi-bind []
  (let [x 3
        y (mul-i64 x 2)]
    (add-i64 x y)))

;; Nested let
(defn nested-let []
  (let [x 5]
    (let [y (add-i64 x 1)]
      (mul-i64 x y))))

;; Shadowing: inner x hides outer x
(defn shadowing []
  (let [x 10]
    (let [x 20]
      x)))

;; Using let to name intermediate computations:
;; compute the distance squared between two 1D points
(defn distance-squared [x1 x2]
  (let [diff (sub-i64 x2 x1)]
    (mul-i64 diff diff)))

;; Let with if: absolute value using a named intermediate
(defn abs [n]
  (let [is-negative (lt-i64 n 0)]
    (if is-negative (sub-i64 0 n) n)))

;; Expected: 6 + 9 + 30 + 20 + 25 + 7 = 97
(defn main []
  (add-i64 (single-bind)
    (add-i64 (multi-bind)
      (add-i64 (nested-let)
        (add-i64 (shadowing)
          (add-i64 (distance-squared 2 7)
                   (abs -7)))))))
