;; L-B1 golden-CLIF corpus 09 — ParBind/LaunchContinue shape: a
;; divide-and-conquer reduce whose two independent recursive apply-args
;; auto-spark under lenient eval (the F1 tree shape at miniature scale).
;; Suspension-crossing captures are the R6 escape class (L-C1/L-D3c).
;; Free-standing; green by construction (parallel ≡ serial by
;; tests/s99_fixtures.rs precedent).
(import [primitives [*]])

(defn leaf [:Int i] (add-i64 (mul-i64 i i) 1))

(defn mid-of [:Int lo :Int hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

(defn reduce-range [:Int lo :Int hi]
  (if (eq-i64 (sub-i64 hi lo) 1)
    (leaf lo)
    (let [m (mid-of lo hi)]
      (add-i64 (reduce-range lo m) (reduce-range m hi)))))

(defn main []
  (Pure (reduce-range 0 8)))
