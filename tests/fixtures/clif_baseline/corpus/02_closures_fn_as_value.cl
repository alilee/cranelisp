;; L-B1 golden-CLIF corpus 02 — closures + fn-as-value (same-module,
;; single-instantiation shapes only: the 0483 two-instantiation HOF and the
;; 0488 FQ-call/imported-value-use shapes are corpus-EXCLUDED — see
;; ../EXCLUSIONS.md). Free-standing; green by construction.
(import [primitives [*]])

(defn incr [:Int x] (add-i64 x 1))

(defn call1 [f :Int x] (f x))

(defn make-adder [:Int n] (fn [m] (add-i64 n m)))

(defn main []
  (Pure (add-i64 (call1 incr 4) ((make-adder 10) 7))))
