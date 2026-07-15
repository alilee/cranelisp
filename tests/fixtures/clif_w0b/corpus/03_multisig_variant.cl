;; W0.b lenient-class corpus 03 — `f$Var` multi-sig VARIANT bodies.
;; A multi-signature `defn` mangles each arity/type variant to `pick$Int`,
;; `pick$Int+Int`. Each variant body is compiled through the LENIENT arm
;; (backend lib.rs `_ => (lenient_mono_from_expr(&variant.body), None)` — the
;; multi-sig variant path proper). Calling both variants forces both frames.
;; Free-standing (primitives only); green by construction.
(import [primitives [*]])

(defn pick
  ([:Int x] x)
  ([:Int x :Int y] (add-i64 x y)))

(defn main []
  (Pure (add-i64 (pick 5) (pick 3 4))))
