;; W0.b lenient-class corpus 01 — CTOR `Def` synthetic body.
;; The ctor `MkBox` is a `DefKind::Constructor` (requires_codegen_view == false)
;; whose `ConstrADT` synthetic body is built by the LENIENT view builder, never
;; strict `from_expr`. Constructing `(MkBox 5)` forces the `user::Box.MkBox`
;; frame into codegen. Free-standing (primitives only); green by construction.
(import [primitives [*]])

(deftype Box (MkBox [:Int w]))

(defn main []
  (Pure (match (MkBox 5) [(MkBox w) w])))
