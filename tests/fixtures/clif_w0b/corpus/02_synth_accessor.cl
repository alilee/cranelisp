;; W0.b lenient-class corpus 02 — SYNTHESISED field accessor.
;; A product `deftype` generates canonical field accessors `Point.x` / `Point.y`,
;; each a `Concrete{slot}` UserFn that legitimately carries `codegen_view: None`
;; (its synthetic `(match self [(Point _ y) y])` body has no typecheck view — the
;; backend reads field types from the ctor signature), so it falls to the LENIENT
;; builder. Invoking both accessors forces the `user::Point.x` / `user::Point.y`
;; frames. (The product ctor `user::Point` is captured too — it is itself a
;; lenient synthetic ctor body, a control alongside the accessor focus.)
;; Free-standing (primitives only); green by construction.
(import [primitives [*]])

(deftype Point [:Int x :Int y])

(defn main []
  (Pure (add-i64 (Point.x (Point 3 7)) (Point.y (Point 3 7)))))
