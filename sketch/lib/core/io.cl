(import [primitives [*]])

;; ── IO Monadic Operations ──────────────────────────

(defn pure "Lift a value into IO" [x] (Pure x))
;; bind is now a primitive (inline codegen — constructs Bind nodes)
