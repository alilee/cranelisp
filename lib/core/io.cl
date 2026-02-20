(import [primitives [*]])

;; ── IO Monadic Operations ──────────────────────────

(defn pure "Lift a value into IO" [x] (IOVal x))

(defn bind "Chain IO actions, passing result of first to second" [io cont]
  (match io
    [(IOVal v) (cont v)]))
