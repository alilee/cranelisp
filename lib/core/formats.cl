(import [primitives [*]])

;; ── Display Trait ───────────────────────────────────

(deftrait Display "Convert to string representation"
  (show "Convert value to string" [self] String))

;; ── Display Impls ───────────────────────────────────

(impl Display Int
  (defn show [x] (int-to-string x)))

(impl Display Float
  (defn show [x] (float-to-string x)))

(impl Display Bool
  (defn show [x] (bool-to-string x)))

(impl Display String
  (defn show [x] (string-identity x)))
