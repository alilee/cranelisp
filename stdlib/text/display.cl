;; text/display.cl — Display trait and primitive impls
;;
;; The Display trait defines how values are converted to human-readable
;; string representations.
;;
;; Spec: 07-traits.md §7.1

(import [prelude []])
(import [primitives [*]])

(deftrait Display
  (show [self] String))

(impl Display Int
  (defn show [x] (int-to-string x)))

(impl Display Float
  (defn show [x] (float-to-string x)))

(impl Display Bool
  (defn show [x] (bool-to-string x)))

(impl Display String
  (defn show [x] x))

;; ── Self-tests ───────────────────────────────────────────────────────
;; `(mod test …)` submodule (S87 Stage C.2): super-imports `show` and checks
;; each primitive's rendering. HARNESS-FREE by necessity: `testing.assertions`
;; depends on `text.display` (for `assert-eq`'s `Display` bound), so importing
;; the harness here forms a load cycle
;; (text.display → text.display.test → testing.assertions → text.display).
;; The tests return `(Option String)` directly via inline `if` over a
;; `str-eq` of the rendered String — the same shape the harness produces.

(mod test)
