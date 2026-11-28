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

;; ── The seeded data types ─────────────────────────────────────────────
;; `Option`, `Result` and `Pair` are seeded by `primitives`, so their impls
;; live with the trait. The format is the one `derive-Display` produces: a
;; nullary constructor is its name, and a data constructor is its name followed
;; by its fields' `show`s, space-separated, in parentheses — `Some(1)`,
;; `Pair(1 a)`.

(impl Display (Option :Display a)
  (defn show [self]
    (match self
      [None "None"
       (Some u) (str-concat "Some(" (str-concat (show u) ")"))])))

(impl Display (Result :Display a :Display e)
  (defn show [self]
    (match self
      [(Ok u) (str-concat "Ok(" (str-concat (show u) ")"))
       (Err u) (str-concat "Err(" (str-concat (show u) ")"))])))

(impl Display (Pair :Display a :Display b)
  (defn show [self]
    (match self
      [(Pair u v)
       (str-concat "Pair(" (str-concat (show u) (str-concat " " (str-concat (show v) ")"))))])))

;; ── Self-tests ───────────────────────────────────────────────────────
;; Backing file `text/display/test.cl`: super-imports `show` and checks
;; each primitive's rendering. HARNESS-FREE by necessity: `testing.assertions`
;; depends on `text.display` (for `assert-eq`'s `Display` bound), so importing
;; the harness here forms a load cycle
;; (text.display → text.display.test → testing.assertions → text.display).
;; The tests return `(Option String)` directly via inline `if` over a
;; `str-eq` of the rendered String — the same shape the harness produces.

(mod- test)
