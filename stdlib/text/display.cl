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
