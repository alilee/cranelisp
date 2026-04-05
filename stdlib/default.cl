;; default.cl — Default trait
;;
;; The Default trait provides a "zero value" for types. Types with a
;; natural empty/identity value implement this trait.
;;
;; Spec: plan-stdlib.md §3.3

(import [prelude []])

(import [fn.option [Option None]])

(deftrait Default
  (default [] self))

(impl Default Int
  (defn default [] 0))

(impl Default Float
  (defn default [] 0.0))

(impl Default Bool
  (defn default [] false))

(impl Default String
  (defn default [] ""))
