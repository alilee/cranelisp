;; default.cl — Default trait
;;
;; The Default trait provides a "zero value" for types. Types with a
;; natural empty/identity value implement this trait.
;;
;; Spec: plan-stdlib.md §3.3

(import [prelude []])

(import [primitives [Int Float Bool String]])
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

;; An absent value is the natural default for any `Option`; no bound on `a`.
(impl Default (Option a)
  (defn default [] None))

;; ── Self-tests ───────────────────────────────────────────────────────
;; Backing file `default/test.cl` (module `default.test`) exercises each impl
;; through return-type dispatch, importing the method without the trait.

(mod- test)
