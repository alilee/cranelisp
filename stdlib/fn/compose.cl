;; fn/compose.cl — Function composition utilities
;;
;; Pure function combinators: compose, pipe, identity, flip.
;; No stdlib dependencies — uses only primitives.
;;
;; Spec: plan-stdlib.md §3.3

(import [prelude []])

(defn identity "Return the argument unchanged" [x] x)

(defn compose "Compose two functions: (compose f g) returns (fn [x] (f (g x)))"
  [f g]
  (fn [x] (f (g x))))

(defn pipe "Pipe two functions: (pipe f g) returns (fn [x] (g (f x)))"
  [f g]
  (fn [x] (g (f x))))

(defn flip "Flip the argument order: (flip f) returns (fn [a b] (f b a))"
  [f]
  (fn [a b] (f b a)))

;; ── Self-tests ───────────────────────────────────────────────────────
;; `(mod test …)` submodule (S87 Stage C.2): exercises the combinators with
;; the in-language harness.

(mod test)  ;; body in compose/test.cl (extraction-stable backing file, spec §8.2.5)
