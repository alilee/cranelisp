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
