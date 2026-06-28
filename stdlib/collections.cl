;; collections.cl — Data structure group
;;
;; Submodules:
;;   collections.pair   — Pair type
;;   collections.either — Either type
;;   collections.list   — List type (recursive ADT)
;;   collections.vec    — Vec utility functions
;;   collections.parallel — Parallel map/reduce/map-reduce over a Vec

(import [prelude []])

(mod pair)
(mod either)
(mod list)
(mod vec)
(mod parallel)
