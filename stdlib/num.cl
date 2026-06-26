;; num.cl — Numeric trait group
;;
;; Submodules:
;;   num.num   — Num trait + impls
;;   num.int   — Int operations
;;   num.float — Float operations
;;   num.bits  — Bitwise operations (curated layer over S91 native primitives)

(import [prelude []])

(mod num)
(mod int)
(mod float)
(mod bits)
