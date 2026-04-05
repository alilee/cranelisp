;; fn.cl — Function composition and error types group
;;
;; Submodules:
;;   fn.option    — Option type
;;   fn.result    — Result type
;;   fn.compose   — compose, pipe, identity, flip
;;   fn.threading — ->, ->> macros

(import [prelude []])

(mod option)
(mod result)
(mod compose)
(mod threading)
