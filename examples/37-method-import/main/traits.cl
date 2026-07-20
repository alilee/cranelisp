;; main/traits.cl -- A module that declares a trait and implements it.
;;
;; This is the nested child main/traits.cl, so its module identity is
;; "main.traits" (per spec/08-modules.md §8.2.5). It is loaded by main.cl
;; via (mod traits).
;;
;; The point of this example lives in main.cl: the entry module imports the
;; trait's METHODS (`describe`, `blank`) WITHOUT importing the trait
;; `Describe` itself -- and dispatch still works. This module just supplies
;; the trait and its impls to import from.
;;
;; A submodule does not inherit the entry module's prelude, so it imports
;; the primitives it uses explicitly (per spec/08-modules.md §8.3),
;; including the `Int` type used in the deftype field annotations.
(import [primitives [Int mul-i64]])

;; A trait with two shapes of method:
;;   - `describe` is UNARY: it dispatches on the concrete type of its one
;;     argument (§7.4 argument dispatch).
;;   - `blank` is NULLARY and returns `self` -- the implementing type. It has
;;     no argument to dispatch on, so it dispatches on its expected RETURN
;;     type (§7.1.1 return-type dispatch): the caller supplies the type.
(deftrait Describe
  (describe [self] Int)
  (blank [] self))

;; Two unrelated types, each with its own impl of Describe.
(deftype Shape [:Int sides])
(deftype Circle [:Int radius])

;; describe on a Shape returns its side count; blank yields a 3-sided default.
(impl Describe Shape
  (defn describe [s] (match s [(Shape n) n]))
  (defn blank [] (Shape 3)))

;; describe on a Circle returns its area (r*r approx); blank yields radius 5.
(impl Describe Circle
  (defn describe [c] (match c [(Circle r) (mul-i64 r r)]))
  (defn blank [] (Circle 5)))
