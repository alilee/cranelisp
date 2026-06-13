;; 29-annotations.cl -- Type annotations with :Type
;;
;; `:Type` is a type-unifying annotation. It is a reader-level prefix that
;; binds the IMMEDIATELY-FOLLOWING form -- in EVERY position -- and unifies
;; that form's inferred type with the named type. It is never a standalone
;; atom; it always attaches to the next form.
;;
;;   :Int 42      ;; annotates the literal 42 with Int -> :primitives/Int 42
;;   :Int x       ;; annotates the name x with Int
;;   :Int (f y)   ;; annotates the call (f y) with Int
;;
;; The annotation is a CHECK, not a cast. The annotated form must already
;; have a type that unifies with the named type, or compilation fails.
;; Annotations document intent and pin inference; they never change a value.
;;
;; You have already seen :Type in two idiomatic places:
;;   - deftype fields:  (deftype Point [:Int x :Int y])
;;   - defn params:     (defn rem [:Int a :Int b] ...)
;; Those are the same construct: `:Int` binds the following form (the field
;; name, the parameter name), unifying its type with Int.

;; --- Annotating a literal -------------------------------------------------

;; Annotate a literal directly. The literal already infers as Int, and the
;; annotation unifies with that -- so this is the identity on the value 42.
(defn annotated-literal []
  :Int 42)

;; --- Annotating a let binding's value ------------------------------------

;; Inside a let, annotate the bound value to pin its type explicitly.
;; `n` is forced to Int; the body returns it.
(defn annotated-let []
  (let [n :Int 40]
    (add-i64 n 2)))

;; --- Annotating a parameter (the idiomatic defn form) --------------------

;; The :Type prefix on a parameter name unifies that parameter's type.
;; Here both parameters are pinned to Int and the body adds them.
(defn add-ints [:Int a :Int b]
  (add-i64 a b))

;; --- Annotating fields in a deftype --------------------------------------

;; Each field's :Type binds the following field name, unifying its type.
(deftype Point [:Int x :Int y])

(defn point-sum [p]
  (match p [(Point x y) (add-i64 x y)]))

;; --- Annotating a subexpression ------------------------------------------

;; The annotation can bind a whole parenthesised form. Here it documents
;; that the result of the call is expected to be Int.
(defn annotated-call []
  :Int (add-i64 10 7))

;; --- Error cases (shown as comments -- a runnable example cannot type-error)

;; The annotation must UNIFY with the form's inferred type. Annotating an
;; Int literal with Float is a type mismatch, rejected at compile time:
;;
;;   :Float 42
;;   ;; error: type mismatch: expected Int, got Float
;;
;; `:Type` is NOT a function and `(:Type form)` is NOT a special form. The
;; reader binds :Int to the single following element, yielding a one-element
;; list -- then that Int-typed element is applied as a function, which fails:
;;
;;   (:Int 42)
;;   ;; error: type mismatch: expected Int, got (Fn ...)   ;; Int is not callable
;;
;; The annotation type must also be a known type. An unknown name is rejected:
;;
;;   :Foo 42
;;   ;; error: unknown type `Foo`

;; Expected: 42 + 42 + 11 + 7 + 17 = 119
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (annotated-literal)
      (add-i64 (annotated-let)
        (add-i64 (add-ints 5 6)
          (add-i64 (point-sum (Point 3 4))
                   (annotated-call)))))))
