;; 29-annotations.cl -- What the :Type annotation is FOR (capstone)
;;
;; You have been reading `:Type` since the very first typed examples:
;; `:Int` on deftype fields (example 10), `:Int` on defn parameters
;; (from example 04 onward), `:primitives/Int` in every REPL result line.
;; This example does NOT introduce a new feature -- it names the single
;; model those scattered appearances share, and then shows the annotation
;; doing REAL WORK: changing what typechecks and which trait instance the
;; compiler selects.
;;
;; The rule: `:Type` is a type-unifying annotation. It is a reader-level
;; prefix that binds the IMMEDIATELY-FOLLOWING form (no space) -- in EVERY
;; position -- and unifies that form's inferred type with the named type.
;; It is never a standalone atom; it always attaches to the next form.
;;
;;   :Int x       ;; annotate the name x with Int
;;   :Int (f y)   ;; annotate the call (f y) with Int
;;   :Int 42      ;; simplest form: annotate a literal (a no-op identity here,
;;                ;; since 42 already infers as Int -- shown once, for shape)
;;
;; The annotation is a CHECK, not a cast. The annotated form must already
;; have a type that unifies with the named type, or compilation fails. It
;; never changes a value -- but it CAN change what the compiler infers, and
;; that is the point of this example.
;;
;; Why annotations earn their keep:
;;
;;   1. CONSTRAIN FUNCTION TYPING. A function whose body is polymorphic or
;;      under-determined can be pinned to a concrete type by an annotation
;;      on a parameter, on the return, or on a sub-expression. The annotation
;;      decides which trait instance the body uses.
;;
;;   2. DISAMBIGUATE AN EXPRESSION. An expression the inferencer cannot pin
;;      on its own -- e.g. a nullary trait method whose only type clue is its
;;      RETURN type -- is ambiguous and is REJECTED. Annotating it resolves
;;      which instance to select, and the program compiles.
;;
;; Both purposes are demonstrated below with code that genuinely needs the
;; annotation. The error cases at the end show what happens WITHOUT it.

;; --- A tiny trait family we can be ambiguous about ------------------------
;;
;; `Default` returns a value OF THE IMPLEMENTING TYPE with no arguments.
;; Its signature is (default [] self): the only type information is the
;; return type. That is exactly the shape inference cannot resolve on its
;; own -- there is no argument to drive instance selection.
(deftrait Default
  (default [] self))

(impl Default Int
  (defn default [] 7))

(impl Default Float
  (defn default [] 2.5))

;; `Show` turns a value into a String. Its parameter type is the only clue.
(deftrait Show
  (show [v] String))

(impl Show Int
  (defn show [v] (int-to-string v)))

(impl Show Float
  (defn show [v] (float-to-string v)))

;; --- Purpose 1: DISAMBIGUATE an expression --------------------------------
;;
;; `(default)` is ambiguous: both `Default Int` and `Default Float` match,
;; and there is no argument to choose between them. On its own this does NOT
;; compile (see the error notes at the bottom). Annotating the call pins the
;; return type, which selects the instance:
;;
;;   :Int   (default)  -> selects `Default Int`,   yields 7
;;   :Float (default)  -> selects `Default Float`, yields 2.5
(defn disambiguate-int []
  (let [x :Int (default)]                                 ;; pins Default Int
    x))                                                   ;; -> 7

(defn disambiguate-float []
  (let [x :Float (default)]                               ;; pins Default Float
    (if (eq-f64 x 2.5) 1 0)))                             ;; -> 1

;; --- Purpose 2: CONSTRAIN function typing ---------------------------------
;;
;; (a) Annotate the RETURN sub-expression. `int-default` has no parameters
;; and its body is the ambiguous `(default)`. Annotating the body pins the
;; whole function to Int -- its inferred type becomes (Fn [] Int), and the
;; body uses `Default Int`.
(defn int-default []
  :Int (default))                                         ;; body pinned to Int

(defn constrain-return []
  (add-i64 (int-default) 35))                             ;; 7 + 35 -> 42

;; (b) Annotate a PARAMETER. `describe`'s parameter `v` is only constrained
;; by `(show v)`, which is itself polymorphic over Show. Annotating the
;; parameter `:Int v` pins the body to the `Show Int` instance, so `show`
;; resolves to `int-to-string`. Without the annotation the parameter type is
;; under-determined and the call is ambiguous.
(defn describe [:Int v]
  (str-len (show v)))                                     ;; uses Show Int

(defn constrain-param []
  (describe 12345))                                       ;; len of "12345" -> 5

;; --- Simplest form: annotate a literal (shown once, for completeness) -----
;;
;; The literal already infers as Int, so the annotation is the identity on
;; the value. This is the shape you have seen since example 04; it does no
;; inference work, which is precisely why it is NOT the interesting case.
(defn annotate-literal []
  :Int 64)                                                ;; -> 64

;; --- Error cases (comments -- a runnable example cannot type-error) --------
;;
;; WITHOUT the annotation, the disambiguation cases above are REJECTED,
;; because the inferencer has no way to choose an instance:
;;
;;   (let [x (default)] x)
;;   ;; error: ambiguous trait method `default` -- no argument or annotation
;;   ;;        pins which Default instance to use
;;
;; The annotation must UNIFY with the form's inferred type. Pinning an Int
;; literal to Float is a mismatch, rejected at compile time:
;;
;;   :Float 42
;;   ;; error: type mismatch: expected Float, got Int
;;
;; `:Type` is NOT a function and `(:Type form)` is NOT a special form. The
;; reader binds `:Int` to the single following element, yielding a one-element
;; list -- then that Int-typed element is applied as a function, which fails:
;;
;;   (:Int (default))
;;   ;; error: type mismatch: expected a function, got Int  ;; Int is not callable
;;
;; The annotation type must also be a known type. An unknown name is rejected:
;;
;;   :Foo 42
;;   ;; error: unknown type `Foo`

;; Expected: 7 + 1 + 42 + 5 + 64 = 119
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (disambiguate-int)
      (add-i64 (disambiguate-float)
        (add-i64 (constrain-return)
          (add-i64 (constrain-param)
                   (annotate-literal)))))))
