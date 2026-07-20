;; 37-method-import -- Dispatch reaches the METHOD, not the trait
;;
;; Examples 15/17/20 declared traits and dispatched their methods with the
;; trait in scope. This example shows the subtler rule (spec/07-traits.md
;; §7.11.2, settled S113): to CALL a trait method you only need the METHOD in
;; scope -- the trait itself need NOT be imported.
;;
;; A method reference carries the method's fully-qualified identity, and that
;; identity names the one trait that declares it (and its home module). So
;; reaching the method reaches everything dispatch needs: the compiler roots
;; resolution at the method's home and finds the matching impl by key on
;; (method identity, concrete type). Impl coherence is global -- the impl need
;; not be separately visible at the call site.
;;
;;   Declaration reaches the TRAIT; dispatch reaches the METHOD.
;;
;; (Declaring an impl -- `(impl Describe ...)` -- still needs the trait name in
;; scope, §7.11.2 edge (d). That is why the impls live in main/traits.cl,
;; where `Describe` is declared. This entry module never imports `Describe`.)

;; Load the helper module main/traits.cl (module main.traits).
(mod traits)

;; The entry module names the primitives it uses (a subdirectory entry is its
;; own project root, so it inherits no ancestor prelude -- keeps the example
;; free-standing, spec/08-modules.md §8.3).
(import [primitives [Pure add-i64 eq-i64]])

;; Import the METHODS `describe` and `blank`, plus the two TYPES -- but NOT the
;; trait `Describe`. This is the whole point: `Describe` is never in this
;; module's scope, yet every call below dispatches.
(import [main.traits [describe blank Shape Circle]])

;; --- Unary dispatch: the argument's concrete type selects the impl ---

;; `describe` on a Shape runs the Shape impl -> side count.
(defn test-unary-shape []
  (if (eq-i64 (describe (Shape 7)) 7) 1 0))              ;; -> 1

;; The SAME method name on a Circle runs the Circle impl -> r*r. One imported
;; method, two impls, dispatch chosen by the argument type.
(defn test-unary-circle []
  (if (eq-i64 (describe (Circle 4)) 16) 1 0))           ;; -> 1

;; --- Nullary return-type dispatch: the EXPECTED TYPE selects the impl ---

;; `blank` takes no argument, so nothing about the call fixes which impl runs.
;; A `:Type` annotation supplies the expected return type, and THAT drives the
;; dispatch. Here the let-binding annotation `:Shape` picks Shape's `blank`
;; (which yields `(Shape 3)`), so `describe` then reads 3.
(defn test-nullary-shape []
  (if (eq-i64 (let [x :Shape (blank)] (describe x)) 3) 1 0))   ;; -> 1

;; The annotation can also sit inline directly on the dispatch call: `:Circle`
;; binds the following form `(blank)`, picking Circle's `blank` -> `(Circle 5)`,
;; and `describe` reads 5*5 = 25.
(defn test-nullary-circle []
  (if (eq-i64 (describe :Circle (blank)) 25) 1 0))            ;; -> 1

;; Sum of pass counts: 1 + 1 + 1 + 1 = 4. Every sub-test contributes 1 on
;; success, so any dispatch regression lowers the exit code below 4.
(defn main []
  (Pure
    (add-i64 (test-unary-shape)
      (add-i64 (test-unary-circle)
        (add-i64 (test-nullary-shape)
                 (test-nullary-circle))))))
