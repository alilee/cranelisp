;; 11-destructuring.cl -- Pattern matching on data constructors
;;
;; Example 06 showed pattern matching on enums (nullary constructors).
;; Now we match on data constructors to extract their fields.
;;
;; Constructor patterns bind each field to a variable:
;;   (match (Point 3 4) [(Point x y) (add-i64 x y)])
;;   Here x binds to 3 and y binds to 4.
;;
;; Sum type patterns discriminate between constructors:
;;   (match opt [(Some x) x  None 0])
;;   If opt is (Some 42), x binds to 42.
;;   If opt is None, the second arm runs.
;;
;; Wildcard _ matches anything without binding:
;;   (match opt [(Some _) 1  _ 0])
;;   Returns 1 if opt is Some (ignoring the value), 0 otherwise.
;;
;; Variable patterns (a bare name, not a constructor) match anything and bind:
;;   (match opt [(Some x) x  other 0])
;;   'other' would bind the None value (but we return 0 regardless).
;;
;; Nested match: match on one level, then match the bound value:
;;   (match outer [(Some inner) (match inner [(Some x) x None 0]) ...])

;; Types for this example
(deftype Point [:Int x :Int y])
(deftype (Option a) None (Some [:a val]))

;; --- Extracting fields from product types ---

;; Swap the x and y coordinates of a point
(defn swap-point [p]
  (match p [(Point x y) (Point y x)]))

(defn test-swap []
  (let [swapped (swap-point (Point 3 7))]
    (match swapped [(Point x y) (sub-i64 x y)])))

;; Compute the Manhattan distance from a point to the origin
(defn manhattan [p]
  (match p
    [(Point x y)
     (let [ax (if (lt-i64 x 0) (sub-i64 0 x) x)
           ay (if (lt-i64 y 0) (sub-i64 0 y) y)]
       (add-i64 ax ay))]))

(defn test-manhattan []
  (manhattan (Point -3 4)))

;; --- Discriminating sum types ---

;; Check whether an Option has a value
(defn is-some [opt]
  (match opt
    [(Some _) 1
     _        0]))

(defn test-is-some []
  ;; `(is-some (Some 42))` pins the Option element type via the `(Some 42)` value.
  ;; A bare `(is-some None)` would reach codegen with `None`'s `(Option a)` element
  ;; type unpinned — an ambiguity error under spec §3.11.1 (no representation-based
  ;; exemption). Disambiguate the bare nullary constructor with `:(Option Int) None`.
  (add-i64 (is-some (Some 42)) (is-some :(Option Int) None)))

;; Provide a default for None
(defn get-or-default [opt default]
  (match opt
    [(Some x) x
     None     default]))

(defn test-get-or-default []
  (add-i64 (get-or-default (Some 10) 0)
           (get-or-default None 5)))

;; --- Wildcard patterns ---

;; Count how many of three options have values (using wildcard for the value)
(defn count-some [a b c]
  (let [ca (match a [(Some _) 1 _ 0])
        cb (match b [(Some _) 1 _ 0])
        cc (match c [(Some _) 1 _ 0])]
    (add-i64 ca (add-i64 cb cc))))

(defn test-count-some []
  ;; The bare `None` is `(Option a)` with the element type unpinned; under the
  ;; tightened §3.11.1 (full-concreteness) it must be annotated concrete at the
  ;; codegen-reaching call site. `(Some 1)`/`(Some 3)` are already `(Option Int)`.
  (count-some (Some 1) :(Option Int) None (Some 3)))

;; --- Nested match ---

;; Add two optional integers, treating None as zero
(defn add-opts [a b]
  (match a
    [None 0
     (Some x)
       (match b
         [None     x
          (Some y) (add-i64 x y)])]))

(defn test-add-opts []
  (add-i64 (add-opts (Some 10) (Some 20))
           (add-opts (Some 5) None)))

;; --- Combining match with recursion ---

;; A recursive safe-division that returns Option
(defn safe-div [a b]
  (if (eq-i64 b 0)
    None
    (Some (div-i64 a b))))

;; Chain two divisions: a / b / c
(defn chain-div [a b c]
  (match (safe-div a b)
    [None     0
     (Some r) (match (safe-div r c)
                [None     0
                 (Some s) s])]))

(defn test-chain-div []
  (add-i64 (chain-div 100 5 4)     ;; 100/5=20, 20/4=5
           (chain-div 100 0 4)))    ;; division by zero -> 0

;; Expected: 4 + 7 + 1 + 15 + 2 + 35 + 5 = 69
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-swap)
      (add-i64 (test-manhattan)
        (add-i64 (test-is-some)
          (add-i64 (test-get-or-default)
            (add-i64 (test-count-some)
              (add-i64 (test-add-opts)
                       (test-chain-div)))))))))
