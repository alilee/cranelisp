;; 20-adt-traits.cl -- Implementing traits for algebraic data types
;;
;; Example 15 introduced traits (Num, Eq, Ord) for primitive types.
;; Example 17 showed how to define custom traits like Display and
;; implement them for user-defined types.
;;
;; This example focuses on implementing Eq and Display for algebraic
;; data types -- enum types and data-carrying sum types. These are
;; the patterns that a derive macro would automate:
;;
;;   - Eq for enums: compare constructor tags
;;   - Eq for sum types: compare tags, then compare fields
;;   - Display for enums: return the constructor name as a string
;;   - Display for data types: format as "Name(field1 field2 ...)"
;;
;; Each trait impl uses match to dispatch on constructors.

;; --- Trait declarations ---

(deftrait Eq
  (= [a b] Bool))

(deftrait Display
  (show [x] String))

;; === Part 1: Enum types (nullary constructors only) ===

;; A simple three-variant enum
(deftype Color Red Green Blue)

;; Eq for an enum: match the first argument, then check the second.
;; Each arm matches a specific constructor pair.
(impl Eq Color
  (defn = [a b]
    (match a
      [Red   (match b [Red true   _ false])
       Green (match b [Green true _ false])
       Blue  (match b [Blue true  _ false])])))

;; Display for an enum: return the name as a string literal.
(impl Display Color
  (defn show [c]
    (match c
      [Red   "Red"
       Green "Green"
       Blue  "Blue"])))

;; Tests for Color Eq
(defn test-color-eq-same []
  (if (= Red Red) 1 0))                             ;; -> 1

(defn test-color-eq-diff []
  (if (= Red Blue) 1 0))                            ;; -> 0

(defn test-color-eq-all []
  ;; Verify each constructor equals itself
  (if (= Red Red)
    (if (= Green Green)
      (if (= Blue Blue) 1 0)
      0)
    0))                                              ;; -> 1

;; Tests for Color Display
(defn test-color-show-red []
  (if (str-eq (show Red) "Red") 1 0))               ;; -> 1

(defn test-color-show-green []
  (if (str-eq (show Green) "Green") 1 0))            ;; -> 1

(defn test-color-show-blue []
  (if (str-eq (show Blue) "Blue") 1 0))              ;; -> 1

;; === Part 2: An enum with more variants ===

(deftype Suit Clubs Diamonds Hearts Spades)

(impl Eq Suit
  (defn = [a b]
    (match a
      [Clubs    (match b [Clubs true    _ false])
       Diamonds (match b [Diamonds true _ false])
       Hearts   (match b [Hearts true   _ false])
       Spades   (match b [Spades true   _ false])])))

(impl Display Suit
  (defn show [s]
    (match s
      [Clubs    "Clubs"
       Diamonds "Diamonds"
       Hearts   "Hearts"
       Spades   "Spades"])))

(defn test-suit-eq []
  (if (= Hearts Hearts) 1 0))                       ;; -> 1

(defn test-suit-neq []
  (if (= Clubs Spades) 1 0))                        ;; -> 0

(defn test-suit-show []
  (if (str-eq (show Diamonds) "Diamonds") 1 0))      ;; -> 1

;; === Part 3: Data-carrying sum type ===

;; A monomorphic sum type with a mix of nullary and data constructors.
;; This is the pattern you would see for Option<Int>, Result<Int>, etc.
(deftype MaybeInt MissInt (HasInt [:Int val]))

;; Eq for a mixed type: nullary = nullary, data = data with field comparison.
(impl Eq MaybeInt
  (defn = [a b]
    (match a
      [MissInt  (match b [MissInt true _ false])
       (HasInt x) (match b [(HasInt y) (eq-i64 x y) _ false])])))

;; Display: nullary prints as name, data prints as "Name(value)"
(impl Display MaybeInt
  (defn show [m]
    (match m
      [MissInt  "MissInt"
       (HasInt x) (str-concat "HasInt(" (str-concat (int-to-string x) ")"))])))

;; Tests for MaybeInt Eq
(defn test-maybe-miss-eq []
  (if (= MissInt MissInt) 1 0))                     ;; -> 1

(defn test-maybe-has-eq []
  (if (= (HasInt 42) (HasInt 42)) 1 0))              ;; -> 1

(defn test-maybe-has-neq []
  (if (= (HasInt 1) (HasInt 2)) 1 0))                ;; -> 0

(defn test-maybe-mixed-neq []
  (if (= (HasInt 1) MissInt) 1 0))                   ;; -> 0

;; Tests for MaybeInt Display
(defn test-maybe-show-miss []
  (if (str-eq (show MissInt) "MissInt") 1 0))        ;; -> 1

(defn test-maybe-show-has []
  (if (str-eq (show (HasInt 42)) "HasInt(42)") 1 0)) ;; -> 1

;; === Part 4: Product type with fields ===

;; A simple product type (single constructor, multiple fields)
(deftype Point [:Int x :Int y])

(impl Eq Point
  (defn = [a b]
    (match a
      [(Point ax ay)
       (match b
         [(Point bx by)
          (if (eq-i64 ax bx) (eq-i64 ay by) false)])])))

(impl Display Point
  (defn show [p]
    (match p
      [(Point x y)
       (str-concat "Point("
         (str-concat (int-to-string x)
           (str-concat " "
             (str-concat (int-to-string y) ")"))))])))

;; Tests for Point Eq
(defn test-point-eq-same []
  (if (= (Point 3 4) (Point 3 4)) 1 0))             ;; -> 1

(defn test-point-eq-diff []
  (if (= (Point 3 4) (Point 5 6)) 1 0))             ;; -> 0

(defn test-point-eq-partial []
  (if (= (Point 3 4) (Point 3 5)) 1 0))             ;; -> 0

;; Tests for Point Display
(defn test-point-show []
  (if (str-eq (show (Point 3 4)) "Point(3 4)") 1 0))  ;; -> 1

(defn test-point-show-neg []
  (if (str-eq (show (Point (sub-i64 0 1) 0)) "Point(-1 0)") 1 0))  ;; -> 1

;; === Part 5: Using trait-dispatched equality in functions ===

;; With Eq defined, we can write functions that use = on our types.
(defn find-color [target c1 c2 c3]
  (if (= target c1) 1
    (if (= target c2) 2
      (if (= target c3) 3 0))))

(defn test-find-color []
  (find-color Green Red Green Blue))                 ;; -> 2

;; Combine show with string operations
(defn describe-point [p]
  (str-concat "The point is " (show p)))

(defn test-describe []
  (str-len (describe-point (Point 3 4))))            ;; -> 23 ("The point is Point(3 4)")

;; --- Sum results ---

;; test-color-eq-same:      1
;; test-color-eq-diff:      0
;; test-color-eq-all:       1
;; test-color-show-red:     1
;; test-color-show-green:   1
;; test-color-show-blue:    1
;; test-suit-eq:            1
;; test-suit-neq:           0
;; test-suit-show:          1
;; test-maybe-miss-eq:      1
;; test-maybe-has-eq:       1
;; test-maybe-has-neq:      0
;; test-maybe-mixed-neq:    0
;; test-maybe-show-miss:    1
;; test-maybe-show-has:     1
;; test-point-eq-same:      1
;; test-point-eq-diff:      0
;; test-point-eq-partial:   0
;; test-point-show:         1
;; test-point-show-neg:     1
;; test-find-color:         2
;; test-describe:           23
;; Total: 1+0+1+1+1+1+1+0+1+1+1+0+0+1+1+1+0+0+1+1+2+23 = 39

(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-color-eq-same)
      (add-i64 (test-color-eq-diff)
        (add-i64 (test-color-eq-all)
          (add-i64 (test-color-show-red)
            (add-i64 (test-color-show-green)
              (add-i64 (test-color-show-blue)
                (add-i64 (test-suit-eq)
                  (add-i64 (test-suit-neq)
                    (add-i64 (test-suit-show)
                      (add-i64 (test-maybe-miss-eq)
                        (add-i64 (test-maybe-has-eq)
                          (add-i64 (test-maybe-has-neq)
                            (add-i64 (test-maybe-mixed-neq)
                              (add-i64 (test-maybe-show-miss)
                                (add-i64 (test-maybe-show-has)
                                  (add-i64 (test-point-eq-same)
                                    (add-i64 (test-point-eq-diff)
                                      (add-i64 (test-point-eq-partial)
                                        (add-i64 (test-point-show)
                                          (add-i64 (test-point-show-neg)
                                            (add-i64 (test-find-color)
                                                     (test-describe))))))))))))))))))))))))
