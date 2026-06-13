;; 17-display.cl -- User-defined traits and the Display pattern
;;
;; Example 15 showed built-in traits (Num, Eq, Ord) for operator dispatch.
;; This example shows how to define your own traits with deftrait and
;; implement them for different types with impl.
;;
;; The key pattern is Display -- a trait for converting values to strings:
;;
;;   (deftrait Display
;;     (show [self] String))
;;
;; Any type can implement Display by providing a show function.
;; This is how Cranelisp produces human-readable output from data types.
;;
;; Traits enable polymorphic dispatch: the same function name (show)
;; does different things depending on the type of its argument.

;; --- Defining a trait ---

;; Display: convert a value to its string representation.
;; The [self] parameter means the method is dispatched on the first arg's type.
(deftrait Display
  (show [self] String))

;; --- Implementing Display for primitive types ---

;; Each impl maps show to a type-specific conversion primitive.
(impl Display Int
  (defn show [x] (int-to-string x)))

(impl Display Float
  (defn show [x] (float-to-string x)))

(impl Display Bool
  (defn show [x] (bool-to-string x)))

;; --- Test Display on primitives ---

(defn test-show-int []
  (if (str-eq (show 42) "42") 1 0))                     ;; -> 1

(defn test-show-neg []
  (if (str-eq (show (sub-i64 0 7)) "-7") 1 0))          ;; -> 1

(defn test-show-bool []
  (if (str-eq (show true) "true") 1 0))                 ;; -> 1

;; --- Implementing Display for user-defined types ---

;; An enum type
(deftype Season Spring Summer Autumn Winter)

(impl Display Season
  (defn show [s]
    (match s
      [Spring "spring"
       Summer "summer"
       Autumn "autumn"
       Winter "winter"])))

(defn test-show-season []
  (if (str-eq (show Spring) "spring") 1 0))              ;; -> 1

(defn test-show-winter []
  (if (str-eq (show Winter) "winter") 1 0))              ;; -> 1

;; --- A custom trait: Measurable ---

;; Traits are not limited to Display. You can define any interface.
(deftrait Measurable
  (measure [self] Int))

;; ADT types
(deftype Segment [:Int length])
(deftype Rectangle [:Int width :Int height])

(impl Measurable Segment
  (defn measure [s]
    (match s [(Segment len) len])))

(impl Measurable Rectangle
  (defn measure [r]
    (match r [(Rectangle w h) (mul-i64 w h)])))

(defn test-measure-segment []
  (measure (Segment 42)))                                ;; -> 42

(defn test-measure-rect []
  (measure (Rectangle 6 7)))                             ;; -> 42

;; --- Display for ADT types ---

(impl Display Segment
  (defn show [s]
    (match s
      [(Segment len) (str-concat "Segment(" (str-concat (int-to-string len) ")"))])))

(impl Display Rectangle
  (defn show [r]
    (match r
      [(Rectangle w h)
        (str-concat "Rectangle("
          (str-concat (int-to-string w)
            (str-concat "x"
              (str-concat (int-to-string h) ")"))))])))

(defn test-show-segment []
  (if (str-eq (show (Segment 10)) "Segment(10)") 1 0))            ;; -> 1

(defn test-show-rect []
  (if (str-eq (show (Rectangle 3 4)) "Rectangle(3x4)") 1 0))     ;; -> 1

;; --- Polymorphic use with concrete types ---

;; A function that shows a value and returns its string length.
;; The compiler resolves which show to call based on the argument type.
(defn show-len-int [x] (str-len (show x)))
(defn show-len-bool [x] (str-len (show x)))

(defn test-show-len-int []
  (show-len-int 12345))                                  ;; -> 5

(defn test-show-len-bool []
  (show-len-bool false))                                 ;; -> 5

;; --- Combining traits ---

;; A type that implements both Display and Measurable
(defn test-both-traits []
  (let [r (Rectangle 12 5)]
    (add-i64 (measure r) (str-len (show r)))))           ;; -> 60 + 15 = 75

;; Expected: 1+1+1+1+1+42+42+1+1+5+5+75 = 176
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-show-int)
      (add-i64 (test-show-neg)
        (add-i64 (test-show-bool)
          (add-i64 (test-show-season)
            (add-i64 (test-show-winter)
              (add-i64 (test-measure-segment)
                (add-i64 (test-measure-rect)
                  (add-i64 (test-show-segment)
                    (add-i64 (test-show-rect)
                      (add-i64 (test-show-len-int)
                        (add-i64 (test-show-len-bool)
                                 (test-both-traits))))))))))))))
