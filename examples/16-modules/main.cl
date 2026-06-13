;; 16-modules -- Multi-file programs with modules
;;
;; Cranelisp organizes code into modules. Each source file is a module.
;; The main file declares its dependencies with (mod name), which tells
;; the compiler to look for name.cl in the same directory.
;;
;; Functions, types, and constructors from another module are accessed
;; using qualified names: module/name.
;;
;;   (mod math)                   ;; declares dependency on math.cl
;;   (math/double 21)             ;; calls math module's double function
;;   (shapes/Point 3 4)           ;; constructs shapes module's Point type
;;
;; A project can have multiple modules. Each module is compiled
;; independently and can define its own types and functions.
;;
;; This example has two helper modules:
;;   math.cl   -- arithmetic utility functions
;;   shapes.cl -- geometric types and operations

(mod math)
(mod shapes)

;; --- Using functions from the math module ---

;; Qualified calls: module-name/function-name
(defn test-double []
  (math/double 21))                                     ;; -> 42

(defn test-triple []
  (math/triple 10))                                     ;; -> 30

(defn test-square []
  (math/square 7))                                      ;; -> 49

(defn test-abs []
  (math/abs (sub-i64 0 7)))                             ;; -> 7

(defn test-sum-of-sq []
  (math/sum-of-squares 3 4))                            ;; -> 25

;; --- Using types and constructors from the shapes module ---

;; Constructors are qualified just like functions
(defn test-point []
  (let [p (shapes/make-point 3 4)]
    (shapes/distance-sq p)))                            ;; -> 25

;; Constructors can be called directly with qualified names
(defn test-circle []
  (shapes/area-approx (shapes/Circle 0 0 5)))          ;; -> 75

;; --- Combining modules ---

;; Use math functions on values from shapes
(defn test-combined []
  (math/double (shapes/distance-sq (shapes/Point 3 4))))  ;; -> 50

;; Expected: 42 + 30 + 49 + 7 + 25 + 25 + 75 + 50 = 303
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-double)
      (add-i64 (test-triple)
        (add-i64 (test-square)
          (add-i64 (test-abs)
            (add-i64 (test-sum-of-sq)
              (add-i64 (test-point)
                (add-i64 (test-circle)
                         (test-combined))))))))))
