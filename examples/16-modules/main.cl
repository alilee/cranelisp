;; 16-modules -- Multi-file programs with modules
;;
;; Cranelisp organizes code into modules. Each source file is a module.
;; The main file declares its submodules with (mod name), which tells
;; the compiler to look for the nested child file main/name.cl (per
;; spec/08-modules.md §8.2.5: a bare (mod name) resolves the NESTED
;; child {stem}/{name}.cl, never a sibling file).
;;
;; Because the children live under main/, their module identities are
;; nested: main/math.cl is module "main.math", main/shapes.cl is module
;; "main.shapes". Functions, types, and constructors from another module
;; are accessed using the fully-qualified module path: module-path/name.
;;
;;   (mod math)                       ;; loads nested child main/math.cl
;;   (main.math/double 21)            ;; calls main.math module's double
;;   (main.shapes/Point 3 4)          ;; constructs main.shapes' Point type
;;
;; A project can have multiple modules. Each module is compiled
;; independently and can define its own types and functions.
;;
;; This example has two helper modules, both nested under main/:
;;   main/math.cl   -- arithmetic utility functions  (module main.math)
;;   main/shapes.cl -- geometric types and operations (module main.shapes)

(mod math)
(mod shapes)

;; The entry module imports the primitives it uses directly. (A project
;; entry in a subdirectory is its own project root, so it does not pick up
;; an ancestor lib-dir prelude — every module names the primitives it uses,
;; keeping the example free-standing per spec/08-modules.md §8.3.)
(import [primitives [Pure add-i64 sub-i64]])

;; --- Using functions from the main.math module ---

;; Qualified calls: module-path/function-name
(defn test-double []
  (main.math/double 21))                                ;; -> 42

(defn test-triple []
  (main.math/triple 10))                                ;; -> 30

(defn test-square []
  (main.math/square 7))                                 ;; -> 49

(defn test-abs []
  (main.math/abs (sub-i64 0 7)))                        ;; -> 7

(defn test-sum-of-sq []
  (main.math/sum-of-squares 3 4))                       ;; -> 25

;; --- Using types and constructors from the main.shapes module ---

;; Constructors are qualified just like functions
(defn test-point []
  (let [p (main.shapes/make-point 3 4)]
    (main.shapes/distance-sq p)))                       ;; -> 25

;; Constructors can be called directly with qualified names
(defn test-circle []
  (main.shapes/area-approx (main.shapes/Circle 0 0 5))) ;; -> 75

;; --- Combining modules ---

;; Use math functions on values from shapes
(defn test-combined []
  (main.math/double
    (main.shapes/distance-sq (main.shapes/Point 3 4)))) ;; -> 50

;; Expected sum: 42 + 30 + 49 + 7 + 25 + 25 + 75 + 50 = 303.
;; The process exit code is the low byte of that Int, so the observed
;; exit is 303 mod 256 = 47.
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (low byte preserved).
  (Pure
    (add-i64 (test-double)
      (add-i64 (test-triple)
        (add-i64 (test-square)
          (add-i64 (test-abs)
            (add-i64 (test-sum-of-sq)
              (add-i64 (test-point)
                (add-i64 (test-circle)
                         (test-combined))))))))))
