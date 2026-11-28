;; 01-integers.cl -- Integer literals and arithmetic
;;
;; Cranelisp integers are signed 64-bit values.
;; The core language exposes monomorphic named primitives for arithmetic:
;;   add-i64, sub-i64, mul-i64, div-i64
;;
;; The zero-argument function named `main` is the program entry point.
;; Its result must be an IO value. The built-in function pure lifts a
;; computed integer n into (IO Int). When the runtime executes (pure n),
;; it obtains n without an effect and uses its low byte as the exit code.
;; This is the entry-point recipe for now; example 21 teaches opaque IO
;; and sequencing.
;; The examples-local prelude supplies these primitive names without
;; loading the standard library (see lib/README.md).

;; Addition
(defn add-example [] (add-i64 3 4))

;; Subtraction
(defn sub-example [] (sub-i64 10 3))

;; Multiplication
(defn mul-example [] (mul-i64 6 7))

;; Division (integer, truncating toward zero)
(defn div-example [] (div-i64 17 5))

;; Nested arithmetic: (3 * 4) + (10 - 5)
(defn nested [] (add-i64 (mul-i64 3 4) (sub-i64 10 5)))

;; Negation via subtraction from zero (no int-neg primitive)
(defn negate-example [] (sub-i64 0 7))

;; The entry point combines the results to verify they all work.
;; Expected: 7 + 7 + 42 + 3 + 17 + (-7) = 69
(defn main []
  ;; Lift the combined result with the built-in function pure, giving main
  ;; an (IO Int) result. The runtime uses the Int's low byte as the exit code.
  (pure
    (add-i64 (add-example)
      (add-i64 (sub-example)
        (add-i64 (mul-example)
          (add-i64 (div-example)
            (add-i64 (nested)
                     (negate-example))))))))
