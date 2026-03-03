;; Derive trait implementations automatically for ADTs
;;
;; `derive` generates trait impls from the type definition.
;; Supported traits: Eq, Ord, Display

(platform stdio)
(import [platform.stdio [*]])

;; Enum type with all three traits
(derive [Eq Ord Display]
  (deftype Color Red Green Blue))

(defn main []
  (do
    ;; Enum equality
    (print (if (= Red Red) "Red = Red: true\n" "Red = Red: false\n"))
    (print (if (= Red Blue) "Red = Blue: true\n" "Red = Blue: false\n"))

    ;; Enum ordering (by declaration order)
    (print (if (< Red Green) "Red < Green: true\n" "Red < Green: false\n"))
    (print (if (<= Red Red) "Red <= Red: true\n" "Red <= Red: false\n"))

    ;; Enum display
    (print (str-concat "show Red = " (str-concat (show Red) "\n")))
    (print (str-concat "show Green = " (str-concat (show Green) "\n")))
    (print (str-concat "show Blue = " (str-concat (show Blue) "\n")))

    (pure 0)))
