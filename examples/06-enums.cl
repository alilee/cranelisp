;; 06-enums.cl -- Enum types and pattern matching
;;
;; (deftype Name Variant1 Variant2 ...)
;;
;; Defines a new type with named constructors (no fields in Ring 0).
;; Each variant is a distinct value of the type.
;;
;; (match scrutinee [Pattern1 body1 Pattern2 body2 ...])
;;
;; Patterns are tested top to bottom. Patterns can be:
;;   - Constructor names (e.g., Red, North)
;;   - Wildcard _ (matches anything, binds nothing)
;;   - Variable names (matches anything, binds the value)

;; A simple three-variant enum
(deftype Color Red Green Blue)

;; Convert a Color to an integer using match
(defn color-to-int [c]
  (match c
    [Red   1
     Green 2
     Blue  3]))

;; Check if a color is red using wildcard for non-red cases
(defn is-red [c]
  (match c
    [Red true
     _   false]))

;; A four-variant enum for compass directions
(deftype Direction North South East West)

;; Compute the opposite direction
(defn opposite [d]
  (match d
    [North South
     South North
     East  West
     West  East]))

;; Check if a direction is on the vertical axis
(defn is-vertical [d]
  (match d
    [North true
     South true
     _     false]))

;; A two-variant enum acts like a boolean
(deftype YesNo Yes No)

(defn yes-no-to-int [yn]
  (match yn
    [Yes 1
     No  0]))

;; Variable patterns bind the matched value:
;; match Red with "Red -> 0, anything-else -> 99"
(defn red-or-other [c]
  (match c
    [Red 0
     x   99]))

;; Convert direction to an integer
(defn dir-to-int [d]
  (match d
    [North 1
     South 2
     East  3
     West  4]))

;; Expected: 2 + 0 + 1 + 1 + 1 + 99 = 104
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (color-to-int Green)
      (add-i64 (if (is-red Blue) 1 0)
        (add-i64 (if (is-vertical North) 1 0)
          (add-i64 (yes-no-to-int Yes)
            (add-i64 (dir-to-int (opposite South))
                     (red-or-other Blue))))))))
