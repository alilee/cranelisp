;; shapes.cl -- A module defining geometric types and operations
;;
;; Demonstrates modules that define types (deftype) alongside functions.
;; Types and constructors are accessed as shapes/Point, shapes/Circle, etc.

;; A 2D point
(deftype Point [:Int x :Int y])

;; A circle with center and radius
(deftype Circle [:Int cx :Int cy :Int r])

;; Construct a point at a given position
(defn make-point [x y] (Point x y))

;; Squared distance from origin
(defn distance-sq [p]
  (match p [(Point x y) (add-i64 (mul-i64 x x) (mul-i64 y y))]))

;; Approximate area of a circle (3 * r^2, integer approx)
(defn area-approx [c]
  (match c [(Circle cx cy r) (mul-i64 3 (mul-i64 r r))]))
