(deftype Point [:Int x :Int y])

(defn make-point [:Int x :Int y] :Point (Point x y))

(defn- internal [:Int x] :Int (* x x))
