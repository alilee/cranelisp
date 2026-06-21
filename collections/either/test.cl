(import
  [super
   [Either Left Right is-left? is-right? from-left from-right
    map-left
    either]])
(import
  [testing.assertions [assert-true assert-false assert-eq]])
(import [primitives [Option String Int add-i64]])
(defn test-is-left [] : (Option String)
  (assert-true (is-left? : (Either Int String) (Left 1))))
(defn test-is-right [] : (Option String)
  (assert-true (is-right? : (Either String Int) (Right 1))))
(defn test-left-not-right [] : (Option String)
  (assert-false (is-right? : (Either Int String) (Left 1))))
(defn test-from-left [] : (Option String)
  (assert-eq 7 (from-left 0 : (Either Int String) (Left 7))))
(defn test-from-right-default [] : (Option String)
  (assert-eq "d"
    (from-right "d" : (Either Int String) (Left 7))))
(defn- inc [:Int x] :Int (add-i64 x 1))
(defn test-either-left [] : (Option String)
  (assert-eq 2 (either inc inc : (Either Int Int) (Left 1))))