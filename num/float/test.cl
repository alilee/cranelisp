(import
  [super
   [abs-float sign-float negate-float min-float max-float
    clamp-float]])
(import [testing.assertions [assert-eq]])
(import [primitives [Option String]])
(defn test-abs-float-neg [] : (Option String)
  (assert-eq 2.5 (abs-float -2.5)))
(defn test-sign-float-pos [] : (Option String)
  (assert-eq 1.0 (sign-float 3.0)))
(defn test-negate-float [] : (Option String)
  (assert-eq -4.0 (negate-float 4.0)))
(defn test-min-float [] : (Option String)
  (assert-eq 1.0 (min-float 1.0 2.0)))
(defn test-max-float [] : (Option String)
  (assert-eq 2.0 (max-float 1.0 2.0)))
(defn test-clamp-float-lo [] : (Option String)
  (assert-eq 0.0 (clamp-float -1.0 0.0 9.0)))