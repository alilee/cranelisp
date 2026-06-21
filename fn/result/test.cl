(import
  [super
   [Result Ok Err is-ok? is-err? unwrap-or map-ok map-err
    and-then]])
(import
  [testing.assertions [assert-true assert-false assert-eq]])
(import [primitives [Option String Int add-i64]])
(defn test-is-ok [] : (Option String)
  (assert-true (is-ok? : (Result Int String) (Ok 1))))
(defn test-is-err [] : (Option String)
  (assert-true (is-err? : (Result Int String) (Err "boom"))))
(defn test-ok-not-err [] : (Option String)
  (assert-false (is-err? : (Result Int String) (Ok 1))))
(defn test-unwrap-or-ok [] : (Option String)
  (assert-eq 5 (unwrap-or 0 : (Result Int String) (Ok 5))))
(defn test-unwrap-or-err [] : (Option String)
  (assert-eq 0 (unwrap-or 0 : (Result Int String) (Err "x"))))
(defn test-map-ok [] : (Option String)
  (let [r : (Result Int String) (Ok 2)]
    (assert-eq 3 (unwrap-or 0 (map-ok (fn [x] (add-i64 x 1)) r)))))
(defn- inc-ok [:Int x] : (Result Int String)
  (Ok (add-i64 x 1)))
(defn test-and-then-ok [] : (Option String)
  (let [r : (Result Int String) (Ok 3)]
    (assert-eq 4 (unwrap-or 0 (and-then inc-ok r)))))