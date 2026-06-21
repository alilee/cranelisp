(import
  [super
   [List Nil Cons empty? length first rest fold reverse
    map-list
    filter-list
    nth]])
(import
  [testing.assertions [assert-true assert-false assert-eq]])
(import
  [primitives [Option Some None String Int add-i64 eq-i64]])
(defn- l123 [] : (List Int) (Cons 1 (Cons 2 (Cons 3 Nil))))
(defn test-empty-nil [] : (Option String)
  (assert-true (empty? : (List Int) Nil)))
(defn test-not-empty [] : (Option String)
  (assert-false (empty? (l123))))
(defn test-length [] : (Option String)
  (assert-eq 3 (length (l123))))
(defn test-fold-sum [] : (Option String)
  (assert-eq 6 (fold (fn [acc x] (add-i64 acc x)) 0 (l123))))
(defn test-reverse-length [] : (Option String)
  (assert-eq 3 (length (reverse (l123)))))
(defn test-first-some [] : (Option String)
  (match (first (l123))
    [(Some h) (if (eq-i64 h 1) None (Some "first wrong")) None
     (Some "expected Some")]))
(defn test-map-list-length [] : (Option String)
  (assert-eq 3
    (length (map-list (fn [x] (add-i64 x 1)) (l123)))))