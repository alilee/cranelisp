(import [super [Option Some None]])
(import [primitives [String Int eq-i64]])
(defn- some-val? [o :Int expect] : (Option String)
  (match o
    [(Some v)
     (if (eq-i64 v expect) None (Some "Some carried wrong value"))
     None
     (Some "expected Some, got None")]))
(defn test-some-carries-value [] : (Option String)
  (some-val? (Some 7) 7))
(defn test-none-matches [] : (Option String)
  (match : (Option Int) None
    [(Some _) (Some "expected None, got Some") None None]))