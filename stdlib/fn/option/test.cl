;; fn/option/test.cl — self-tests for fn.option (module fn.option.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod test)`. HARNESS-FREE: `testing.assertions` depends on `fn.option`
;; (returns `(Option String)`), so importing the harness here forms a load
;; cycle. Tests construct/match Some & None and return `(Option String)`.

(import [super [Option Some None]])
(import [primitives [String Int eq-i64]])

(defn- some-val? [o :Int expect] :(Option String)
  (match o
    [(Some v) (if (eq-i64 v expect) None (Some "Some carried wrong value"))
     None     (Some "expected Some, got None")]))

(defn test-some-carries-value [] :(Option String)
  (some-val? (Some 7) 7))

(defn test-none-matches [] :(Option String)
  (match :(Option Int) None
    [(Some _) (Some "expected None, got Some")
     None     None]))
