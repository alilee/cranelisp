;; compare/ord/test.cl — self-tests for compare.ord (module compare.ord.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`. HARNESS-FREE inline-`if` shape (None = pass). String ordering
;; is omitted by design (see compare/ord.cl), so there is no String self-test.

(import [super [Ord < > <= >=]])
(import [primitives [Option Some None String Bool]])

(defn test-int-lt [] :(Option String)
  (if (< 1 2) None (Some "expected (< 1 2) true")))

(defn test-int-gt [] :(Option String)
  (if (> 3 2) None (Some "expected (> 3 2) true")))

(defn test-int-le-equal [] :(Option String)
  (if (<= 2 2) None (Some "expected (<= 2 2) true")))

(defn test-int-ge [] :(Option String)
  (if (>= 5 4) None (Some "expected (>= 5 4) true")))

(defn test-int-not-lt [] :(Option String)
  (if (< 2 1) (Some "expected (< 2 1) false") None))

(defn test-bool-lt [] :(Option String)
  (if (< false true) None (Some "expected (< false true) true")))

(defn test-bool-not-lt [] :(Option String)
  (if (< true true) (Some "expected (< true true) false") None))
