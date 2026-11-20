;; compare/ord/test.cl — self-tests for compare.ord (module compare.ord.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`. HARNESS-FREE inline-`if` shape (None = pass). String ordering
;; is omitted by design (see compare/ord.cl), so there is no String self-test.

(import [super [Ord < > <= >=]])
(import [primitives [Option Some None Result Ok Err Pair String Int Bool]])

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

;; ── Option, Result, Pair ─────────────────────────────────────────────

(defn- expect [ok why] :(Option String) (if ok None (Some why)))

(defn test-option-none-lt-some [] :(Option String)
  (expect (< None (Some 0)) "expected None < (Some 0)"))

(defn test-option-some-not-lt-none [] :(Option String)
  (expect (if (< (Some 0) None) false true) "expected not (Some 0) < None"))

(defn test-option-payload-decides [] :(Option String)
  (expect (< (Some 1) (Some 2)) "expected (Some 1) < (Some 2)"))

(defn test-option-equal-is-not-lt [] :(Option String)
  (expect (if (< (Some 1) (Some 1)) false true) "expected not (Some 1) < (Some 1)"))

(defn test-option-le-ge-when-equal [] :(Option String)
  (expect (if (<= (Some 1) (Some 1)) (>= (Some 1) (Some 1)) false) "expected <= and >= on equal"))

(defn test-option-gt [] :(Option String)
  (expect (> (Some 2) None) "expected (Some 2) > None"))

(defn test-result-ok-lt-err [] :(Option String)
  (expect (< :(Result Int Int) (Ok 9) (Err 0)) "expected (Ok 9) < (Err 0)"))

(defn test-result-err-not-lt-ok [] :(Option String)
  (expect (if (< :(Result Int Int) (Err 0) (Ok 9)) false true) "expected not (Err 0) < (Ok 9)"))

(defn test-result-payload-decides [] :(Option String)
  (expect (< :(Result Int Int) (Err 1) (Err 2)) "expected (Err 1) < (Err 2)"))

(defn test-pair-first-decides [] :(Option String)
  (expect (< (Pair 1 9) (Pair 2 0)) "expected (Pair 1 9) < (Pair 2 0)"))

(defn test-pair-first-decides-against [] :(Option String)
  (expect (if (< (Pair 2 0) (Pair 1 9)) false true) "expected not (Pair 2 0) < (Pair 1 9)"))

(defn test-pair-second-breaks-tie [] :(Option String)
  (expect (< (Pair 1 2) (Pair 1 3)) "expected (Pair 1 2) < (Pair 1 3)"))

(defn test-pair-le-false-when-greater [] :(Option String)
  (expect (if (<= (Pair 1 3) (Pair 1 2)) false true) "expected not (Pair 1 3) <= (Pair 1 2)"))
