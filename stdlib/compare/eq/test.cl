;; compare/eq/test.cl — self-tests for compare.eq (module compare.eq.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`.
;;
;; HARNESS-FREE: `testing.assertions` depends on `compare.eq` (its `assert-eq`
;; carries an `Eq` bound), so importing the harness here would form a load
;; cycle. Tests return `(Option String)` directly via inline `if` — None = pass.

(import [super [Eq = !=]])
(import [primitives [Option Some None Result Ok Err Pair String Int Bool]])

(defn test-int-eq [] :(Option String)
  (if (= 1 1) None (Some "expected (= 1 1) true")))

(defn test-int-neq [] :(Option String)
  (if (= 1 2) (Some "expected (= 1 2) false") None))

(defn test-int-bang-eq [] :(Option String)
  (if (!= 1 2) None (Some "expected (!= 1 2) true")))

(defn test-bool-eq [] :(Option String)
  (if (= true true) None (Some "expected (= true true) true")))

(defn test-string-eq [] :(Option String)
  (if (= "a" "a") None (Some "expected string eq true")))

(defn test-string-bang-eq [] :(Option String)
  (if (!= "a" "b") None (Some "expected string neq true")))

;; ── Option, Result, Pair ─────────────────────────────────────────────

(defn- expect [ok why] :(Option String) (if ok None (Some why)))

(defn test-option-eq-same-payload [] :(Option String)
  (expect (= (Some 1) (Some 1)) "expected (Some 1) = (Some 1)"))

(defn test-option-eq-payload-differs [] :(Option String)
  (expect (!= (Some 1) (Some 2)) "expected (Some 1) != (Some 2)"))

(defn test-option-eq-ctor-differs [] :(Option String)
  (expect (!= (Some 1) None) "expected (Some 1) != None"))

(defn test-option-eq-none [] :(Option String)
  (expect (= :(Option Int) None None) "expected None = None"))

(defn test-option-eq-nested [] :(Option String)
  (expect (!= (Some (Some 1)) (Some (Some 2))) "expected nested payloads to compare"))

(defn test-result-eq-ok [] :(Option String)
  (expect (= :(Result Int String) (Ok 1) (Ok 1)) "expected (Ok 1) = (Ok 1)"))

(defn test-result-eq-err-payload-differs [] :(Option String)
  (expect (!= :(Result Int String) (Err "a") (Err "b")) "expected (Err a) != (Err b)"))

(defn test-result-eq-ctor-differs [] :(Option String)
  (expect (!= :(Result Int Int) (Ok 1) (Err 1)) "expected (Ok 1) != (Err 1)"))

(defn test-pair-eq-same [] :(Option String)
  (expect (= (Pair 1 "a") (Pair 1 "a")) "expected equal pairs"))

(defn test-pair-eq-first-differs [] :(Option String)
  (expect (!= (Pair 1 "a") (Pair 2 "a")) "expected first component to count"))

(defn test-pair-eq-second-differs [] :(Option String)
  (expect (!= (Pair 1 "a") (Pair 1 "b")) "expected second component to count"))
