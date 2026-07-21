;; testing/assertions/test.cl — self-tests for testing.assertions
;; (module testing.assertions.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`.
;;
;; THE HARNESS TESTING ITSELF. Every other stdlib self-test module reports
;; through `assert-eq`/`assert-true`/`assert-false`, so a bug here is invisible
;; in exactly the way that matters: an assertion that returned `None`
;; unconditionally would make the whole suite report green forever. That module
;; had no self-tests of its own until S115.
;;
;; The cases below therefore lean on the NEGATIVE side. `assert-eq` returning
;; `None` for equal values is the cheap half; what actually protects the suite
;; is that it returns `(Some …)` for UNEQUAL values, and those are the
;; `*-fails-on-*` cases. They are written by inspecting the returned Option
;; directly rather than by asserting with the function under test, which would
;; be circular.

(import [super [assert-eq assert-true assert-false]])
(import [compare.eq [=]])
(import [primitives [Option Some None Int Bool String str-concat]])

;; Inspect an assertion's RESULT without using an assertion to do it.
(defn- passed? "True when an assertion returned None (success)" [r] :Bool
  (match r [(Some _) false _ true]))

(defn- ok "None — this test passed" [] :(Option String)
  None)

(defn- expect "None when `cond` holds, else (Some why)" [:Bool cond :String why] :(Option String)
  (if cond None (Some why)))

;; ── assert-eq — positive ───────────────────────────────────────────────

(defn test-assert-eq-passes-on-equal-ints [] :(Option String)
  (expect (passed? (assert-eq 1 1)) "assert-eq 1 1 should pass"))

(defn test-assert-eq-passes-on-equal-strings [] :(Option String)
  (expect (passed? (assert-eq "a" "a")) "assert-eq \"a\" \"a\" should pass"))

(defn test-assert-eq-passes-on-equal-bools [] :(Option String)
  (expect (passed? (assert-eq true true)) "assert-eq true true should pass"))

;; ── assert-eq — negative (the half that protects every other module) ───

(defn test-assert-eq-fails-on-unequal-ints [] :(Option String)
  (expect (if (passed? (assert-eq 1 2)) false true)
          "assert-eq 1 2 should FAIL — a harness that passes here reports the whole suite green"))

(defn test-assert-eq-fails-on-unequal-strings [] :(Option String)
  (expect (if (passed? (assert-eq "a" "b")) false true)
          "assert-eq \"a\" \"b\" should FAIL"))

(defn test-assert-eq-fails-on-unequal-bools [] :(Option String)
  (expect (if (passed? (assert-eq true false)) false true)
          "assert-eq true false should FAIL"))

;; The failure REASON must name both values, or a red test says nothing useful.
(defn test-assert-eq-failure-reason-reports-both-values [] :(Option String)
  (expect (= "expected 1 but got 2" (match (assert-eq 1 2) [(Some why) why _ "<passed>"]))
          "assert-eq's failure reason must read `expected <a> but got <b>`"))

;; ── assert-true / assert-false ─────────────────────────────────────────

(defn test-assert-true-passes-on-true [] :(Option String)
  (expect (passed? (assert-true true)) "assert-true true should pass"))

(defn test-assert-true-fails-on-false [] :(Option String)
  (expect (if (passed? (assert-true false)) false true)
          "assert-true false should FAIL"))

(defn test-assert-false-passes-on-false [] :(Option String)
  (expect (passed? (assert-false false)) "assert-false false should pass"))

(defn test-assert-false-fails-on-true [] :(Option String)
  (expect (if (passed? (assert-false true)) false true)
          "assert-false true should FAIL"))

;; assert-true and assert-false are not the same function.
(defn test-assert-true-and-assert-false-disagree [] :(Option String)
  (expect (if (= (passed? (assert-true true)) (passed? (assert-false true))) false true)
          "assert-true and assert-false must disagree on the same input"))

(defn test-assert-true-failure-reason [] :(Option String)
  (expect (= "expected true but got false"
             (match (assert-true false) [(Some why) why _ "<passed>"]))
          "assert-true's failure reason should say what it expected"))

(defn test-assert-false-failure-reason [] :(Option String)
  (expect (= "expected false but got true"
             (match (assert-false true) [(Some why) why _ "<passed>"]))
          "assert-false's failure reason should say what it expected"))
