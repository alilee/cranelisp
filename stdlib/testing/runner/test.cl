;; testing/runner/test.cl — self-tests for testing.runner (module
;; testing.runner.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`. Exercises the runner's pure helpers (run-one / present-one /
;; tally-line / passed?) via the in-language harness.

(import [super [run-one present-one tally-line passed?
                Outcome Passed Failed Panicked Tally]])
(import [testing.assertions [assert-true assert-false assert-eq]])
(import [primitives [Option Pair None Some String Bool]])

(defn- passed-outcome? [:Outcome o] :Bool
  (match o [(Passed _) true (Failed _ _) false (Panicked _ _) false]))

(defn- failed-outcome? [:Outcome o] :Bool
  (match o [(Failed _ _) true (Passed _) false (Panicked _ _) false]))

(defn test-run-one-pass [] :(Option String)
  (assert-true (passed-outcome? (run-one (Pair "t" (fn [] None))))))

(defn test-run-one-fail [] :(Option String)
  (assert-true (failed-outcome? (run-one (Pair "t" (fn [] (Some "why")))))))

(defn test-passed?-empty [] :(Option String)
  (assert-true (passed? (Tally 3 0 0))))

(defn test-passed?-with-fail [] :(Option String)
  (assert-false (passed? (Tally 1 1 0))))

(defn test-present-one-pass [] :(Option String)
  (assert-eq "t ... ok" (present-one (Passed "t"))))

(defn test-tally-line [] :(Option String)
  (assert-eq "2 passed, 1 failed, 0 panicked"
             (tally-line (Tally 2 1 0))))
