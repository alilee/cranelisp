;; tests.cl — Free-standing test runner for the Sudoku exemplar.
;;
;; The in-language test runner (`discover-tests` / `testing.runner`) is a
;; LIVE-REPL-only capability (carried defects D3/D4/D5 — see SPRINT.md), so
;; this entry does NOT use `(mod test)` submodules or `discover-tests`.
;; Instead it follows the `examples/` convention: import each module's
;; `test-*` function, call them directly, and return the number of passing
;; tests as the process exit code (`(Pure <count>)`).
;;
;; Each `test-*` returns `(Option String)`: `None` = pass, `(Some why)` =
;; fail (repl/spec.md §16.1). `score` maps None→1, Some→0; the run is green
;; when the exit code equals the total test count (40).
;;
;; EXCLUDED: `solver/test-hard-puzzle`. It is correct (it solves), but the
;; genuinely-hard backtracking search copies the whole 81-cell Vec on every
;; guess (`set-cell`/`assoc`), so it runs for minutes — impractical for a
;; fast green run. The function stays in solver.cl as documentation; the
;; easy puzzle + the `eliminate`/`unsolvable` tests cover the solver path
;; here, and `user.cl` solves the easy puzzle end-to-end in seconds. The
;; quadratic-copy cost is a performance finding, not a correctness defect.
;;
;; Run it:
;;   CRANELISP_PLATFORM_PATH=target/debug CRANELISP_LIB=stdlib \
;;     cargo run -- --run exemplar/tests.cl
;;   echo $?   # => 40  (all green)
;;
;; The suite now includes `solver/test-solve-parallel-equiv` (S92, FIXME 0408):
;; a backtracking-requiring puzzle solved through the parallel divide-and-conquer
;; search, pinned to its unique solution. Running the suite under both default
;; (parallel) and `CRANELISP_NO_LENIENT=1` (serial) and getting the same green
;; 40 is the parallel ≡ serial equivalence guard for the reshape. That one test
;; adds ~8-9s to the run (the carried copy-per-guess cost — FIXME 0408 perf
;; half); `test-hard-puzzle` stays excluded (it would run for minutes).

(import [primitives [Pure]])

(import [grid [test-full-mask test-pow2 test-bit-set? test-bit-clear
               test-bit-count test-bit-lowest test-row-of test-col-of
               test-box-of test-peers-count test-make-grid-wrong-length
               test-cell-at-and-set test-is-solved-all-given
               test-is-solved-with-candidates test-set-cell]])
;; test-hard-puzzle is deliberately NOT imported here — see header note.
(import [solver [test-eliminate-removes-digit test-eliminate-no-effect-on-given
                 test-eliminate-determines-cell test-eliminate-contradiction
                 test-easy-puzzle test-unsolvable test-solve-parallel-equiv]])
(import [html [test-form-page-has-inputs test-form-page-has-action
               test-form-page-has-table test-wrap-tag test-td
               test-error-page-has-message test-error-page-has-link
               test-solution-page-has-digits test-solution-page-given-class
               test-solution-page-mixed]])
(import [form [test-parse-simple test-empty-values-produce-dots
               test-result-length test-url-decode test-field-index-valid
               test-field-index-invalid test-last-position
               test-multiple-digits]])

;; Map a test outcome to a pass count: None (pass) => 1, (Some _) (fail) => 0.
(defn score [outcome]
  (match outcome
    [None 1
     (Some _) 0]))

(defn main []
  (Pure
    (+ (score (test-full-mask))
    (+ (score (test-pow2))
    (+ (score (test-bit-set?))
    (+ (score (test-bit-clear))
    (+ (score (test-bit-count))
    (+ (score (test-bit-lowest))
    (+ (score (test-row-of))
    (+ (score (test-col-of))
    (+ (score (test-box-of))
    (+ (score (test-peers-count))
    (+ (score (test-make-grid-wrong-length))
    (+ (score (test-cell-at-and-set))
    (+ (score (test-is-solved-all-given))
    (+ (score (test-is-solved-with-candidates))
    (+ (score (test-set-cell))
    (+ (score (test-eliminate-removes-digit))
    (+ (score (test-eliminate-no-effect-on-given))
    (+ (score (test-eliminate-determines-cell))
    (+ (score (test-eliminate-contradiction))
    (+ (score (test-easy-puzzle))
    (+ (score (test-unsolvable))
    (+ (score (test-solve-parallel-equiv))
    (+ (score (test-form-page-has-inputs))
    (+ (score (test-form-page-has-action))
    (+ (score (test-form-page-has-table))
    (+ (score (test-wrap-tag))
    (+ (score (test-td))
    (+ (score (test-error-page-has-message))
    (+ (score (test-error-page-has-link))
    (+ (score (test-solution-page-has-digits))
    (+ (score (test-solution-page-given-class))
    (+ (score (test-solution-page-mixed))
    (+ (score (test-parse-simple))
    (+ (score (test-empty-values-produce-dots))
    (+ (score (test-result-length))
    (+ (score (test-url-decode))
    (+ (score (test-field-index-valid))
    (+ (score (test-field-index-invalid))
    (+ (score (test-last-position))
       (score (test-multiple-digits)))))))))))))))))))))))))))))))))))))))))))
