;; tests.cl — the exemplar's test runner. It calls each module's `test-*`
;; function directly and exits with the number that pass (`score`: `None` → 1,
;; `(Some why)` → 0). A green run exits 43, in the default parallel mode and
;; under `CRANELISP_NO_LENIENT=1`; agreement between the two is the
;; parallel ≡ serial guard (`solver/test-solve-parallel-equiv`).
;;
;; `solver/test-hard-puzzle` is not called: it passes, but runs about ten times
;; longer than `solver/test-easy-puzzle` (exemplar/plan-exemplar.md,
;; "Copy-per-guess performance").

(import [primitives [Pure]])

(import [grid [test-full-mask test-pow2 test-bit-set? test-bit-clear
               test-bit-count test-bit-lowest test-row-of test-col-of
               test-box-of test-peers-count test-make-grid-wrong-length
               test-cell-at-and-set test-is-solved-all-given
               test-is-solved-with-candidates test-set-cell]])
(import [solver [test-eliminate-removes-digit test-eliminate-no-effect-on-given
                 test-eliminate-determines-cell test-eliminate-contradiction
                 test-easy-puzzle test-unsolvable test-solve-parallel-equiv]])
(import [html [test-form-page-has-inputs test-form-page-has-action
               test-form-page-has-table test-wrap-tag test-td
               test-error-page-has-message test-error-page-has-link
               test-not-found-page-has-path test-not-found-page-has-link
               test-solution-page-has-digits test-solution-page-given-class
               test-solution-page-mixed]])
(import [form [test-parse-simple test-empty-values-produce-dots
               test-result-length test-url-decode test-field-index-valid
               test-field-index-invalid test-last-position
               test-multiple-digits test-malformed-body]])

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
    (+ (score (test-not-found-page-has-path))
    (+ (score (test-not-found-page-has-link))
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
    (+ (score (test-multiple-digits))
       (score (test-malformed-body))))))))))))))))))))))))))))))))))))))))))))))
