;; testing/runner.cl — Test runner helpers and check macro
;;
;; Provides:
;;   check         — macro to chain assertions (returns first failure)
;;   run-tests-pass-default  — default pass fold fn for run-tests
;;   run-tests-fail-default  — default fail fold fn for run-tests
;;   run-tests-report        — convenience: run all tests, return report string
;;
;; The check macro chains (Option String) assertions, short-circuiting on
;; the first Some (failure). The run-tests-* functions are fold callbacks
;; for the (run-tests init pass-fn fail-fn) special form.
;;
;; Spec: plan-stdlib.md §3.3

(import [primitives [Trace TraceCall]])
(import [fn.option [Option Some None]])
(import [macros [SexpSym SexpStr SexpList SCons SNil Sexp SList]])
(import [core.trace [trace-show-tree]])

;; ── check macro ──────────────────────────────────────────────────────
;; Chains assertions: returns first Some (failure), short-circuits.
;; (check a b c) expands to:
;;   (match a [(Some f) (Some f) None (match b [(Some f) (Some f) None c])])

(defmacro check "Chain assertions, returning first failure"
  ([x] x)
  ([x & rest]
    `(match ~x
       [(Some __f__) (Some __f__)
        None (check ~@rest)])))

;; ── run-tests helpers ────────────────────────────────────────────────
;; Default fold functions for (run-tests init pass-fn fail-fn).
;; Accumulator is a String (the report text).

(defn run-tests-pass-default "Append a '... ok' line to the report string"
  [:String acc :String name :Int nanos] :String
  (str-concat acc (str-concat "  " (str-concat name " ... ok\n"))))

(defn run-tests-fail-default "Append a '... FAILED' line with reason and trace tree to the report string"
  [:String acc :String name :Int nanos :String reason :Trace trace] :String
  (str-concat acc
    (str-concat "  "
      (str-concat name
        (str-concat " ... FAILED: "
          (str-concat reason
            (str-concat "\n"
              (trace-show-tree trace))))))))

(defn run-tests-report "Run all tests and return a formatted report string"
  [] :String
  (run-tests "" run-tests-pass-default run-tests-fail-default))
