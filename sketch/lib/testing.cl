;; Test assertions and check macro.
;; Import with (import [testing [*]]) in test modules.

(import [primitives [Trace]])

;; ── Assertions ─────────────────────────────────────
;; Each assertion returns (Option String):
;;   None = pass, (Some "reason") = fail

(defn assert-eq "Assert two values are equal"
  [expected actual]
  (if (= expected actual)
    None
    (Some (str-concat "expected "
      (str-concat (show expected)
        (str-concat ", got " (show actual)))))))

(defn assert-true "Assert a value is true"
  [x]
  (if x None (Some "expected true, got false")))

(defn assert-false "Assert a value is false"
  [x]
  (if x (Some "expected false, got true") None))

;; ── run-tests helpers ───────────────────────────────
;; Default fold functions for (run-tests "" run-tests-pass-default run-tests-fail-default).

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

;; ── check macro ────────────────────────────────────
;; Chains assertions: returns first Some (failure), short-circuits.
;; (check a b c) expands to:
;;   (match a [(Some f) (Some f) None (match b [(Some f) (Some f) None c])])

(defmacro check "Chain assertions, returning first failure"
  ([x] x)
  ([x & rest]
    `(match ~x
       [(Some __f__) (Some __f__)
        None (check ~@rest)])))
