;; 38-program-tests.cl -- Tests the compiler discovers and runs
;;
;; Every earlier example checks itself through `main`: each check returns a
;; number and `main` adds the numbers into the exit code. The language has a
;; direct form for this. A TEST FUNCTION is a zero-argument function whose
;; name begins with `test-` and whose type is exactly (Fn [] (Option String)):
;;
;;   None           -- the test passed
;;   (Some reason)  -- the test failed, and `reason` says why
;;
;; `--test` compiles the program, finds its test functions, runs every one
;; and reports each result. It never calls `main`. It exits 0 when no test
;; fails, and 1 when any test fails or panics.
;;
;; Running:
;;   ./target/debug/cranelisp --test examples/38-program-tests.cl
;;   ./target/debug/cranelisp --run examples/38-program-tests.cl
;;
;; The --test report lists each test by its qualified name, then a summary
;; (the time varies):
;;
;;   38-program-tests/test-addition .......... ok
;;   38-program-tests/test-concat ............ ok
;;   38-program-tests/test-division-truncates  ok
;;   38-program-tests/test-sign .............. ok
;;
;;   4 passed in 0.03ms
;;
;; A failing test prints its reason in place of `ok`. If `test-concat`
;; expected "hello, word" instead, its line would end
;; `FAILED: str-concat should join both strings`, the summary would read
;; `3 passed, 1 failed`, and the run would exit 1.
;;
;; WHAT IS NOT A TEST. A `test-` function of any other type is not run.
;; `--test` warns instead, so a mistyped test cannot pass silently. A
;; `(defn test-sum [] 3)` would be reported as:
;;
;;   warning: `38-program-tests/test-sum` is not run as a test: its type is
;;   `(Fn [] Int)`, and a test must have type `(Fn [] (Option String))`
;;
;; That is why the checks in examples 02-37 are named `check-`, not `test-`.
;;
;; Only the program's own modules are searched. Library modules, such as
;; examples/lib/operators.cl, contribute no tests.
;;
;; Expected exit code under --run: 4, one per passing test.

;; Option's constructors come from the `primitives` module.
(import [primitives [None Some]])

;; An ordinary helper. It does not start with `test-`, so it is not a test.
(defn expect-int [actual expected reason]
  (if (eq-i64 actual expected) None (Some reason)))

;; --- The tests ---

(defn test-addition []
  (expect-int (add-i64 2 3) 5 "2 + 3 should be 5"))

(defn test-division-truncates []
  (expect-int (div-i64 17 5) 3 "integer division should truncate"))

(defn test-concat []
  (if (str-eq (str-concat "hello, " "world") "hello, world")
    None
    (Some "str-concat should join both strings")))

(defn sign [n]
  (if (lt-i64 n 0) -1 (if (eq-i64 n 0) 0 1)))

(defn test-sign []
  (match (expect-int (sign -7) -1 "sign of a negative should be -1")
    [None (expect-int (sign 0) 0 "sign of zero should be 0")
     (Some reason) (Some reason)]))

;; --- main, for --run ---

;; `--test` ignores `main`. Under `--run`, `main` calls the same test
;; functions and counts the ones that pass.
(defn passed [result]
  (match result
    [None 1
     (Some _) 0]))

(defn main []
  (Pure
    (add-i64 (passed (test-addition))
      (add-i64 (passed (test-division-truncates))
        (add-i64 (passed (test-concat))
                 (passed (test-sign)))))))
