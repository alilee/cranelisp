;; testing/assertions.cl — Test assertion functions
;;
;; Each assertion returns (Option String): None on success, (Some reason) on
;; failure. `check` chains assertions.
;;
;; This module does not reference `discover-tests`, so batch programs
;; (`--run`, `--link`, `--test`) can import it; `testing.runner` cannot be.
;;
;; Spec: plan-stdlib.md §3.3

(import [prelude []])

(import [primitives [Bool String str-concat]])
(import [compare.eq [Eq = !=]])
(import [text.display [Display show]])
(import [fn.option [Option Some None]])

(defn assert-eq "Assert two values are equal"
  [:Eq :Display a :Eq :Display b] :(Option String)
  (if (= a b)
    None
    (Some (str-concat (str-concat (str-concat "expected " (show a)) " but got ") (show b)))))

(defn assert-true "Assert a boolean is true"
  [:Bool x] :(Option String)
  (if x None (Some "expected true but got false")))

(defn assert-false "Assert a boolean is false"
  [:Bool x] :(Option String)
  (if x (Some "expected false but got true") None))

;; Returns the first failure and does not evaluate the assertions after it;
;; when every assertion passes it returns the last one's value (None).
;; The expansion names `Some`, `None` and `check` unqualified, so the caller
;; must have all three in scope (spec §9.3.4).
(defmacro check "Chain assertions, returning the first failure"
  ([x] x)
  ([x & rest]
    `(match ~x
       [(Some __f__) (Some __f__)
        None (check ~@rest)])))

;; ── Self-tests ───────────────────────────────────────────────────────
;; Backing file `testing/assertions/test.cl` (module `testing.assertions.test`).

(mod- test)
