;; testing/assertions.cl — Test assertion functions
;;
;; Each assertion returns (Option String): None on success, (Some reason) on
;; failure. Written using only functions and primitives (no macros), so it
;; lights up at Ring 2.
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

;; ── Self-tests ───────────────────────────────────────────────────────
;; Backing file `testing/assertions/test.cl` (module `testing.assertions.test`).

(mod- test)
