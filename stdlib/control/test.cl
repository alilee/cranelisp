;; control/test.cl — self-tests for control (module control.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`.
;;
;; REGRESSION GUARD (S115): `when`/`unless` expanded to `(if ~test ~body None)`,
;; which forces the two `if` branches to unify — so they only typechecked when
;; the body was ALREADY an `(Option a)`. `(when true 5)` failed outright. Both
;; macros are bare-exported by the prelude, so this was a user-facing break in
;; the most visible stdlib surface. The `test-when-*-non-option-body` cases
;; below are the specific guard: they pass a body that is NOT an Option.

(import [super [when unless cond case]])
(import [testing.assertions [assert-eq assert-true]])
(import [primitives [Option Some None String Int Bool]])

;; `(Option a)` has no Eq/Display impl, so unwrap before asserting.
(defn- unwrap-int "Unwrap (Option Int), defaulting to the given sentinel" [o :Int dflt] :Int
  (match o [(Some x) x _ dflt]))

(defn- unwrap-str "Unwrap (Option String), defaulting to the given sentinel" [o :String dflt] :String
  (match o [(Some x) x _ dflt]))

(defn- none? "True when the Option is None" [o] :Bool
  (match o [(Some _) false _ true]))

;; ── when ───────────────────────────────────────────────────────────────

(defn test-when-true [] :(Option String)
  (assert-eq 5 (unwrap-int (when true 5) 0)))

(defn test-when-false [] :(Option String)
  (assert-true (none? (when false 5))))

;; The exact shape the pre-S115 expansion could not typecheck: a non-Option body.
(defn test-when-non-option-body [] :(Option String)
  (assert-eq "hi" (unwrap-str (when true "hi") "")))

(defn test-when-bool-body [] :(Option String)
  (assert-true (match (when true true) [(Some x) x _ false])))

;; ── unless ─────────────────────────────────────────────────────────────

(defn test-unless-false [] :(Option String)
  (assert-eq 7 (unwrap-int (unless false 7) 0)))

(defn test-unless-true [] :(Option String)
  (assert-true (none? (unless true 7))))

(defn test-unless-non-option-body [] :(Option String)
  (assert-eq "ho" (unwrap-str (unless false "ho") "")))

;; ── cond ───────────────────────────────────────────────────────────────

(defn test-cond-first-arm [] :(Option String)
  (assert-eq 1 (cond true 1 false 2 99)))

(defn test-cond-later-arm [] :(Option String)
  (assert-eq 2 (cond false 1 true 2 99)))

(defn test-cond-default [] :(Option String)
  (assert-eq 99 (cond false 1 false 2 99)))

;; ── case ───────────────────────────────────────────────────────────────

(defn test-case-match [] :(Option String)
  (assert-eq "two" (case 2 1 "one" 2 "two" "other")))

(defn test-case-default [] :(Option String)
  (assert-eq "other" (case 7 1 "one" 2 "two" "other")))

(defn test-case-evaluates-scrutinee-once [] :(Option String)
  ;; the scrutinee is an expression, not an atom
  (assert-eq "three" (case (+ 1 2) 1 "one" 3 "three" "other")))
