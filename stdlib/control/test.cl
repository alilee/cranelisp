;; control/test.cl — self-tests for control (module control.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`.
;;
;; REGRESSION GUARD: an expansion `(if ~test ~body None)` forces the two `if`
;; branches to unify, so `when`/`unless` would typecheck only when the body is
;; already an `(Option a)`. The `test-*-non-option-body` cases pass a body that
;; is NOT an Option.

(import [super [when unless cond case]])
(import [testing.assertions [assert-eq assert-true]])
(import [primitives [Option Some None String Int Bool]])

;; Unwrap to a scalar before asserting.
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

;; A non-Option body, which an unwrapped expansion cannot typecheck.
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
