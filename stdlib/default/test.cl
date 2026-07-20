;; default/test.cl — self-tests for `default` (module default.test)
;;
;; Authored as a SEPARATE backing file (not an inline `(mod test …)` body) so
;; the compiler's one-time inline-submodule EXTRACTION (spec §8.2.5) cannot
;; strip it: an inline body is extracted to this path on first compile and the
;; parent left with a bare `(mod- test)`; authoring the file directly is the
;; durable, extraction-stable form. The parent declares `(mod- test)`.
;;
;; Un-defers the stale S87 "Default self-test is a language limitation"
;; deferral: nullary return-type dispatch (S112 leg (c)) makes the
;; annotation-selected form `(let [x :Int (default)] …)` dispatch to the Int
;; impl and compile + run end-to-end.
;;
;; D2 REGRESSION GUARD: this module imports the `default` METHOD ONLY — WITHOUT
;; the `Default` trait — via `super`. At S112 6a that leaked
;; `undefined function: default` at codegen; the S113 D2 ruling (method-import
;; suffices for dispatch, spec §7.11.2) + typecheck fix make it dispatch
;; correctly, so this method-only import is now the durable guard for that
;; path. Do NOT re-add `Default` to this import — it would defeat the guard.
;;
;; (0672, adjacent open defect: a nullary return-dispatch to a type with NO
;; impl still leaks `undefined function` instead of a clean reject. The four
;; impls cover Int/Float/Bool/String, so these tests never hit it; do NOT add a
;; no-impl negative cell until 0672 is fixed.)
;;
;; HARNESS-FREE: tests return `(Option String)` directly (None = pass) via
;; inline `if`, avoiding `testing.assertions` (whose `assert-eq` carries an
;; `Eq` bound). `=` is imported from `compare.eq` for value assertions;
;; `compare.eq` does not depend on `default`, so there is no load cycle.

(import [super [default]])
(import [compare.eq [=]])
(import [primitives [Int Float Bool String Option Some None]])

(defn test-default-int [] :(Option String)
  (let [x :Int (default)]
    (if (= x 0) None (Some "expected (default):Int = 0"))))

(defn test-default-float [] :(Option String)
  (let [x :Float (default)]
    (if (= x 0.0) None (Some "expected (default):Float = 0.0"))))

(defn test-default-bool [] :(Option String)
  (let [x :Bool (default)]
    (if x (Some "expected (default):Bool = false") None)))

(defn test-default-string [] :(Option String)
  (let [x :String (default)]
    (if (= x "") None (Some "expected (default):String = \"\""))))
