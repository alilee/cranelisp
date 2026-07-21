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
;; 0672 RETIRED (verified S115 6b). The deferral above read: "a nullary
;; return-dispatch to a type with NO impl still leaks `undefined function`
;; instead of a clean reject … do NOT add a no-impl negative cell until 0672 is
;; fixed." This sprint's 0709 work fixed it — the no-impl case now rejects
;; cleanly at typecheck:
;;
;;   (deftype Widget W)
;;   (let [x :Widget (default)] x)
;;   ⇒ error: no impl of trait default/Default for type user/Widget
;;
;; Neither owed cell can live in THIS module, for two independent structural
;; reasons — both worth stating so nobody re-opens the question:
;;
;;   1. The no-impl reject is a COMPILE-TIME error. A `test-*` function that
;;      must fail to compile would take the whole module with it. Its guard is
;;      a reject test in `tests/`, `/testing`'s cell, asserting the message
;;      above.
;;   2. The positive companion — dispatching `(default)` by return type to a
;;      USER-DEFINED type, the same non-primitive path the no-impl case travels
;;      — needs an `(impl Default …)`, and `impl` requires the trait in scope
;;      by BARE name: `(impl default/Default Slot …)` is rejected with
;;      "unknown trait: default/Default". Importing `Default` here is exactly
;;      what the D2 guard above forbids. The two are mutually exclusive in one
;;      module; the user-type cell therefore belongs in a consumer module or in
;;      `tests/`, not here. (The qualified-trait-name gap is FIXME 0836.)
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
