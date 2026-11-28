;; io/monad/test.cl — self-tests for io.monad (module io.monad.test)
;;
;; A discovered test has type `(Fn [] (Option String))`, so it cannot run an IO
;; action and observe the result. Only the forms that expand without `bind` are
;; tested here: `do` over one form, and `bind!` with no bindings.
;;
;; Withheld, because each case's result is an IO action:
;;   - `do` over several actions
;;   - `bind!` with one binding
;;   - `bind!` with two bindings, the second referring to the first
;; `tests/spec_11_stdlib.rs` runs these through the REPL.

(import [super [do bind!]])
(import [testing.assertions [assert-eq]])
(import [primitives [Option String]])

(defn test-do-single-form-is-the-form [] :(Option String)
  (assert-eq 42 (do 42)))

(defn test-do-single-form-keeps-its-type [] :(Option String)
  (assert-eq "x" (do "x")))

(defn test-bind!-no-bindings-is-the-body [] :(Option String)
  (assert-eq 7 (bind! [] 7)))
