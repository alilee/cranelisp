;; fn/result.cl — Result type
;;
;; The Result type represents a computation that can succeed (Ok) or fail
;; (Err). Used for error handling without exceptions.
;;
;; `Result` is seeded by `primitives` (it is the return type of
;; `catch-runtime-error :: forall a. (Fn [(Fn [] a)] (Result a String))`).
;; To keep ONE canonical `Result` type across the system, this module
;; RE-EXPORTS the primitives `Result`/`Ok`/`Err` rather than defining a
;; second, distinct ADT — mirroring `fn.option`. The combinators below
;; operate over the SAME `primitives/Result` type.
;;
;; Spec: plan-stdlib.md §3.3, 08-modules.md §8.6.4

(import [prelude []])
(import [primitives [Result Ok Err]])
(export [primitives [Result Ok Err]])

(defn is-ok? "Test if a Result is Ok" [r]
  (match r
    [(Ok _) true
     (Err _) false]))

(defn is-err? "Test if a Result is Err" [r]
  (match r
    [(Ok _) false
     (Err _) true]))

(defn unwrap-or "Extract Ok value or return default" [default r]
  (match r
    [(Ok v) v
     (Err _) default]))

(defn map-ok "Apply function to Ok value, pass through Err" [f r]
  (match r
    [(Ok v) (Ok (f v))
     (Err e) (Err e)]))

(defn map-err "Apply function to Err value, pass through Ok" [f r]
  (match r
    [(Ok v) (Ok v)
     (Err e) (Err (f e))]))

(defn and-then "Chain a fallible computation on Ok value" [f r]
  (match r
    [(Ok v) (f v)
     (Err e) (Err e)]))

;; ── Self-tests ───────────────────────────────────────────────────────
;; `(mod- test …)` submodule (S87 Stage C.2): exercises the Result combinators
;; with the in-language harness (`testing.assertions` does NOT depend on
;; `fn.result`, so there is no load cycle).

(mod- test)
