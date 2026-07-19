;; default.cl — Default trait
;;
;; The Default trait provides a "zero value" for types. Types with a
;; natural empty/identity value implement this trait.
;;
;; Spec: plan-stdlib.md §3.3

(import [prelude []])

(import [primitives [Int Float Bool String]])
(import [fn.option [Option None]])

(deftrait Default
  (default [] self))

(impl Default Int
  (defn default [] 0))

(impl Default Float
  (defn default [] 0.0))

(impl Default Bool
  (defn default [] false))

(impl Default String
  (defn default [] ""))

;; ── Self-tests — SHIPPED at S112 6b (return-type dispatch now works) ──
;; S112 leg (c) landed nullary return-type dispatch. The backing self-test
;; `default/test.cl` (module `default.test`) exercises each impl via the
;; annotation-selected form `(let [x :Int (default)] …)`, which dispatches to
;; the per-type impl and compiles + runs end-to-end — PROVIDED the `Default`
;; TRAIT is in scope, i.e. imported alongside the method
;; (`(import [super [Default default]])` in the backing module). The S87
;; "language limitation" / "poisons the prelude load graph" claim is
;; SUPERSEDED; the S87 deferral is retired.
;;
;; RESIDUAL COMPILER DEFECT (found S112 6a, /stdlib) — D2: a nullary
;; return-type-dispatch method imported WITHOUT its trait —
;; `(import [default [default]])` only — passes typecheck then leaks
;; `codegen error … undefined function: default`, whereas the analogous UNARY
;; method is caught cleanly at typecheck ("no impl of trait … for type …").
;; A check-gate leak (dispatch-uniformity), NOT a stdlib bug — the backing
;; test module sidesteps it by importing the trait (the green fence above).
;; Pinned as a failing test (S112 /testing batch); open user normative
;; question on whether method-only import suffices for dispatch.

(mod- test)
