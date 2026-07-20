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

;; ── Self-tests — SHIPPED at S112 6b (return-type dispatch works) ──
;; S112 leg (c) landed nullary return-type dispatch. The backing self-test
;; `default/test.cl` (module `default.test`) exercises each impl via the
;; annotation-selected form `(let [x :Int (default)] …)`, which dispatches to
;; the per-type impl and compiles + runs end-to-end.
;;
;; D2 RESOLVED (S113). The user ruled that importing a trait METHOD without its
;; TRAIT suffices for dispatch (spec §7.11.2); the typecheck fix landed in
;; S113 W2a. So `(import [default [default]])` (method-only — no `Default`
;; trait in scope) now dispatches correctly, where at S112 6a it leaked
;; `codegen error … undefined function: default`. The S112 "RESIDUAL COMPILER
;; DEFECT" claim is SUPERSEDED. Verified end-to-end for all four impls
;; (Int/Float/Bool/String) at S113 6a. The backing test now imports the method
;; ONLY (`(import [super [default]])`) so the self-test is a live regression
;; guard for the D2 dispatch path.
;;
;; NOTE (S113, adjacent open defect 0672): a nullary return-dispatch to a type
;; with NO impl still leaks `codegen error: undefined function` instead of a
;; clean typecheck reject. Our four impls cover the tested types, so the
;; self-tests never hit it; do NOT add a no-impl negative cell here until 0672
;; is fixed.

(mod- test)
