;; compare/eq.cl — Eq trait and primitive impls
;;
;; The Eq trait defines equality comparison. All types that support equality
;; testing implement this trait.
;;
;; Spec: 07-traits.md §7.1

(import [prelude []])
(import [primitives [*]])

(deftrait Eq
  (= [a b] Bool)
  (!= [a b] Bool))

(impl Eq Int
  (defn = [a b] (eq-i64 a b))
  (defn != [a b] (not (eq-i64 a b))))

(impl Eq Float
  (defn = [a b] (eq-f64 a b))
  (defn != [a b] (not (eq-f64 a b))))

(impl Eq Bool
  (defn = [a b] (eq-bool a b))
  (defn != [a b] (not (eq-bool a b))))

(impl Eq String
  (defn = [a b] (str-eq a b))
  (defn != [a b] (not (str-eq a b))))

;; ── Self-tests ───────────────────────────────────────────────────────
;; INTENDED: a `(mod test …)` submodule with zero-arg `(Fn [] (Option
;; String))` `test-*` fns asserting `(= 1 1)` etc. via testing.assertions.
;;
;; BLOCKED this sprint by compiler defects in the submodule-test path
;; (S86 Phase 6b — routed to /qa for narrow repro → /typecheck/backend):
;;   * A `(mod test …)` inside a TRAIT-DEFINING module that imports
;;     `testing.assertions` creates a circular re-definition — the import
;;     chain compare.eq → compare.eq.test → testing.assertions → compare.eq
;;     re-enters the parent and errors "trait Eq already defined".
;;   * A test submodule importing the parent trait (`Eq`/`=`) resolves it
;;     in the WRONG module scope ("unknown trait Eq (from module user)").
;;   * String `!=` monomorphises to an unresolved `neq-string` symbol
;;     (JIT "can't resolve symbol neq-string") — a PRE-EXISTING codegen
;;     defect, reproducible with plain `(!= "a" "b")` on pristine HEAD.
;; See plan-stdlib.md §"S86 self-test rollout — blocked" for the full list.
