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
;; `(mod- test …)` submodule (S87 Stage C.2): imports the parent trait + its
;; methods via `super` (D4 path — the trait is seeded into the child's
;; constraint scope). The S86 trait-bedrock blockers (D3 child re-defines
;; parent trait; D4 super-trait not in child scope; the `neq-string` String
;; `!=` codegen) are all FIXED — this is a real, runnable `(mod- test)`.
;;
;; HARNESS-FREE by necessity: `testing.assertions` itself depends on
;; `compare.eq` (its `assert-eq` carries an `Eq` bound), so a self-test that
;; imported `testing.assertions` would form a load cycle
;; (compare.eq → compare.eq.test → testing.assertions → compare.eq). The
;; tests therefore return `(Option String)` directly via inline `if`, exactly
;; the shape the harness produces — None = pass, (Some why) = fail.

(mod- test)
