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

;; ── The seeded data types ─────────────────────────────────────────────
;; `Option`, `Result` and `Pair` are seeded by `primitives`, so their impls
;; live with the trait: wherever `Eq` is reachable, so are these. Two values
;; are equal when they have the same constructor and equal payloads.

(impl Eq (Option :Eq a)
  (defn = [x y]
    (match x
      [None (match y [None true _ false])
       (Some u) (match y [(Some v) (= u v) _ false])]))
  (defn != [x y] (if (= x y) false true)))

(impl Eq (Result :Eq a :Eq e)
  (defn = [x y]
    (match x
      [(Ok u) (match y [(Ok v) (= u v) _ false])
       (Err u) (match y [(Err v) (= u v) _ false])]))
  (defn != [x y] (if (= x y) false true)))

(impl Eq (Pair :Eq a :Eq b)
  (defn = [x y]
    (match x
      [(Pair x1 x2) (match y [(Pair y1 y2) (if (= x1 y1) (= x2 y2) false)])]))
  (defn != [x y] (if (= x y) false true)))

;; ── Self-tests ───────────────────────────────────────────────────────
;; Backing file `compare/eq/test.cl` (module `compare.eq.test`) imports the
;; trait and its methods via `super`.
;;
;; HARNESS-FREE by necessity: `testing.assertions` itself depends on
;; `compare.eq` (its `assert-eq` carries an `Eq` bound), so a self-test that
;; imported `testing.assertions` would form a load cycle
;; (compare.eq → compare.eq.test → testing.assertions → compare.eq). The
;; tests therefore return `(Option String)` directly via inline `if`, exactly
;; the shape the harness produces — None = pass, (Some why) = fail.

(mod- test)
