(import [primitives [*]])

;; ── Trait Declarations ──────────────────────────────

(deftrait Num "Numeric arithmetic operations"
  (+ "Add two values" [self self] self)
  (- "Subtract two values" [self self] self)
  (* "Multiply two values" [self self] self)
  (/ "Divide two values" [self self] self))

(deftrait Eq "Equality comparison"
  (= "Test equality" [self self] Bool))

(deftrait Ord "Ordering comparisons"
  (< "Test less-than" [self self] Bool)
  (> "Test greater-than" [self self] Bool)
  (<= "Test less-than-or-equal" [self self] Bool)
  (>= "Test greater-than-or-equal" [self self] Bool))

;; ── Int ─────────────────────────────────────────────

(impl Num Int
  (defn + [x y] (add-i64 x y))
  (defn - [x y] (sub-i64 x y))
  (defn * [x y] (mul-i64 x y))
  (defn / [x y] (div-i64 x y)))

(impl Eq Int
  (defn = [x y] (eq-i64 x y)))

(impl Ord Int
  (defn < [x y] (lt-i64 x y))
  (defn > [x y] (gt-i64 x y))
  (defn <= [x y] (le-i64 x y))
  (defn >= [x y] (ge-i64 x y)))

(defn inc "Increment by one" [:Int x] (+ x 1))

;; ── Float ───────────────────────────────────────────

(impl Num Float
  (defn + [x y] (add-f64 x y))
  (defn - [x y] (sub-f64 x y))
  (defn * [x y] (mul-f64 x y))
  (defn / [x y] (div-f64 x y)))

(impl Eq Float
  (defn = [x y] (eq-f64 x y)))

(impl Ord Float
  (defn < [x y] (lt-f64 x y))
  (defn > [x y] (gt-f64 x y))
  (defn <= [x y] (le-f64 x y))
  (defn >= [x y] (ge-f64 x y)))
