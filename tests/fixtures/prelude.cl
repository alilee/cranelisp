;; Test prelude — owned by /qa, NOT a copy of stdlib/prelude.cl
;;
;; This fixture provides stable type and trait definitions for integration
;; and E2E tests. It is loaded via the same prelude auto-import mechanism
;; that stdlib uses, so tests validate that imported types display correctly.
;;
;; Changes here require QA review because test assertions depend on exact
;; type shapes and module paths.
;;
;; See tests/plan/strategy.md §"Prelude & Stdlib Test Isolation" for rationale.
;;
;; Spec §8.4: re-EXPORT (not import) so primitive fns AND types are Public and
;; flow through the user module's implicit prelude glob (§8.8). A plain import
;; is Private and the glob (§8.7.3) skips it — FIXME 0263.

(export [primitives [*]])

;; --- Core ADTs ---

(deftype (Option a) None (Some [:a val]))
(deftype (Result a b) (Ok [:a val]) (Err [:b err]))

;; --- Numeric trait + impls ---

(deftrait Num
  (+ [a b] self)
  (- [a b] self)
  (* [a b] self)
  (/ [a b] self))

(impl Num Int
  (defn + [a b] (add-i64 a b))
  (defn - [a b] (sub-i64 a b))
  (defn * [a b] (mul-i64 a b))
  (defn / [a b] (div-i64 a b)))

(impl Num Float
  (defn + [a b] (add-f64 a b))
  (defn - [a b] (sub-f64 a b))
  (defn * [a b] (mul-f64 a b))
  (defn / [a b] (div-f64 a b)))

;; --- Equality trait + impls ---

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

;; --- Ordering trait + impls ---

(deftrait Ord
  (< [a b] Bool)
  (> [a b] Bool)
  (<= [a b] Bool)
  (>= [a b] Bool))

(impl Ord Int
  (defn < [a b] (lt-i64 a b))
  (defn > [a b] (gt-i64 a b))
  (defn <= [a b] (le-i64 a b))
  (defn >= [a b] (ge-i64 a b)))

(impl Ord Float
  (defn < [a b] (lt-f64 a b))
  (defn > [a b] (gt-f64 a b))
  (defn <= [a b] (le-f64 a b))
  (defn >= [a b] (ge-f64 a b)))
