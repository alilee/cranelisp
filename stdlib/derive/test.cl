;; derive/test.cl — self-tests for derive (module derive.test)
;;
;; The consumer module `plan-stdlib.md` §3.3 specifies. The derive macros
;; cannot be exercised from an inline `(mod test …)`
;; body in `derive.cl` itself: a `defmacro` is available only to the forms that
;; FOLLOW it in the same module (spec §9.3.4), so a `(derive-Eq …)` call inside
;; derive.cl's own submodule forms fails at expansion. A SEPARATE module that
;; imports the macros and derives on its OWN ADTs is the correct test home —
;; this file. It is the standing guard for the derive surface.
;;
;; USAGE CONTRACT exercised here: `derive-Eq`/`derive-Ord`/`derive-Display` take
;; a `deftype` sexp as their INTROSPECTION argument but do NOT define the type —
;; the type must already exist, so this module derives against pre-defined types.
;;
;; NOT COVERED HERE: the `derive` dispatch form, two-field constructors, and
;; `derive-Ord` on a three-constructor enum. The last two are covered by the
;; `stdlib_derive_*` cases in `tests/stdlib_conformance.rs`.

(import [super [derive-Eq derive-Ord derive-Display]])
(import [testing.assertions [assert-eq assert-true assert-false]])
(import [primitives [Option String Int Bool]])

;; ── Types under test ───────────────────────────────────────────────────
;;
;; Defined first, then derived against — see the usage contract above.

(deftype Flag Off On)                       ; 2-ctor nullary enum
(deftype Colour Red Green Blue)             ; 3-ctor nullary enum
(deftype Level (Lvl [:Int n]))              ; single 1-field data constructor
(deftype Shade Dark (Bright [:Int level]))  ; mixed: nullary + 1-field data ctor

(derive-Eq (deftype Flag Off On))
(derive-Ord (deftype Flag Off On))
(derive-Display (deftype Flag Off On))

(derive-Eq (deftype Colour Red Green Blue))
(derive-Display (deftype Colour Red Green Blue))

(derive-Eq (deftype Level (Lvl [:Int n])))
(derive-Ord (deftype Level (Lvl [:Int n])))
(derive-Display (deftype Level (Lvl [:Int n])))

(derive-Eq (deftype Shade Dark (Bright [:Int level])))
(derive-Display (deftype Shade Dark (Bright [:Int level])))

;; ── derive-Eq ──────────────────────────────────────────────────────────

(defn test-eq-enum-reflexive [] :(Option String)
  (assert-true (= Off Off)))

(defn test-eq-enum-distinct [] :(Option String)
  (assert-false (= Off On)))

;; CONFORMANCE GUARD (S115): `Eq` declares BOTH `=` and `!=`; `derive-Eq`
;; emitted only `=`, so every use failed with "missing required method !=".
;; This case does not merely check `!=`'s value — the module would not COMPILE
;; without the emitted method.
(defn test-eq-derives-neq [] :(Option String)
  (assert-true (!= Off On)))

(defn test-eq-neq-false-when-equal [] :(Option String)
  (assert-false (!= On On)))

(defn test-eq-three-ctor-enum [] :(Option String)
  (assert-true (if (= Red Red) (if (= Green Blue) false true) false)))

(defn test-eq-data-ctor-same [] :(Option String)
  (assert-true (= (Lvl 1) (Lvl 1))))

(defn test-eq-data-ctor-differs [] :(Option String)
  (assert-false (= (Lvl 1) (Lvl 9))))

(defn test-eq-data-ctor-neq [] :(Option String)
  (assert-true (!= (Lvl 1) (Lvl 9))))

(defn test-eq-mixed-nullary-vs-data [] :(Option String)
  (assert-false (= Dark (Bright 3))))

(defn test-eq-mixed-data-same [] :(Option String)
  (assert-true (= (Bright 3) (Bright 3))))

;; ── derive-Ord ─────────────────────────────────────────────────────────
;; Constructor declaration order IS the order: Off < On.

(defn test-ord-enum-lt [] :(Option String)
  (assert-true (< Off On)))

(defn test-ord-enum-lt-is-strict [] :(Option String)
  (assert-false (< Off Off)))

(defn test-ord-enum-not-lt-backwards [] :(Option String)
  (assert-false (< On Off)))

(defn test-ord-enum-gt [] :(Option String)
  (assert-true (> On Off)))

;; CONFORMANCE GUARD (S115): `Ord` declares `<`, `>`, `<=` AND `>=`;
;; `derive-Ord` emitted only `<` and `>`, so every use failed with "missing
;; required method <=". As with `!=` above, the module would not COMPILE
;; without the emitted methods.
(defn test-ord-enum-le-when-equal [] :(Option String)
  (assert-true (<= Off Off)))

(defn test-ord-enum-le-when-less [] :(Option String)
  (assert-true (<= Off On)))

(defn test-ord-enum-le-false-when-greater [] :(Option String)
  (assert-false (<= On Off)))

(defn test-ord-enum-ge-when-equal [] :(Option String)
  (assert-true (>= On On)))

(defn test-ord-enum-ge-false-when-less [] :(Option String)
  (assert-false (>= Off On)))

;; Field order on a single-field data constructor.
(defn test-ord-data-field-decides [] :(Option String)
  (assert-true (< (Lvl 1) (Lvl 2))))

(defn test-ord-data-equal-is-not-lt [] :(Option String)
  (assert-false (< (Lvl 2) (Lvl 2))))

(defn test-ord-data-le-when-equal [] :(Option String)
  (assert-true (<= (Lvl 2) (Lvl 2))))

(defn test-ord-data-ge-when-greater [] :(Option String)
  (assert-true (>= (Lvl 9) (Lvl 1))))

;; ── derive-Display ─────────────────────────────────────────────────────

(defn test-show-nullary-ctor [] :(Option String)
  (assert-eq "Off" (show Off)))

(defn test-show-three-ctor-enum [] :(Option String)
  (assert-eq "Blue" (show Blue)))

(defn test-show-data-ctor-wraps-field [] :(Option String)
  (assert-eq "Lvl(1)" (show (Lvl 1))))

(defn test-show-mixed-nullary-arm [] :(Option String)
  (assert-eq "Dark" (show Dark)))

(defn test-show-mixed-data-arm [] :(Option String)
  (assert-eq "Bright(3)" (show (Bright 3))))
