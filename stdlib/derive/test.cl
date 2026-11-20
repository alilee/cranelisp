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
;; The `derive` dispatch form, by contrast, emits the `deftype` itself
;; (`Suit` below).

(import [super [derive derive-Eq derive-Ord derive-Display]])
(import [testing.assertions [assert-eq assert-true assert-false]])
(import [primitives [Option String Int Bool]])

;; ── Types under test ───────────────────────────────────────────────────
;;
;; Defined first, then derived against — see the usage contract above.

(deftype Flag Off On)                       ; 2-ctor nullary enum
(deftype Colour Red Green Blue)             ; 3-ctor nullary enum
(deftype Level (Lvl [:Int n]))              ; single 1-field data constructor
(deftype Shade Dark (Bright [:Int level]))  ; mixed: nullary + 1-field data ctor
(deftype Point (Pt [:Int x :Int y]))      ; single 2-field data constructor

(derive-Eq (deftype Flag Off On))
(derive-Ord (deftype Flag Off On))
(derive-Display (deftype Flag Off On))

(derive-Eq (deftype Colour Red Green Blue))
(derive-Ord (deftype Colour Red Green Blue))
(derive-Display (deftype Colour Red Green Blue))

(derive-Eq (deftype Level (Lvl [:Int n])))
(derive-Ord (deftype Level (Lvl [:Int n])))
(derive-Display (deftype Level (Lvl [:Int n])))

(derive-Eq (deftype Shade Dark (Bright [:Int level])))
(derive-Display (deftype Shade Dark (Bright [:Int level])))

(derive-Eq (deftype Point (Pt [:Int x :Int y])))
(derive-Ord (deftype Point (Pt [:Int x :Int y])))
(derive-Display (deftype Point (Pt [:Int x :Int y])))

;; The dispatch form defines the type and derives all three traits.
(derive [Eq Ord Display] (deftype Suit Clubs Hearts Spades))

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

;; Two fields: equal only when both are.
(defn test-eq-two-field-same [] :(Option String)
  (assert-true (= (Pt 1 2) (Pt 1 2))))

(defn test-eq-two-field-first-differs [] :(Option String)
  (assert-false (= (Pt 1 2) (Pt 9 2))))

(defn test-eq-two-field-second-differs [] :(Option String)
  (assert-false (= (Pt 1 2) (Pt 1 9))))

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

;; Three constructors: declaration order Red < Green < Blue, including the
;; non-adjacent pair.
(defn test-ord-three-ctor-adjacent [] :(Option String)
  (assert-true (< Red Green)))

(defn test-ord-three-ctor-non-adjacent [] :(Option String)
  (assert-true (< Red Blue)))

(defn test-ord-three-ctor-not-lt-backwards [] :(Option String)
  (assert-false (< Blue Green)))

;; Two fields: lexicographic — the first field decides unless equal.
(defn test-ord-two-field-first-decides [] :(Option String)
  (assert-true (< (Pt 1 9) (Pt 2 0))))

(defn test-ord-two-field-first-decides-against [] :(Option String)
  (assert-false (< (Pt 2 0) (Pt 1 9))))

(defn test-ord-two-field-second-breaks-tie [] :(Option String)
  (assert-true (< (Pt 1 2) (Pt 1 3))))

(defn test-ord-two-field-equal-is-not-lt [] :(Option String)
  (assert-false (< (Pt 1 2) (Pt 1 2))))

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

(defn test-show-two-field-ctor [] :(Option String)
  (assert-eq "Pt(1 2)" (show (Pt 1 2))))

;; ── derive dispatch form ───────────────────────────────────────────────

(defn test-dispatch-defines-type-and-eq [] :(Option String)
  (assert-false (= Clubs Spades)))

(defn test-dispatch-derives-ord [] :(Option String)
  (assert-true (< Hearts Spades)))

(defn test-dispatch-derives-display [] :(Option String)
  (assert-eq "Hearts" (show Hearts)))
