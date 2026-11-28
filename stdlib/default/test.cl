;; default/test.cl — self-tests for `default` (module default.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`. Each impl is exercised through the annotation-selected form
;; `(let [x :Int (default)] …)`, which dispatches by return type.
;;
;; REGRESSION GUARD: this module imports the `default` METHOD ONLY, without the
;; `Default` trait, because a method import suffices for dispatch (spec
;; §7.11.2). Do NOT add `Default` to the `super` import; that would defeat the
;; guard.
;;
;; A return-type dispatch to a type with no impl is a compile-time error, so
;; it cannot be a `test-*` case here; its reject cell lives in `tests/`.
;;
;; HARNESS-FREE: tests return `(Option String)` directly (None = pass) via
;; inline `if`, avoiding `testing.assertions` (whose `assert-eq` carries an
;; `Eq` bound). `=` is imported from `compare.eq` for value assertions;
;; `compare.eq` does not depend on `default`, so there is no load cycle.

(import [super [default]])
(import [compare.eq [=]])
(import [primitives [Int Float Bool String Option Some None]])

(defn test-default-int [] :(Option String)
  (let [x :Int (default)]
    (if (= x 0) None (Some "expected (default):Int = 0"))))

(defn test-default-float [] :(Option String)
  (let [x :Float (default)]
    (if (= x 0.0) None (Some "expected (default):Float = 0.0"))))

(defn test-default-bool [] :(Option String)
  (let [x :Bool (default)]
    (if x (Some "expected (default):Bool = false") None)))

(defn test-default-string [] :(Option String)
  (let [x :String (default)]
    (if (= x "") None (Some "expected (default):String = \"\""))))

(defn test-default-option-is-none [] :(Option String)
  (let [x :(Option Int) (default)]
    (match x
      [None None
       (Some _) (Some "expected (default):(Option Int) = None")])))
