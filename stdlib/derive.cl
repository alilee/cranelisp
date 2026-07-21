;; derive.cl — Derive macro for automatic trait implementations
;;
;; Generates Eq, Ord, and Display trait implementations from deftype forms.
;; Usage: (derive [Eq Ord Display] (deftype Color Red Green Blue))
;;
;; Individual macros: derive-Eq, derive-Ord, derive-Display
;;
;; The expansion-time helpers (SList utilities, deftype introspection, and the
;; template builders) live in the dependency submodule `derive.helpers`
;; (`derive/helpers.cl`). Per spec §9.3.4 a macro's expansion MUST NOT reference
;; a same-module non-macro definition — helpers a macro needs at expansion time
;; MUST live in a dependency module. `(mod helpers)` declares that dependency and
;; the import below binds the seven functions the macro bodies call directly.
;;
;; Uses primitives directly (no prelude dependency) since this module is compiled
;; outside the prelude graph.
;;
;; Spec: 07-traits.md §7.4, 09-macros.md §9.3.4, plan-stdlib.md §3.3

(import [prelude []])
(import [primitives [str-concat]])

(import [macros [*]])
(import [core.syntax [sfold sreverse]])

(mod helpers)
(import [derive.helpers
         [dt-name dt-params dt-constructors
          build-impl-target build-eq-arms build-ord-lt-arms build-show-arms]])

;; ── derive-Eq macro ────────────────────────────────────

;; CONFORMANCE (S115): a derived impl must supply EVERY method the trait
;; declares, or the `impl` is rejected ("impl Eq for T: missing required method
;; !="). `Eq` declares `=` and `!=`; `Ord` declares `<`, `>`, `<=`, `>=`. The
;; pre-S115 macros emitted only `=` (Eq) and `<`/`>` (Ord), so EVERY use of
;; `derive-Eq`/`derive-Ord` failed conformance. The derived companions are
;; expressed with `if`, not `not`, because the expansion lands in the CONSUMER's
;; module, where the raw primitive `not` is not in scope (the S86 prelude
;; de-leak). Guarded by `derive/test.cl`.

(defmacro derive-Eq "Derive Eq trait implementation" [dt]
  `(impl Eq ~(build-impl-target (dt-name dt) (dt-params dt) "Eq" dt)
     (defn = [a b] (match a ~(SexpBracket (build-eq-arms (dt-constructors dt)))))
     (defn != [a b] (if (= a b) false true))))

;; ── derive-Ord macro ───────────────────────────────────
;;
;; Only `<` is derived structurally; the other three comparisons are expressed
;; in terms of it, so they cannot disagree with it (`>` = b<a, `<=` = ¬(b<a),
;; `>=` = ¬(a<b)). Using `<` alone — never `=` — keeps `derive-Ord` independent
;; of whether `Eq` was also derived for the type.

(defmacro derive-Ord "Derive Ord trait implementation" [dt]
  `(impl Ord ~(build-impl-target (dt-name dt) (dt-params dt) "Ord" dt)
     (defn < [a b] (match a ~(SexpBracket (build-ord-lt-arms (dt-constructors dt)))))
     (defn > [a b] (< b a))
     (defn <= [a b] (if (< b a) false true))
     (defn >= [a b] (if (< a b) false true))))

;; ── derive-Display macro ───────────────────────────────

(defmacro derive-Display "Derive Display trait implementation" [dt]
  `(impl Display ~(build-impl-target (dt-name dt) (dt-params dt) "Display" dt)
     (defn show [self] (match self ~(SexpBracket (build-show-arms (dt-constructors dt)))))))

;; ── derive dispatch macro ──────────────────────────────

(defmacro derive "Derive trait implementations for a type" [[&traits] dt]
  (let [calls (sfold
                (fn [acc trait-sexp]
                  (match trait-sexp
                    [(SexpSym name)
                     (SCons (SexpList (SCons (SexpSym (str-concat "derive-" name))
                                            (SCons dt SNil)))
                            acc)
                     _ acc]))
                SNil traits)]
    (SexpList (SCons (SexpSym "begin") (SCons dt (sreverse calls))))))

;; ── Self-tests — home is a SEPARATE consumer module ────
;; The derive macros cannot be exercised from an in-module `(mod test)` BODY: a
;; `defmacro` is available only to the forms that FOLLOW it in the same module
;; (§9.3.4 defmacro-before-use), and a `(derive …)` call needs its own type
;; (`(deftype …)`) plus an `(impl …)` expansion that references the derived
;; methods — all of which belong to a DOWNSTREAM module that imports these
;; macros and derives on its own ADT. That downstream module is the correct
;; test home (spec §9.3.4). Recorded in plan-stdlib.md §26.4.
;;
;; BUILT S115: `derive/test.cl` (module `derive.test`) is that consumer — a
;; separate module that imports these macros from `super` and derives against
;; its own four ADTs. It is the standing guard for the derive surface; the two
;; S115 conformance fixes above (`!=` for Eq, `<=`/`>=` for Ord) are pinned
;; there, and its header records the FIXME-0815 / FIXME-0816 boundaries.

(mod- test)
;;
;; (The §9.3.4 expansion-time-helper requirement is satisfied by the sibling
;; `derive.helpers` dependency module — see the header. The derive macros'
;; expansions reference only those dependency-module functions plus the
;; synthetic `macros` module, never a same-module non-macro definition.)
