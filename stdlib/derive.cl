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

(defmacro derive-Eq "Derive Eq trait implementation" [dt]
  `(impl Eq ~(build-impl-target (dt-name dt) (dt-params dt) "Eq" dt)
     (defn = [a b] (match a ~(SexpBracket (build-eq-arms (dt-constructors dt)))))))

;; ── derive-Ord macro ───────────────────────────────────

(defmacro derive-Ord "Derive Ord trait implementation" [dt]
  `(impl Ord ~(build-impl-target (dt-name dt) (dt-params dt) "Ord" dt)
     (defn < [a b] (match a ~(SexpBracket (build-ord-lt-arms (dt-constructors dt)))))
     (defn > [a b] (< b a))))

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
;; The derive macros cannot be exercised from an in-module `(mod test)`: a
;; `defmacro` is available only to the forms that FOLLOW it in the same module
;; (§9.3.4 defmacro-before-use), and a `(derive …)` call needs its own type
;; (`(deftype …)`) plus an `(impl …)` expansion that references the derived
;; methods — all of which belong to a DOWNSTREAM module that imports these
;; macros and derives on its own ADT. That downstream module is the correct
;; test home (spec §9.3.4). Recorded in plan-stdlib.md §26.4.
;;
;; (The §9.3.4 expansion-time-helper requirement is satisfied by the sibling
;; `derive.helpers` dependency module — see the header. The derive macros'
;; expansions reference only those dependency-module functions plus the
;; synthetic `macros` module, never a same-module non-macro definition.)
