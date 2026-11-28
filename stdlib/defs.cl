;; defs.cl — Definition convenience macros
;;
;; Macros for defining constants and values as zero-arg functions with
;; bare-symbol expansion.
;;
;; Spec: 09-macros.md §9.5, plan-stdlib.md §3.2

(import [prelude []])
(import [primitives [*]])

;; Macro bodies use qualified macros/ names so expansion results are
;; independent of the call-site's imports (spec §9.1.3).

(defmacro const "Define a named constant (bare symbol expansion)" [name value]
  `(defmacro ~name [] ~(primitives/quote-sexp value)))

(defmacro const- "Define a private named constant" [name value]
  `(defmacro- ~name [] ~(primitives/quote-sexp value)))

;; def and def- inline the name-mangling (append "-def" to symbol name)
;; rather than calling a helper: a macro body cannot call a `defn` of its own
;; module at expansion time (spec §9.2.5).
;;
;; `(k a b)` on a `def`-bound function value fails with the zero-argument
;; macro's arity error; FIXME 0800 carries that API choice (plan-stdlib.md §6.1).

(defmacro def "Define a named value (zero-arg function, bare symbol)" [name value]
  (match name
    [(macros/SexpSym s)
     (let [impl-name (macros/SexpSym (primitives/str-concat s "-def"))]
       `(begin
         (defn ~impl-name [] ~value)
         (defmacro ~name [] (macros/SexpList (macros/SCons ~(primitives/quote-sexp impl-name) macros/SNil)))))
     _ name]))

(defmacro def- "Define a private named value" [name value]
  (match name
    [(macros/SexpSym s)
     (let [impl-name (macros/SexpSym (primitives/str-concat s "-def"))]
       `(begin
         (defn- ~impl-name [] ~value)
         (defmacro- ~name [] (macros/SexpList (macros/SCons ~(primitives/quote-sexp impl-name) macros/SNil)))))
     _ name]))

;; ── Self-tests ───────────────────────────────────────────────────────
;; Backing file `defs/test.cl` (module `defs.test`).

(mod- test)
