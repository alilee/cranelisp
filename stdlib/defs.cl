;; defs.cl — Definition convenience macros
;;
;; Macros for defining constants and values as zero-arg functions with
;; bare-symbol expansion.
;;
;; Spec: 09-macros.md §9.5, plan-stdlib.md §3.2

(import [macros [SexpSym SexpStr SexpInt SexpFloat SexpBool SexpList SexpBracket
                 SCons SNil Sexp SList]])

(defmacro const "Define a named constant (bare symbol expansion)" [name value]
  `(defmacro ~name [] ~(quote-sexp value)))

(defmacro const- "Define a private named constant" [name value]
  `(defmacro- ~name [] ~(quote-sexp value)))

;; def and def- inline the name-mangling (append "-def" to symbol name)
;; rather than calling a separate make-def-name helper, because defn-defined
;; helpers are not available during macro compilation (Phase 3 vs Phase 4).

(defmacro def "Define a named value (zero-arg function, bare symbol)" [name value]
  (match name
    [(SexpSym s)
     (let [impl-name (SexpSym (str-concat s "-def"))]
       `(begin
         (defn ~impl-name [] ~value)
         (defmacro ~name [] (macros/SexpList (macros/SCons ~(quote-sexp impl-name) macros/SNil)))))
     _ name]))

(defmacro def- "Define a private named value" [name value]
  (match name
    [(SexpSym s)
     (let [impl-name (SexpSym (str-concat s "-def"))]
       `(begin
         (defn- ~impl-name [] ~value)
         (defmacro- ~name [] (macros/SexpList (macros/SCons ~(quote-sexp impl-name) macros/SNil)))))
     _ name]))
