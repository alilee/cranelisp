;; core/syntax.cl — SList helper functions for macro authors
;;
;; These functions operate on (SList Sexp) values from the synthetic `macros`
;; module. `sconcat` is a runtime extern in the `macros` module (not here).
;; Helpers are available via explicit (import [core.syntax [...]]).

(import [prelude []])

(import [primitives [str-concat]])
(import [macros [*]])

;; -- SList Helpers ----------------------------------------------------------

(defn sempty? "Test if an SList is empty" [xs]
  (match xs
    [SNil true
     _ false]))

(defn sfold "Left fold over an SList" [f init xs]
  (match xs
    [SNil init
     (SCons h t) (sfold f (f init h) t)]))

(defn sreverse "Reverse an SList" [xs]
  (sfold (fn [acc x] (SCons x acc)) SNil xs))

;; sconcat is a runtime extern in the `macros` module (not defined here).
;; Quasiquote-generated code for ~@ emits `macros/sconcat` calls directly.

;; -- Macro-Authoring Helper -------------------------------------------------

(defn make-def-name "Mangle symbol name for def implementation" [name-sexp]
  (match name-sexp
    [(SexpSym s) (SexpSym (str-concat s "-def"))
     _ name-sexp]))

;; -- slist Macro ------------------------------------------------------------

(defmacro slist "Construct an SList from elements"
  ([] `macros/SNil)
  ([x &rest] `(macros/SCons ~x (slist ~@rest))))
