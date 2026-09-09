;; core/syntax.cl — SList helper functions for macro authors
;;
;; These functions operate on (SList Sexp) values from the synthetic `macros`
;; module. `sconcat` is a runtime extern in the `macros` module (not here).
;; Helpers are available via explicit (import [core.syntax [...]]).

(import [prelude []])

(import [primitives [str-concat Some None]])
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

;; Reader annotations arrive at macros as one structural SexpAnnotated node.
;; Keep these helpers module-qualified: they are macro-authoring tools, not
;; general prelude syntax.
(defn annotated? "True when an Sexp carries a reader annotation" [form]
  (match form
    [(SexpAnnotated _ _) true
     _ false]))

(defn annotation "Return an Sexp's reader annotation, when present" [form]
  (match form
    [(SexpAnnotated ann _) (Some ann)
     _ None]))

(defn unannotate "Return an annotated Sexp's subject, or an ordinary Sexp unchanged" [form]
  (match form
    [(SexpAnnotated _ subject) subject
     _ form]))

;; -- slist Macro ------------------------------------------------------------

(defmacro slist "Construct an SList from elements"
  ([] `macros/SNil)
  ([x &rest] `(macros/SCons ~x (slist ~@rest))))

;; ── Self-tests ───────────────────────────────────────────────────────
;; Backing file `core/syntax/test.cl` (module `core.syntax.test`).

(mod- test)
