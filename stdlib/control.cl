;; control.cl — Control flow macros
;;
;; Conditional and branching macros that don't fit in core special forms.
;;
;; Spec: 09-macros.md §9.5, plan-stdlib.md §3.2

(import [prelude []])

(import [macros [SexpSym SexpStr SexpInt SexpFloat SexpBool SexpList SexpBracket
                 SCons SNil Sexp SList]])

(defmacro when "Conditional with implicit None else branch" [test body]
  `(if ~test ~body None))

(defmacro unless "Conditional with implicit None if-true branch" [test body]
  `(if ~test None ~body))

(defmacro cond "Multi-way conditional with mandatory default"
  ([x] x)
  ([x body &rest] `(if ~x ~body (cond ~@rest))))

(defmacro case "Dispatch on value equality with mandatory default"
  ([expr x] `(let [__case__ ~expr] ~x))
  ([expr x body &rest]
    `(let [__case__ ~expr] (if (= __case__ ~x) ~body (case __case__ ~@rest)))))
