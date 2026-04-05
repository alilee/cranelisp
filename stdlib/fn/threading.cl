;; fn/threading.cl — Threading macros
;;
;; The -> and ->> macros thread a value through a series of forms.
;; Moved from prelude inline macros for modularity.
;;
;; Spec: 09-macros.md §9.5

(import [prelude []])

(import [macros [SexpSym SexpList SCons SNil Sexp SList]])

(defmacro -> "Thread value through forms as first argument"
  ([x] x)
  ([x form &rest]
    (match form
      [(SexpList items)
         (match items
           [(SCons hd tl) `(-> ~(SexpList (SCons hd (SCons x tl))) ~@rest)
            SNil `(-> ~x ~@rest)])
       _ `(-> ~(SexpList (SCons form (SCons x SNil))) ~@rest)])))

(defmacro ->> "Thread value through forms as last argument"
  ([x] x)
  ([x form &rest]
    (match form
      [(SexpList items) `(->> ~(SexpList (macros/sconcat items (SCons x SNil))) ~@rest)
       _ `(->> ~(SexpList (SCons form (SCons x SNil))) ~@rest)])))
