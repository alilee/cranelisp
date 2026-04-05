;; fn/threading.cl — Threading macros
;;
;; The -> and ->> macros thread a value through a series of forms.
;; Moved from prelude inline macros for modularity.
;;
;; Spec: 09-macros.md §9.5

(import [prelude []])

;; Macro bodies use qualified macros/ names so expansion results are
;; independent of the call-site's imports (spec §9.1.3).
(defmacro -> "Thread value through forms as first argument"
  ([x] x)
  ([x form &rest]
    (match form
      [(macros/SexpList items)
         (match items
           [(macros/SCons hd tl) `(-> ~(macros/SexpList (macros/SCons hd (macros/SCons x tl))) ~@rest)
            macros/SNil `(-> ~x ~@rest)])
       _ `(-> ~(macros/SexpList (macros/SCons form (macros/SCons x macros/SNil))) ~@rest)])))

(defmacro ->> "Thread value through forms as last argument"
  ([x] x)
  ([x form &rest]
    (match form
      [(macros/SexpList items) `(->> ~(macros/SexpList (macros/sconcat items (macros/SCons x macros/SNil))) ~@rest)
       _ `(->> ~(macros/SexpList (macros/SCons form (macros/SCons x macros/SNil))) ~@rest)])))
