;; prelude.cl — Standard prelude macros for Cranelisp
;;
;; Loaded implicitly for all non-prelude modules. Defines convenience macros
;; that make the language ergonomic. The macros are ordered by infrastructure
;; dependency: each macro may only use helpers/macros defined before it.
;;
;; Spec references: 09-macros.md sections 9.5, 9.6, 9.10, 9.12

(import [macros [SexpSym SexpStr SexpInt SexpFloat SexpBool SexpList SexpBracket
                 SCons SNil Sexp SList]
         core.syntax [make-def-name]])

;; ── Core types needed by prelude macros ────────────────────────────────────

(deftype (Option a) None (Some [:a val]))
(deftype (List a) Nil (Cons [:a head :(List a) tail]))

;; ── Group A: No helper dependencies ────────────────────────────────────────

(defmacro vec "Construct a vec from elements" [&elems]
  (SexpBracket elems))

(defmacro when "Conditional with implicit None else branch" [test body]
  `(if ~test ~body None))

;; ── Group B: Need quote-sexp primitive ─────────────────────────────────────

(defmacro const "Define a named constant (bare symbol expansion)" [name value]
  `(defmacro ~name [] ~(quote-sexp value)))

(defmacro const- "Define a private named constant" [name value]
  `(defmacro- ~name [] ~(quote-sexp value)))

;; ── Group C: Need sconcat (via ~@), multi-clause dispatch ──────────────────

(defmacro do "Sequence expressions, return last value"
  ([x] x)
  ([x &rest] `(let [_ ~x] (do ~@rest))))

(defmacro cond "Multi-way conditional with mandatory default"
  ([x] x)
  ([x body &rest] `(if ~x ~body (cond ~@rest))))

(defmacro list "Construct a list from elements"
  ([] `Nil)
  ([x &rest] `(Cons ~x (list ~@rest))))

(defmacro str "Concatenate string representations of all arguments"
  ([] (SexpStr ""))
  ([x] `(show ~x))
  ([x &rest] `(str-concat (show ~x) (str ~@rest))))

;; ── Group D: Need sconcat + manual Sexp construction ───────────────────────

(defmacro case "Dispatch on value equality with mandatory default"
  ([expr x] `(let [__case__ ~expr] ~x))
  ([expr x body &rest]
    `(let [__case__ ~expr] (if (= __case__ ~x) ~body (case __case__ ~@rest)))))

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

;; ── Group E: Need begin splicing + defmacro-in-results ─────────────────────

(defmacro def "Define a named value (zero-arg function, bare symbol)" [name value]
  `(begin
    (defn ~(make-def-name name) [] ~value)
    (defmacro ~name [] (macros/SexpList (macros/SCons ~(quote-sexp (make-def-name name)) macros/SNil)))))

(defmacro def- "Define a private named value" [name value]
  `(begin
    (defn- ~(make-def-name name) [] ~value)
    (defmacro- ~name [] (macros/SexpList (macros/SCons ~(quote-sexp (make-def-name name)) macros/SNil)))))

;; ── Group F: Deferred to Ring 4 (IO model needed for testing) ──────────────

(defmacro bind! "Monadic bind sugar"
  ([[] body] body)
  ([[name expr &more] body]
    `(bind ~expr (fn [~name] (bind! [~@more] ~body)))))
