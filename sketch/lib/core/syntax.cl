(import [primitives [*] macros [*]])

;; ── SList Helpers ───────────────────────────────────

(defn sfold "Fold over an SList" [f init xs]
  (match xs
    [SNil init
     (SCons h t) (sfold f (f init h) t)]))

(defn sreverse "Reverse an SList" [xs]
  (sfold (fn [acc x] (SCons x acc)) SNil xs))

(defn sconcat "Concatenate two SLists" [xs ys]
  (sfold (fn [acc x] (SCons x acc)) ys (sreverse xs)))

(defn sempty? "Test if an SList is empty" [xs]
  (match xs
    [SNil true
     _ false]))

;; ── Macro Helper ────────────────────────────────────

(defn- make-def-name "Mangle name for def implementation" [name-sexp]
  (match name-sexp
    [(SexpSym s) (SexpSym (str-concat s "-def"))
     _ name-sexp]))

;; ── Quoting & Definition Macros ─────────────────────

(defmacro const "Define a named constant (bare symbol expansion)" [name value]
  `(defmacro ~name [] ~(quote-sexp value)))

(defmacro const- "Define a private named constant" [name value]
  `(defmacro- ~name [] ~(quote-sexp value)))

(defmacro def "Define a named value (zero-arg function, bare symbol)" [name value]
  `(begin
    (defn ~(make-def-name name) [] ~value)
    (defmacro ~name [] (macros/SexpList (macros/SCons ~(quote-sexp (make-def-name name)) macros/SNil)))))

(defmacro def- "Define a private named value" [name value]
  `(begin
    (defn- ~(make-def-name name) [] ~value)
    (defmacro- ~name [] (macros/SexpList (macros/SCons ~(quote-sexp (make-def-name name)) macros/SNil)))))

;; ── Prelude Macros ──────────────────────────────────

(defmacro list "Construct a list from elements"
  ([] `Nil)
  ([x & rest] `(Cons ~x (list ~@rest))))

(defmacro slist "Construct an SList from elements"
  ([] `SNil)
  ([x & rest] `(SCons ~x (slist ~@rest))))

(defmacro do "Sequence IO expressions, return last value"
  ([x] x)
  ([x & rest] `(bind ~x (fn [_] (do ~@rest)))))

(defmacro cond "Multi-way conditional with mandatory default"
  ([x] x)
  ([x body & rest] `(if ~x ~body (cond ~@rest))))

(defmacro str "Concatenate string representations of all arguments"
  ([] (SexpStr ""))
  ([x] `(show ~x))
  ([x & rest] `(str-concat (show ~x) (str ~@rest))))

(defmacro -> "Thread value through forms as first argument"
  ([x] x)
  ([x form & rest]
    (match form
      [(SexpList items)
         (match items
           [(SCons hd tl) `(-> ~(SexpList (SCons hd (SCons x tl))) ~@rest)
            SNil `(-> ~x ~@rest)])
       _ `(-> ~(SexpList (SCons form (SCons x SNil))) ~@rest)])))

(defmacro ->> "Thread value through forms as last argument"
  ([x] x)
  ([x form & rest]
    (match form
      [(SexpList items) `(->> ~(SexpList (sconcat items (SCons x SNil))) ~@rest)
       _ `(->> ~(SexpList (SCons form (SCons x SNil))) ~@rest)])))

(defmacro case "Dispatch on value equality with mandatory default"
  ([expr x] `(let [__case__ ~expr] ~x))
  ([expr x body & rest]
    `(let [__case__ ~expr] (if (= __case__ ~x) ~body (case __case__ ~@rest)))))

(defmacro bind! "Monadic bind sugar"
  ([[] body] body)
  ([[name expr & more] body]
    `(bind ~expr (fn [~name] (bind! [~@more] ~body)))))

(defmacro vec "Construct a vec from elements" [& elems]
  (SexpBracket elems))
