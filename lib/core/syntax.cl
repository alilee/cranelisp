(import [primitives [*] macros [*]])

;; ── SList Helpers ───────────────────────────────────

(defn sfold "Fold over an SList" [f init xs]
  (match xs
    [SNil init
     (SCons h t) (sfold f (f init h) t)]))

(defn sreverse "Reverse an SList" [xs]
  (sfold (fn [acc x] (SCons x acc)) SNil xs))

(defn sconcat "Concatenate two SLists" [xs ys]
  (match xs
    [SNil ys
     (SCons h t) (SCons h (sconcat t ys))]))

(defn sempty? "Test if an SList is empty" [xs]
  (match xs
    [SNil true
     _ false]))

;; ── Macro Helpers ───────────────────────────────────

(defn- bind!-fold "Helper for bind! macro: fold binding pairs into nested bind/fn" [items body]
  (match items
    [SNil body
     (SCons name rest1)
       (match rest1
         [(SCons val rest)
            (SexpList (SCons (SexpSym "bind") (SCons val (SCons (SexpList (SCons (SexpSym "fn") (SCons (SexpBracket (SCons name SNil)) (SCons (bind!-fold rest body) SNil)))) SNil))))])]))

(defn- thread-first-fold "Helper for -> macro: thread value as first argument" [acc forms]
  (match forms
    [SNil acc
     (SCons form rest)
       (match form
         [(SexpList items)
            (match items
              [(SCons hd tl) (thread-first-fold (SexpList (SCons hd (SCons acc tl))) rest)])
          _ (thread-first-fold (SexpList (SCons form (SCons acc SNil))) rest)])]))

(defn- thread-last-fold "Helper for ->> macro: thread value as last argument" [acc forms]
  (match forms
    [SNil acc
     (SCons form rest)
       (match form
         [(SexpList items) (thread-last-fold (SexpList (sconcat items (SCons acc SNil))) rest)
          _ (thread-last-fold (SexpList (SCons form (SCons acc SNil))) rest)])]))

(defn- cond-fold "Helper for cond macro: fold test/body pairs into nested if" [clauses]
  (match clauses
    [(SCons x rest)
       (if (sempty? rest)
         x
         (match rest
           [(SCons body rest2)
              (SexpList (SCons (SexpSym "if") (SCons x (SCons body (SCons (cond-fold rest2) SNil)))))]))]))

(defn- case-fold "Helper for case macro: fold value/body pairs into nested if" [:String name clauses]
  (match clauses
    [(SCons x rest)
       (if (sempty? rest)
         x
         (match rest
           [(SCons body rest2)
              (SexpList (SCons (SexpSym "if") (SCons (SexpList (SCons (SexpSym "=") (SCons (SexpSym name) (SCons x SNil)))) (SCons body (SCons (case-fold name rest2) SNil)))))]))]))

(defn- str-fold "Helper for str macro: fold args into nested str-concat of show" [acc args]
  (match args
    [SNil acc
     (SCons x rest)
       (str-fold (SexpList (SCons (SexpSym "str-concat") (SCons acc (SCons (SexpList (SCons (SexpSym "show") (SCons x SNil))) SNil)))) rest)]))

(defn- make-def-name "Mangle name for def implementation" [name-sexp]
  (match name-sexp
    [(SexpSym s) (SexpSym (str-concat s "-def"))]))

(defn- do-build "Helper for do macro: fold exprs into nested let [_ e] ..." [exprs]
  (match exprs
    [(SCons first rest)
       (if (sempty? rest)
         first
         (SexpList (SCons (SexpSym "let")
           (SCons (SexpBracket (SCons (SexpSym "_") (SCons first SNil)))
           (SCons (do-build rest) SNil)))))]))

;; ── Quoting & Definition Macros ─────────────────────

(defmacro const "Define a named constant (bare symbol expansion)" [name value]
  `(defmacro ~name [] ~(quote-sexp value)))

(defmacro const- "Define a private named constant" [name value]
  `(defmacro- ~name [] ~(quote-sexp value)))

(defmacro def "Define a named value (zero-arg function, bare symbol)" [name value]
  `(begin
    (defn ~(make-def-name name) [] ~value)
    (defmacro ~name [] (SexpList (SCons ~(quote-sexp (make-def-name name)) SNil)))))

(defmacro def- "Define a private named value" [name value]
  `(begin
    (defn- ~(make-def-name name) [] ~value)
    (defmacro- ~name [] (SexpList (SCons ~(quote-sexp (make-def-name name)) SNil)))))

;; ── Prelude Macros ──────────────────────────────────

(defmacro list "Construct a list from elements" [& elems]
  (sfold (fn [acc e] `(Cons ~e ~acc)) `Nil (sreverse elems)))

(defmacro slist "Construct an SList from elements" [& elems]
  (sfold (fn [acc e] `(SCons ~e ~acc)) `SNil (sreverse elems)))

(defmacro bind! "Monadic bind sugar" [bindings body]
  (let [items (match bindings [(SexpBracket xs) xs])]
    (bind!-fold items body)))

(defmacro -> "Thread value through forms as first argument" [x & forms]
  (thread-first-fold x forms))

(defmacro ->> "Thread value through forms as last argument" [x & forms]
  (thread-last-fold x forms))

(defmacro cond "Multi-way conditional with mandatory default" [& clauses]
  (cond-fold clauses))

(defmacro case "Dispatch on value equality with mandatory default" [expr & clauses]
  (SexpList (SCons (SexpSym "let")
    (SCons (SexpBracket (SCons (SexpSym "__case__") (SCons expr SNil)))
      (SCons (case-fold "__case__" clauses) SNil)))))

(defmacro do "Sequence expressions, return last value" [& body]
  (do-build body))

(defmacro vec "Construct a vec from elements" [& elems]
  (SexpBracket elems))

(defmacro str "Concatenate string representations of all arguments" [& args]
  (match args
    [SNil (SexpStr "")
     (SCons x rest)
       (str-fold (SexpList (SCons (SexpSym "show") (SCons x SNil))) rest)]))
