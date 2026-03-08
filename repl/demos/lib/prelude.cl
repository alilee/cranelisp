;; prelude.cl — Stable demo prelude for showcase scripts
;;
;; This is a COPY of stdlib/prelude.cl, frozen for demo stability.
;; Demos depend on this file (via CRANELISP_LIB) so that stdlib
;; development doesn't break showcase playback.
;;
;; Update this file deliberately when demos need new prelude features.

(import [macros [SexpSym SexpStr SexpInt SexpFloat SexpBool SexpList SexpBracket
                 SCons SNil Sexp SList]])

;; ── Core types ───────────────────────────────────────────────────────────

(deftype (Option a) None (Some [:a val]))

;; ── Traits: Num ──────────────────────────────────────────────────────────

(deftrait Num
  (+ [self self] self)
  (- [self self] self)
  (* [self self] self)
  (/ [self self] self))

(impl Num Int
  (defn + [a b] (add-i64 a b))
  (defn - [a b] (sub-i64 a b))
  (defn * [a b] (mul-i64 a b))
  (defn / [a b] (div-i64 a b)))

(impl Num Float
  (defn + [a b] (add-f64 a b))
  (defn - [a b] (sub-f64 a b))
  (defn * [a b] (mul-f64 a b))
  (defn / [a b] (div-f64 a b)))

;; ── Traits: Eq ───────────────────────────────────────────────────────────

(deftrait Eq
  (= [self self] Bool)
  (!= [self self] Bool))

(impl Eq Int
  (defn = [a b] (eq-i64 a b))
  (defn != [a b] (not (eq-i64 a b))))

(impl Eq Float
  (defn = [a b] (eq-f64 a b))
  (defn != [a b] (not (eq-f64 a b))))

(impl Eq Bool
  (defn = [a b] (eq-bool a b))
  (defn != [a b] (not (eq-bool a b))))

(impl Eq String
  (defn = [a b] (str-eq a b))
  (defn != [a b] (not (str-eq a b))))

;; ── Traits: Ord ──────────────────────────────────────────────────────────

(deftrait Ord
  (< [self self] Bool)
  (> [self self] Bool)
  (<= [self self] Bool)
  (>= [self self] Bool))

(impl Ord Int
  (defn < [a b] (lt-i64 a b))
  (defn > [a b] (gt-i64 a b))
  (defn <= [a b] (le-i64 a b))
  (defn >= [a b] (ge-i64 a b)))

(impl Ord Float
  (defn < [a b] (lt-f64 a b))
  (defn > [a b] (gt-f64 a b))
  (defn <= [a b] (le-f64 a b))
  (defn >= [a b] (ge-f64 a b)))

;; ── Traits: Display ──────────────────────────────────────────────────────

(deftrait Display
  (show [self] String))

(impl Display Int
  (defn show [x] (int-to-string x)))

(impl Display Float
  (defn show [x] (float-to-string x)))

(impl Display Bool
  (defn show [x] (bool-to-string x)))

(impl Display String
  (defn show [x] x))

;; ── Group A: No helper dependencies ──────────────────────────────────────

(defmacro vec "Construct a vec from elements" [&elems]
  (SexpBracket elems))

(defmacro when "Conditional with implicit None else branch" [test body]
  `(if ~test ~body None))

;; ── Group B: Need quote-sexp primitive ───────────────────────────────────

(defmacro const "Define a named constant (bare symbol expansion)" [name value]
  `(defmacro ~name [] ~(quote-sexp value)))

(defmacro const- "Define a private named constant" [name value]
  `(defmacro- ~name [] ~(quote-sexp value)))

;; ── Group C: Need sconcat (via ~@), multi-clause dispatch ────────────────

(defmacro do "Sequence expressions, return last value"
  ([x] x)
  ([x &rest] `(let [_ ~x] (do ~@rest))))

(defmacro cond "Multi-way conditional with mandatory default"
  ([x] x)
  ([x body &rest] `(if ~x ~body (cond ~@rest))))

(defmacro str "Concatenate string representations of all arguments"
  ([] (SexpStr ""))
  ([x] `(show ~x))
  ([x &rest] `(str-concat (show ~x) (str ~@rest))))

;; ── Group D: Need sconcat + manual Sexp construction ─────────────────────

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

;; ── Group E: Need begin splicing + defmacro-in-results ───────────────────

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

;; ── Group F: Deferred to Ring 4 (IO model needed for testing) ────────────

(defmacro bind! "Monadic bind sugar"
  ([[] body] body)
  ([[name expr &more] body]
    `(bind ~expr (fn [~name] (bind! [~@more] ~body)))))
