;; prelude.cl — Standard prelude for Cranelisp
;;
;; Loaded implicitly for all non-prelude modules. Re-exports from domain
;; modules plus convenience macros defined inline.
;;
;; Domain modules (traits, types, macros):
;;   compare.eq     — Eq trait + impls
;;   compare.ord    — Ord trait + impls
;;   num.num        — Num trait + impls
;;   text.display   — Display trait + impls
;;   fn.option      — Option type
;;   fn.result      — Result type
;;   fn.threading   — ->, ->> macros
;;
;; Most macros remain inline because they are small or used by the prelude
;; itself. Larger macros (threading) are in dedicated modules.
;;
;; Spec references: 07-traits.md §7.1-7.4, 09-macros.md §9.5, §9.6, §9.10

;; ── Domain module imports (traits + types + macros) ────────────────────

(import [compare.eq [Eq = !=]])
(import [compare.ord [Ord < > <= >=]])
(import [num.num [Num + - * /]])
(import [text.display [Display show]])
(import [fn.option [Option Some None]])
(import [fn.result [Result Ok Err]])
(import [fn.threading [-> ->>]])
(import [collections.list [List Nil Cons empty?]])
(import [core.io [pure]])

;; ── Macro dependencies ─────────────────────────────────────────────────

(import [macros [SexpSym SexpStr SexpInt SexpFloat SexpBool SexpList SexpBracket
                 SCons SNil Sexp SList]])

;; ── Group A: No helper dependencies ────────────────────────────────────

(defmacro vec "Construct a vec from elements" [&elems]
  (SexpBracket elems))

(defmacro when "Conditional with implicit None else branch" [test body]
  `(if ~test ~body None))

;; ── Group B: Need quote-sexp primitive ─────────────────────────────────

(defmacro const "Define a named constant (bare symbol expansion)" [name value]
  `(defmacro ~name [] ~(quote-sexp value)))

(defmacro const- "Define a private named constant" [name value]
  `(defmacro- ~name [] ~(quote-sexp value)))

;; ── Group C: Need sconcat (via ~@), multi-clause dispatch ──────────────

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

;; ── Group D: Need sconcat + manual Sexp construction ───────────────────

(defmacro case "Dispatch on value equality with mandatory default"
  ([expr x] `(let [__case__ ~expr] ~x))
  ([expr x body &rest]
    `(let [__case__ ~expr] (if (= __case__ ~x) ~body (case __case__ ~@rest)))))

;; -> and ->> threading macros are in fn.threading (imported above)

;; ── Group E: Need begin splicing + defmacro-in-results ─────────────────

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

;; ── Group F: IO combinators (Ring 4) ─────────────────────────────────

;; pure is in core.io (imported above)

;; bind! remains inline — bracket destructuring validated at Ring 3.
(defmacro bind! "Monadic bind sugar"
  ([[] body] body)
  ([[name expr &more] body]
    `(bind ~expr (fn [~name] (bind! [~@more] ~body)))))

;; FIXME(/stdlib): When the IO trampoline is operational and all pure `do`
;; uses are migrated to `let [_ ...]`, replace the Group C `do` macro
;; (which uses `let`) with the IO-specific version (expanding to `bind`
;; calls per spec 10.4). The IO `do` is available at `core.io` but not
;; re-exported yet to avoid breaking existing pure-sequencing uses.
;; See plan-stdlib.md §4 Ring 4 Additions.
