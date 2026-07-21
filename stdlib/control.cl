;; control.cl — Control flow macros
;;
;; Conditional and branching macros that don't fit in core special forms.
;;
;; Spec: 09-macros.md §9.5, plan-stdlib.md §3.2

(import [prelude []])

(import [macros [SexpSym SexpStr SexpInt SexpFloat SexpBool SexpList SexpBracket
                 SCons SNil Sexp SList]])

;; `Some`/`None` are the canonical PRIMITIVE constructors (see fn/option.cl —
;; `fn.option` re-exports them rather than defining a second Option). The
;; `when`/`unless` expansions below wrap the body in `Some`, so the two `if`
;; branches unify at `(Option a)` for ANY body type.
(import [primitives [Some None]])

;; `when`/`unless` return an `Option`: the body's value wrapped in `Some` when
;; the branch is taken, `None` otherwise.
;;
;; The body MUST be wrapped. `(if ~test ~body None)` — the pre-S115 expansion —
;; requires the two `if` branches to unify, so it only typechecked when the body
;; was ALREADY an `(Option a)`; `(when true 5)` failed with "expected
;; primitives/Int, got (primitives/Option t)". Wrapping makes the taken branch
;; `(Option a)` for any body type `a`. Self-tested in `control/test.cl`.

(defmacro when "Conditional returning (Some body) when test holds, else None" [test body]
  `(if ~test (Some ~body) None))

(defmacro unless "Conditional returning (Some body) when test fails, else None" [test body]
  `(if ~test None (Some ~body)))

(defmacro cond "Multi-way conditional with mandatory default"
  ([x] x)
  ([x body &rest] `(if ~x ~body (cond ~@rest))))

(defmacro case "Dispatch on value equality with mandatory default"
  ([expr x] `(let [__case__ ~expr] ~x))
  ([expr x body &rest]
    `(let [__case__ ~expr] (if (= __case__ ~x) ~body (case __case__ ~@rest)))))

;; ── Self-tests ───────────────────────────────────────────────────────
;; Backing file `control/test.cl` (module `control.test`), private per
;; stdlib/CLAUDE.md §Conventions.

(mod- test)
