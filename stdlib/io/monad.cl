;; io/monad.cl — IO monadic interface
;;
;; Sequencing macros for IO: do, bind!.
;;
;; `do` sequences IO actions via `bind`. `bind!` provides monadic bind sugar
;; with bracket destructuring. Both expand to the `primitives/bind` primitive.
;;
;; The lift is the `primitives/pure` primitive, which the prelude re-exports;
;; this module does not define a second `pure`.
;;
;; Spec: 10-io.md §10.2-10.5, plan-stdlib.md §3.2

(import [prelude []])

(import [macros [SexpSym SexpStr SexpInt SexpFloat SexpBool SexpList SexpBracket
                 SCons SNil Sexp SList]])

;; ── Macros ───────────────────────────────────────────────────────────

(defmacro do "Sequence IO actions via bind, return last result"
  ([x] x)
  ([x &rest] `(primitives/bind ~x (fn [_] (do ~@rest)))))

(defmacro bind! "Monadic bind sugar"
  ([[] body] body)
  ([[name expr &more] body]
    `(primitives/bind ~expr (fn [~name] (bind! [~@more] ~body)))))

;; ── Self-tests ───────────────────────────────────────────────────────
;; Backing file `io/monad/test.cl` (module `io.monad.test`).

(mod- test)
