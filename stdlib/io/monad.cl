;; io/monad.cl — IO monadic interface
;;
;; Core monadic operations for IO: pure, do, bind!.
;;
;; `pure` lifts a value into IO. `do` sequences IO actions via `bind`.
;; `bind!` provides monadic bind sugar with bracket destructuring.
;;
;; `bind` itself is a compiler-seeded inline primitive (in `primitives`).
;;
;; Spec: 10-io.md §10.2-10.5, plan-stdlib.md §3.2

(import [primitives [Pure]])
(import [macros [SexpSym SexpStr SexpInt SexpFloat SexpBool SexpList SexpBracket
                 SCons SNil Sexp SList]])

;; ── Functions ────────────────────────────────────────────────────────

(defn pure "Lift a value into IO" [x] (Pure x))

;; ── Macros ───────────────────────────────────────────────────────────

(defmacro do "Sequence IO actions via bind, return last result"
  ([x] x)
  ([x &rest] `(bind ~x (fn [_] (do ~@rest)))))

;; bind! remains inline — bracket destructuring validated at Ring 3.
(defmacro bind! "Monadic bind sugar"
  ([[] body] body)
  ([[name expr &more] body]
    `(bind ~expr (fn [~name] (bind! [~@more] ~body)))))
