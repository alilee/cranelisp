;; core/io.cl — IO combinators
;;
;; Functions and macros for composing IO computations. The IO type is
;; compiler-seeded (Pure, Effect, Bind constructors in `primitives`).
;; `bind` is an inline primitive. This module provides the standard
;; library surface: `pure`, `>>`, and higher-order combinators.
;;
;; Macros `do` (IO sequencing) and `bind!` (monadic bind sugar) are
;; defined in prelude.cl because they are prelude-level conveniences.
;; The IO-specific `do` that expands to `bind` calls will replace the
;; pure-sequencing `do` once the IO trampoline is operational.
;;
;; Spec: 10-io.md §10.2-10.5
;; Plan: plan-stdlib.md §3.3 io/, §5.5

;; Pure and Effect constructors are in `primitives` but stored as Import
;; entries in `user` (not seeded into new modules). Explicit import needed.
(import [primitives [Pure]])
(import [collections.list [List Nil Cons]])

;; ── Functions ────────────────────────────────────────────────────────

(defn pure "Lift a value into IO" [x] (Pure x))

(defn >> "Sequence two IO actions, discarding the first result"
  [a b]
  (bind a (fn [_] b)))

(defn map-io "Apply a pure function to the result of an IO action"
  [f io-val]
  (bind io-val (fn [x] (Pure (f x)))))

(defn when-io "Perform an IO action only if condition is true, otherwise pure unit"
  [cond io-action]
  (if cond io-action (Pure 0)))

(defn unless-io "Perform an IO action only if condition is false, otherwise pure unit"
  [cond io-action]
  (if cond (Pure 0) io-action))

(defn sequence-io "Execute a list of IO actions and collect results into a list"
  [ios]
  (match ios
    [Nil (Pure Nil)
     (Cons hd tl)
       (bind hd (fn [x]
         (bind (sequence-io tl) (fn [xs]
           (Pure (Cons x xs))))))]))
