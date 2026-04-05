;; core/io.cl — IO combinators
;;
;; Functions for composing IO computations. The IO type is compiler-seeded
;; (Pure, Effect, Bind constructors in `primitives`). `bind` is an inline
;; primitive. This module provides higher-order combinators: >>, map-io,
;; when-io, unless-io, sequence-io.
;;
;; The monadic interface (pure, do, bind!) lives in io/monad.cl and is
;; re-exported through the prelude.
;;
;; Spec: 10-io.md §10.2-10.5
;; Plan: plan-stdlib.md §3.3 io/, §5.5

;; Pure and Effect constructors are in `primitives` but stored as Import
;; entries in `user` (not seeded into new modules). Explicit import needed.
(import [prelude []])

(import [primitives [Pure]])
(import [collections.list [List Nil Cons]])

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
