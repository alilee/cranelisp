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

;; `bind` is a compiler-seeded inline primitive in `primitives`; import it so the
;; bare `bind` in the combinators below resolves under the null-prelude import.
(import [primitives [Pure bind race sleep Some None]])
(import [collections.list [List Nil Cons]])

(defn >> "Sequence two IO actions, discarding the first result"
  [a b]
  (bind a (fn [_] b)))

(defn map-io "Apply a pure function to the result of an IO action"
  [f io-val]
  (bind io-val (fn [x] (Pure (f x)))))

;; timeout — the derived per-request control combinator (S96 Chunk C4, slice 7;
;; spec §10.12.8, design/int/reactor.md §2.18). `timeout : Int -> IO a -> IO (Option a)`.
;; Runs `io` against a `d`-MILLISECOND timer (the `sleep` runtime leaf): `(Some v)` if
;; `io` completes first (value `v`), `None` if the timer fires first — in which case
;; `io` LOSES the race and is **cancelled** (its future is dropped, releasing its
;; permit + reactor interest, §10.12.9). It is the canonical derivation — NOT a
;; primitive: it composes the `race` primitive (§10.12.8) with the `sleep` runtime
;; leaf, mapping each arm into `Option` so the homogeneous-`race` arms agree on
;; `IO (Option a)`. `timeout` adds NO cancellation plumbing — it inherits the four
;; race-loser drop-release paths from `race` (reactor.md §2.18: "per-request timeout
;; is one stdlib line over the `race` primitive").
;; NB: the winner-arm wraps the `Some` constructor in an explicit lambda
;; (`(fn [x] (Some x))`) rather than passing `Some` itself as `map-io`'s `f`. A
;; bare ADT constructor applied as a first-class fn-value currently miscompiles
;; (FIXME 0476 — `(apply-it Some 7)` SIGSEGVs, no IO involved); the lambda form
;; applies the constructor directly and is the supported shape.
(defn timeout "Run io against a d-millisecond timer: (Some v) if io wins, None if the timer fires (cancelling io)"
  [d io]
  (race (map-io (fn [x] (Some x)) io)
        (map-io (fn [_] None) (sleep d))))

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
