;; core/io.cl — IO combinators
;;
;; Functions for composing IO computations. `IO` is an opaque primitive type;
;; `pure` and `bind` are its primitives. This module provides higher-order
;; combinators: >>, map-io, timeout, when-io, unless-io, sequence-io.
;;
;; The sequencing macros (do, bind!) live in io/monad.cl; the prelude
;; re-exports them with `primitives/pure`.
;;
;; Every combinator returns an IO action, which a discovered `test-*` function
;; cannot run, so this module has no self-tests. Its evidence is the
;; `stdlib_core_io_*` and `stdlib_timeout_*` cells in tests/stdlib_conformance.rs
;; (plan-stdlib.md §2).
;;
;; Spec: 10-io.md §10.2-10.5
;; Plan: plan-stdlib.md §3.3

(import [prelude []])

;; The null prelude import binds nothing, so the primitives used below are
;; imported explicitly.
(import [primitives [pure bind race sleep Some None]])
(import [collections.list [List Nil Cons]])

(defn >> "Sequence two IO actions, discarding the first result"
  [a b]
  (bind a (fn [_] b)))

(defn map-io "Apply a pure function to the result of an IO action"
  [f io-val]
  (bind io-val (fn [x] (pure (f x)))))

;; timeout — the derived per-request control combinator (spec §10.12.8,
;; design/intrinsics/reactor.md §2.18). `timeout : Int -> IO a -> IO (Option a)`.
;; Runs `io` against a `d`-MILLISECOND timer (the `sleep` runtime leaf): `(Some v)` if
;; `io` completes first (value `v`), `None` if the timer fires first — in which case
;; `io` LOSES the race and is **cancelled** (its future is dropped, releasing its
;; permit + reactor interest, §10.12.9). It is the canonical derivation — NOT a
;; primitive: it composes the `race` primitive (§10.12.8) with the `sleep` runtime
;; leaf, mapping each arm into `Option` so the homogeneous-`race` arms agree on
;; `IO (Option a)`. `timeout` adds NO cancellation plumbing — it inherits the four
;; race-loser drop-release paths from `race` (design/intrinsics/reactor.md §2.18: "per-request timeout
;; is one stdlib line over the `race` primitive").
;; The winner arm passes the bare `Some` constructor as `map-io`'s `f`: an ADT
;; constructor is a first-class function value.
(defn timeout "Run io against a d-millisecond timer: (Some v) if io wins, None if the timer fires (cancelling io)"
  [d io]
  (race (map-io Some io)
        (map-io (fn [_] None) (sleep d))))

(defn when-io "Perform an IO action only if condition is true, otherwise pure unit"
  [cond io-action]
  (if cond io-action (pure 0)))

(defn unless-io "Perform an IO action only if condition is false, otherwise pure unit"
  [cond io-action]
  (if cond (pure 0) io-action))

(defn sequence-io "Execute a list of IO actions and collect results into a list"
  [ios]
  (match ios
    [Nil (pure Nil)
     (Cons hd tl)
       (bind hd (fn [x]
         (bind (sequence-io tl) (fn [xs]
           (pure (Cons x xs))))))]))
