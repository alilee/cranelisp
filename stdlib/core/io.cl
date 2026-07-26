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
;;
;; ── KNOWN RED: this module does not compile at HEAD (FIXME 0907) ─────────
;;
;; `stdlib_conformance` reports this module and its parent `core` as the only
;; two of 38 that fail. The failing symbol is `core.io/when-io`:
;;
;;   codegen failed for core.io/when-io: constructor 'Bind' disagrees on
;;   declared parameter identity for 'primitives/IO'
;;
;; Cause is NOT in this file. `primitives/IO`'s `Bind` constructor is seeded
;; with an existential encoding (`src/bootstrap.rs`), so per-concrete drop
;; glue cannot be derived for any concrete `IO T`; W3's canonical-glue
;; migration turned the former silent shallow teardown into a loud refusal.
;; Ruling is owed by `/design`(backend), co-ruled with FIXME 0903 (S119).
;;
;; DO NOT WORK AROUND IT. Measured at HEAD (assessment recorded on 0907):
;;   - `when-io`/`unless-io` refuse at DEFINITION because one `if` arm is the
;;     borrowed `io-action` parameter and the other is a freshly built
;;     concrete `(Pure 0)` :: `(IO Int)`. Two fresh arms (`(if c (Pure 1)
;;     (Pure 0))`) compile; the mixed arm is the trigger, and the same mixed
;;     shape over an ordinary user ADT compiles — the refusal is IO-specific.
;;   - `>>`/`map-io`/`timeout`/`sequence-io` compile here (uninstantiated
;;     polymorphs) but refuse at EVERY concrete call site.
;;   - Re-spelling `when-io` polymorphically (a third `alt` parameter, no
;;     concrete `Pure`) compiles the definition and STILL refuses at every
;;     concrete call.
;; So no spelling makes the capability reachable; a re-spelling would only
;; move a loud module-level failure to a loud call-site failure and hide the
;; defect from the conformance gate. The red module is the honest record.
;;
;; WITHHELD SELF-TESTS (per stdlib/CLAUDE.md — a ceilinged module enumerates
;; its restore list rather than shipping silence). There is no `(mod- test)`
;; here because every case below needs a concrete `IO T` and therefore cannot
;; run until 0907 is ruled. Restore all six with a backing `core/io/test.cl`
;; in the fixing change-set:
;;   1. `>>`  sequences two effects, discarding the first result
;;   2. `map-io` applies a pure fn to an IO result
;;   3. `when-io` true → runs the action; false → `(Pure 0)`
;;   4. `unless-io` false → runs the action; true → `(Pure 0)`
;;   5. `sequence-io` over Nil and over a 3-element Cons list, order preserved
;;   6. `timeout` — winner arm `(Some v)`; timer arm `None` with the loser
;;      cancelled (see spec §10.12.8/§10.12.9)

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
;; The winner-arm passes the bare `Some` constructor as `map-io`'s `f`: an ADT
;; constructor is a first-class fn-value (ctor-as-value fixed, 0712 — S114 Phase 6).
(defn timeout "Run io against a d-millisecond timer: (Some v) if io wins, None if the timer fires (cancelling io)"
  [d io]
  (race (map-io Some io)
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
