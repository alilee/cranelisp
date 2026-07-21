---
number: 0763
target: /testing
filed_by: /dev (cranelisp-backend, S115 W3b)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/adt_wrapped_supersede_leak_0720.rs (the shape/harness precedent); design/arch/fixmes/0749, 0753
status: open
---

# E2e leak pins for the W3b RC-release batch — the shapes, the harness, and the exact numbers (all GREEN at W3b HEAD)

## Severity

Important, and **in-wave** — not a next-sprint carry. The unit tier landed with
the fix (METHOD §2.2); this is the second tier for the two faces that are
observable only end-to-end (a per-iteration alloc/dealloc imbalance across
`--run` and `--link`).

## Why this is a FIXME and not a test

`/dev` owns unit tests inside the crate and does NOT author `tests/`
(`triad-shared.md` §Testing ownership; `.claude/commands/dev.md` §Boundary).
The measurements below were taken by `/dev` and are reproducible verbatim; the
authoring is `/testing`'s. `/sprint`: this wants a `/testing` dispatch inside
W3b, not after it.

## The pins

Harness: the `rc_alloc_dealloc` helper in
`tests/adt_wrapped_supersede_leak_0720.rs` verbatim (`PreludeVariant::
PrimitivesOnly`, `--run`, `CRANELISP_RC_STATS=1`, `CRANELISP_NO_LENIENT=1`).
Every cell below is measured at W3b HEAD and is **GREEN** — these are
regression guards on freshly-fixed behaviour, not defect repros.

**A. FIXME 0749 — the curry-the-local-closure arm across the escape axis.**
The W3 change-set verified only shape A (applied in the same expression); the
leak lived in shape C. `{immediate, let-bound, escaping} × {no capture, String
capture on the target closure}`, `assert_eq!(allocs, deallocs)`, 100
iterations, BOTH toggles (`CRANELISP_NO_OWNERSHIP` set and unset) AND `--link`
as well as `--run`:

```clojure
;; A — applied immediately                              201/201
(defn one [] (let [g (fn [a b] (add-i64 a b))] ((g 1) 2)))
;; B — curried value let-bound in the same frame        201/201
(defn one [] (let [g (fn [a b] (add-i64 a b))] (let [h (g 1)] (h 2))))
;; C — curried value RETURNED from its defining frame   201/201  (was 201/1)
(defn mk  [] (let [g (fn [a b] (add-i64 a b))] (g 1)))
(defn one [] ((mk) 2))
;; C2 — as C, target closure captures a String          301/301  (was 301/1)
(defn mk [] (let [s "hello"] (let [g (fn [a b] (add-i64 (add-i64 a b) (str-len s)))] (g 1))))
(defn one [] ((mk) 2))
```
Driver used for all four: `(defn go [n acc] (if (eq-i64 n 0) acc (go (sub-i64 n 1) (add-i64 acc (one))))) (defn main [] (Pure (go 100 0)))`.
Exit codes: A/B/C 44, C2 32.

**B. The same defect with NO curry involved** (the mechanism was
`is_fresh_construction` not covering the box-minting node kinds, so these are
independent faces of one fix and each guards a different arm):

```clojure
;; D — a plain lambda returned through TWO lets         301/301  (was 301/101)
(defn mk [] (let [s "hello"] (let [t "world"] (fn [b] (add-i64 b (str-len s))))))
(defn one [] ((mk) 2))
;; E — a VecLit returned through one let                201/201  (was 201/101)
(defn mk [] (let [s "hello"] [1 2 (str-len s)]))
(defn one [] (vec-len (mk)))
;; F — a lambda capturing another closure               301/301  (was 301/1)
(defn mk [] (let [s "hello"] (let [g (fn [b] (add-i64 b (str-len s)))] (fn [c] (g c)))))
(defn one [] ((mk) 2))
```

**C. FIXME 0753 — the toggle-ON constant residual.** The minimal repro is
smaller than the 0720 loop and does not need TCO, a loop, or `vec-set`:

```clojure
(deftype G2 (Gr [cells]))
(defn peek [g] 7)
(defn main [] (Pure (peek (Gr [5 5]))))
```
ON 3/3 and OFF 3/3 (was ON 3/2, OFF 3/3 — the toggle ASYMMETRY is the
signature, so pin BOTH toggles and assert they agree AND are exact). The
String-field twin `(deftype G2 (Gr [s])) (defn peek [g] (match g [(Gr s) (str-len s)])) (defn main [] (Pure (peek (Gr "hi"))))`
is 3/3 both toggles.

Also extend the existing `adt_wrapped_supersede_leak_0720.rs` residue cells:
the 0720 face is now EXACT at every N in BOTH toggles — N=1 5/5, N=2 7/7,
N=200 403/403, N=400 803/803. The current test asserts non-scaling; it should
assert exact equality, which is what §2.3 actually requires. The bare-vec twin
control is undisturbed (ON 2/2 `reuse_hit=200`; OFF 202/202 `reuse_miss=200`).

## The standing-instrument half

These pins are examples. The instrument that would have caught the whole batch
is an exact-balance lane over {owning type} × {position}, filed separately as
FIXME 0761 (`target: /qa`). Please read them together — 0761 is the mechanism,
0763 is this wave's evidence.

## Context

`/dev`(backend), S115 W3b. All numbers reproducible from a scratch dir
containing `tests/fixtures/preludes/primitives-only.cl` as `prelude.cl` plus
the source above as `user.cl`.
