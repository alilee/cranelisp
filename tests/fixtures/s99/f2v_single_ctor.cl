;; f2v_single_ctor.cl — Sprint 103 increment-II fixture F2v: the honest R5 witness.
;;
;; IDENTICAL divide-and-conquer REDUCE tree + copy-per-guess leaf work to F2
;; (f2_contention.cl) — same shape, same spark count, same shared-grid copies.
;; The ONLY difference is the payload type: F2's `Cell` is a TWO-constructor ADT
;; (`Given`/`Solved`); F2v's is a ONE-constructor, one-word, scalar-payload
;; wrapper `(Cell [:Int value])`.
;;
;; Why a distinct fixture: R5's first landing (design/backend/ownership-codegen.md
;; §7.1/§7.2) flattens ONLY one-word single-constructor payloads — a `Vec Cell`
;; of these can hold the `Cell`s by value with null element drop/clone fns and
;; `memcpy`-able copies, collapsing the per-copy rc_inc volume F2 pays. F2's
;; two-ctor `Cell` is NOT covered by R5's first landing (it is the II-G4 honesty
;; witness). F2v is therefore the ratified II-G1 witness (qa plan §2, S100 close):
;; a shape R5 genuinely cures, so the rc_inc-collapse + parallel-must-pay gate is
;; attributable to the mechanism and not to borrow-elision.
;;
;; Free-standing: bare primitives only, no stdlib, no prelude.
;; A/B: default = lenient/parallel; CRANELISP_NO_LENIENT=1 = serial. Same result.

(import [primitives [*]])

(deftype Cell (Cell [:Int value]))

(defn cell-value [c] (match c [(Cell v) v]))

;; ── Harness-tunable size knobs (rewritten by the measurement harness) ──
(defn leaves [] 64)   ;;S99-KNOB-LEAVES  tree width (leaf count = parallelism)
(defn copies [] 4)    ;;S99-KNOB-COPIES  shared-grid copies per leaf

(defn rem-i64 [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))
(defn mid-of [lo hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

(defn build-grid [v i n]
  (if (eq-i64 i n) v
    (build-grid (vec-push v (Cell (add-i64 (rem-i64 i 9) 1))) (add-i64 i 1) n)))

;; F2v leaf work: copy the SHARED grid K times. Each `(vec-set g i ...)` copies
;; the whole N-cell Vec (g is shared, rc>1) — but with R5, the `Cell` elements
;; are one-word by-value payloads copied by `memcpy` with null elem fns (no
;; per-cell rc_inc). Always copy the ORIGINAL shared `g` so every iteration is a
;; real shared-copy, not a cheap COW-in-place mutation.
(defn copy-work [g i k acc]
  (if (le-i64 k 0) acc
    (let [g2 (vec-set g i (Cell k))]
      (copy-work g i (sub-i64 k 1)
        (add-i64 acc (cell-value (vec-get g2 i)))))))

(defn leaf-work [g lo]
  (copy-work g (rem-i64 lo (vec-len g)) (copies) 0))

;; Same D&C reduce as F2 — independent apply-arg halves auto-spark.
(defn reduce-tree [g lo hi]
  (if (le-i64 (sub-i64 hi lo) 1)
    (leaf-work g lo)
    (add-i64 (reduce-tree g lo (mid-of lo hi))
             (reduce-tree g (mid-of lo hi) hi))))

(defn main []
  (let [g (build-grid [] 0 81)]
    (Pure (rem-i64 (reduce-tree g 0 (leaves)) 251))))
