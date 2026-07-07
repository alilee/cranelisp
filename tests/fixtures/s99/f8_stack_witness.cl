;; f8_stack_witness.cl — Sprint 105 fixture F8: the parallel stack-allocation witness.
;;
;; PURPOSE (plan §5.2 / §3.1.6-R4 / SPRINT Rev-3): a measurable upper bound on the
;; escape∧uniqueness stack-allocation win BEFORE building it, AND the load-bearing
;; serial-vs-parallel gate-5 DIVERGENCE — the increment-I stack path serves the
;; near-serial in-frame construction but is declined on the sparked / recursive
;; parallel-search branch, so an (a)-isolated *serial* fixture over-states the
;; parallel recovery precisely where the residual lives.
;;
;; STACK-ALLOC TRIGGER (empirically pinned S105): the backend stack-allocs a
;; data-constructor aggregate only when it (1) MATERIALIZES — a phi over two
;; constructors defeats the scalar-replacement that would otherwise register-
;; allocate a statically-known single constructor to nothing (allocs=0) — (2) is
;; NoEscape (matched in the same frame), (3) has all-scalar payload (gate 2), (4)
;; sits in a NON-self-recursive function (gate 3), and (5) is NOT relocated into a
;; spark thunk (gate 5). The phi-`P` below is exactly that shape.
;;
;; THE TWO ARMS (sliced by the harness on the region markers below):
;;   SERIAL arm   (`one` — non-recursive) : gate 3 & gate 5 both CLEAR ⇒ the phi-P
;;                 construction stack-allocates (STACK_SLOT_HITS advances; under
;;                 CRANELISP_NO_STACK_ALLOC it instead heap-allocs once per call —
;;                 the direct-oracle net recovery).
;;   PARALLEL arm (`drive` — self-recursive D&C, the parallel-search shape) : the
;;                 SAME phi-P construction lives lexically inside the recursive,
;;                 spark-bearing apply-args ⇒ gate 3 (self-recursion) declines it,
;;                 and under lenient eval gate 5 additionally declines the spark
;;                 relocation ⇒ STACK_SLOT_HITS stays 0 in BOTH serial and parallel
;;                 compilation. The stack lever does NOT fire on this path.
;;
;; REQUIRED property (plan §5.2): serial-arm hits > 0, parallel-arm hits = 0 — the
;; divergence proving the (a)-allocation on the parallel path is behind gate 3/5.
;; A serial-only witness over-states parallel recovery and is INVALID here.
;;
;; Free-standing: bare primitives only, no stdlib, no prelude.
;; A/B: default = lenient/parallel; CRANELISP_NO_LENIENT=1 = serial. Same result.

(import [primitives [*]])

;; ── Harness-tunable size knob (rewritten by the measurement harness) ──
(defn leaves [] 4096)   ;;S99-KNOB-LEAVES  serial-arm iteration count / parallel-arm range
(defn copies [] 4)      ;;S99-KNOB-COPIES  (unused here; present so scale_synth is a no-op-safe)

(defn rmod [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))
(defn mid-of [lo hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

;; A two-constructor, all-Int-payload ADT. The two constructors force a runtime
;; phi at the construction site (the tag is not statically known), so the aggregate
;; MATERIALIZES rather than being scalar-replaced to registers.
(deftype P (A [:Int x :Int y]) (B [:Int x :Int y]))

;;S105-F8-SERIAL-BEGIN
;; SERIAL arm — non-recursive construction (gate 3 & 5 clear ⇒ stack-allocates).
(defn one [n]
  (let [p (if (eq-i64 (rmod n 2) 0) (A n (add-i64 n 1)) (B (add-i64 n 2) n))]
    (match p [(A x y) (add-i64 x y)  (B x y) (sub-i64 x y)])))

(defn drive-serial [k acc]
  (if (le-i64 k 0) acc
    (drive-serial (sub-i64 k 1) (add-i64 acc (one k)))))
;;S105-F8-SERIAL-END

;;S105-F8-PARALLEL-BEGIN
;; PARALLEL arm — the SAME phi-P construction lexically inside a self-recursive
;; D&C's two independent (spark-bearing) apply-args. gate 3 declines the whole
;; recursive function; gate 5 additionally declines the lenient spark relocation.
(defn drive-parallel [lo hi]
  (if (le-i64 (sub-i64 hi lo) 1)
    lo
    (add-i64
      (let [r (drive-parallel lo (mid-of lo hi))
            p (if (eq-i64 (rmod r 2) 0) (A r (add-i64 r 1)) (B (add-i64 r 2) r))]
        (match p [(A x y) (add-i64 x y)  (B x y) (sub-i64 x y)]))
      (let [r (drive-parallel (mid-of lo hi) hi)
            q (if (eq-i64 (rmod r 2) 0) (A r (add-i64 r 1)) (B (add-i64 r 2) r))]
        (match q [(A x y) (add-i64 x y)  (B x y) (sub-i64 x y)])))))
;;S105-F8-PARALLEL-END

;;S105-F8-MAIN-BOTH
(defn main []
  (Pure (rmod (add-i64 (drive-serial (leaves) 0) (drive-parallel 0 (leaves))) 1000)))
;;S105-F8-MAIN-BOTH-END
;;S105-F8-MAIN-SERIAL   (defn main [] (Pure (rmod (drive-serial (leaves) 0) 1000)))
;;S105-F8-MAIN-PARALLEL (defn main [] (Pure (rmod (drive-parallel 0 (leaves)) 1000)))
