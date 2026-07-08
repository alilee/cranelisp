;; f9_nontailrec.cl — Sprint 105 Phase-5 Wave-1b (acid test) fixture F9-REC.
;;
;; PURPOSE (acid §(i) control-flow reach): the NON-TAIL-RECURSIVE arm. The phi-P
;; construction lives INLINE in the leaf of a non-tail (divide-and-conquer)
;; self-recursive `drive`. Like the loop arm, `drive` contains a self-call, so
;; gate 3 (`fn_has_self_call`) declines stack placement for the whole function.
;;
;; Measured under CRANELISP_NO_LENIENT=1 (serial compile) so the decline is
;; attributable to gate 3 (self-recursion) ALONE and not conflated with gate 5
;; (spark-thunk relocation), which would also decline under lenient eval.
;;
;; EXPECTED: stack_slot (codegen count) = 0; allocs[stackON] == allocs[NO_STACK_ALLOC]
;; (no recovery). Confirms recursion (of any kind) trips the same gate as loops.
;;
;; Free-standing: bare primitives only, no stdlib, no prelude.
;; A/B: default = lenient; CRANELISP_NO_LENIENT=1 = serial. Same result.

(import [primitives [*]])

(defn extent [] 2000000)   ;;S99-KNOB-EXTENT  D&C leaf range (≈ construction count)

(defn rmod [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))
(defn mid-of [lo hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

(deftype P (A [:Int x :Int y]) (B [:Int x :Int y]))

;; Non-tail self-recursive D&C; the phi-P construction is inline at the leaf.
;; `drive` contains a self-call ⇒ gate 3 declines the construction's stack slot.
(defn drive [lo hi]
  (if (le-i64 (sub-i64 hi lo) 1)
    (let [p (if (eq-i64 (rmod lo 2) 0) (A lo (add-i64 lo 1)) (B (add-i64 lo 2) lo))]
      (match p [(A x y) (add-i64 x y)  (B x y) (sub-i64 x y)]))
    (add-i64 (drive lo (mid-of lo hi)) (drive (mid-of lo hi) hi))))

(defn main []
  (Pure (rmod (drive 0 (extent)) 1000)))
