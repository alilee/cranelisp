;; f9_straightline.cl — Sprint 105 Phase-5 Wave-1b (acid test) fixture F9-SL.
;;
;; PURPOSE (acid §(i) control-flow reach): probe WHERE the AS-BUILT
;; statically-sized-all-scalar stack-alloc mechanism (the one F8's serial arm
;; exercises) fires across control-flow shapes. This is the STRAIGHT-LINE arm:
;; the phi-P construction lives in a NON-self-recursive function `one`. Gate 3
;; (self-recursion) is CLEAR for `one`, so the construction is stack-alloc
;; eligible. `drive` is a separate tail loop used only to give the measurement
;; runtime volume — the stack slot lives in `one`'s (non-recursive) frame, fresh
;; per call, so the loop driver does not defeat it (this is exactly F8's serial
;; shape: loop → non-recursive helper).
;;
;; EXPECTED: stack_slot (codegen count) > 0; allocs[stackON] ≈ 0 vs
;; allocs[NO_STACK_ALLOC] ≈ iters (the direct-oracle heap-alloc recovery).
;;
;; Free-standing: bare primitives only, no stdlib, no prelude.
;; A/B: default = lenient; CRANELISP_NO_LENIENT=1 = serial. Same result.

(import [primitives [*]])

(defn iters [] 2000000)   ;;S99-KNOB-ITERS  construction count (runtime volume)

(defn rmod [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))

;; A two-constructor, all-Int-payload ADT — the phi (if over two constructors)
;; forces the aggregate to MATERIALIZE rather than scalar-replace to registers.
(deftype P (A [:Int x :Int y]) (B [:Int x :Int y]))

;; NON-self-recursive: builds + matches one phi-P in its own frame. Gate 3 clear.
(defn one [n]
  (let [p (if (eq-i64 (rmod n 2) 0) (A n (add-i64 n 1)) (B (add-i64 n 2) n))]
    (match p [(A x y) (add-i64 x y)  (B x y) (sub-i64 x y)])))

;; Tail-loop driver — does NOT contain the construction; only supplies volume.
(defn drive [k acc]
  (if (le-i64 k 0) acc
    (drive (sub-i64 k 1) (add-i64 acc (one k)))))

(defn main []
  (Pure (rmod (drive (iters) 0) 1000)))
