;; f9_loop.cl — Sprint 105 Phase-5 Wave-1b (acid test) fixture F9-LOOP.
;;
;; PURPOSE (acid §(i) control-flow reach — THE PIVOTAL PROBE): the LOOP arm.
;; Cranelisp has NO `loop`/`recur`/`while` special form — iteration is *only*
;; self-recursion (special forms are begin/let/if/fn/match). So a "loop" IS a
;; tail-self-recursive function. Here the phi-P construction lives INLINE in the
;; body of the tail-self-recursive `drive` — i.e. in the loop body itself.
;;
;; Gate 3 (`fn_compiler.rs` §4.1 `fn_has_self_call`) declines stack placement for
;; the WHOLE function on ANY self-call, tail OR non-tail (a slot allocated once
;; per frame would clobber the loop-carried value across the TCO back-edge). So
;; the in-loop-body construction is EXPECTED TO DECLINE.
;;
;; EXPECTED: stack_slot (codegen count) = 0; allocs[stackON] == allocs[NO_STACK_ALLOC]
;; (no recovery — the mechanism never fired). This is the fact that decides whether
;; the delta's serial benefit is broad (loops covered) or narrow (straight-line only).
;;
;; Free-standing: bare primitives only, no stdlib, no prelude.
;; A/B: default = lenient; CRANELISP_NO_LENIENT=1 = serial. Same result.

(import [primitives [*]])

(defn iters [] 2000000)   ;;S99-KNOB-ITERS  loop trip count

(defn rmod [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))

(deftype P (A [:Int x :Int y]) (B [:Int x :Int y]))

;; Tail-self-recursive loop with the phi-P construction INLINE in the body.
;; `drive` contains a self-call ⇒ gate 3 declines the construction's stack slot.
(defn drive [k acc]
  (if (le-i64 k 0) acc
    (let [p (if (eq-i64 (rmod k 2) 0) (A k (add-i64 k 1)) (B (add-i64 k 2) k))
          v (match p [(A x y) (add-i64 x y)  (B x y) (sub-i64 x y)])]
      (drive (sub-i64 k 1) (add-i64 acc v)))))

(defn main []
  (Pure (rmod (drive (iters) 0) 1000)))
