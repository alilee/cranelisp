---
number: 0749
target: /dev
filed_by: /review (cranelisp-backend, S115 W3)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-backend/src/compiler/control_flow/fn_as_value.rs::{compile_auto_curry, build_auto_curry_wrapper, build_auto_curry_drop_glue}; crates/cranelisp-backend/src/compiler/apply.rs::compile_auto_curry_call; design/backend/s115-carrier-and-rc-sweep.md §3
status: open
---

# The 0705 curry-the-local-closure arm leaks the target closure AND the curry env whenever the curried value escapes its defining frame

## Severity
Blocker — an unbounded, per-iteration leak in a shape the new arm ACCEPTS.
The `allocs == deallocs` bar (`s115-carrier-and-rc-sweep.md` §2.3, binding for
the wave) holds only for the immediate-application repro; the arm's general
shape violates Principle 22 (published pointers have retention owners).

## Issue

The W3 change-set landed the `ApplyRef::ViaCallee` + `VarRef::Local` arm and
verified it on the FIXME-0705 repro, where the curried value is applied in the
same expression. Measured at HEAD (`--run --no-cache`, `CRANELISP_RC_STATS=1`,
`PreludeVariant::PrimitivesOnly`, 100 iterations):

```clojure
;; A — the 0705 repro shape (curry applied immediately)     BALANCED
(defn one [] (let [g (fn [a b] (add-i64 a b))] ((g 1) 2)))
      allocs=201 deallocs=201

;; B — the curried value bound in the same frame            BALANCED
(defn one [] (let [g (fn [a b] (add-i64 a b))] (let [h (g 1)] (h 2))))
      allocs=201 deallocs=201

;; C — the curried value RETURNED from the frame            LEAKS 2/iteration
(defn mk  [] (let [g (fn [a b] (add-i64 a b))] (g 1)))
(defn one [] ((mk) 2))
      allocs=201 deallocs=1     rc_inc=201 rc_dec=1
```

Nothing in C is ever released — neither the target closure nor the curry env.
With a heap capture on the target closure the residue is 3 objects/iteration
(`allocs=301 deallocs=1`).

**Two controls isolate the arm as the owner:**

- plain lambda returned + applied (`(defn mk [] (let [s "hello"] (fn [b] …)))`)
  — `allocs=201 deallocs=201`, balanced;
- **global-target** curry returned + applied (`(defn tgt [a b] …) (defn mk []
  (tgt 1))`) — `allocs=101 deallocs=101`, balanced.

So escaping curry envs are released correctly in general; it is specifically the
new closure-VALUE arm that is not. `--run` and `--link` agree (both exit 44 on
the N=100 sum), so this is not a mode divergence.

Two candidate mechanisms for `/dev` to discriminate (not a design):

1. **the curry env is never dec'd on this path.** `rc_dec=1` for 100 iterations
   says the temporary curry env returned by `mk` and consumed by `((mk) 2)` gets
   no release at all in the closure-value case, though the identical
   global-target shape does.
2. **the drop glue deallocs the target without running ITS glue.**
   `build_auto_curry_drop_glue` pushes the target slot as
   `HeapCategory::AlwaysHeap`, and `emit_capture_dec_glue` lowers that to
   `heap::emit_rc_dec(cap_val, dealloc_id, None)` — a plain dec + dealloc with
   NO drop-glue pointer. A closure box must be released through its embedded
   `DROP_GLUE_PTR` (`rc_emission.rs::emit_closure_dec_inline`), or its own
   captures are stranded when the curry env is the last owner. Shape C's
   heap-capture variant (3 objects/iteration) is consistent with this being a
   second, independent hole even once (1) is fixed.

The change-set's claim that the arm's allocs==deallocs is therefore
shape-limited: it was measured only where the target closure's own scope-exit
`emit_closure_dec_inline` happens to run last and mask both mechanisms.

## Proposed resolution

`/dev`(backend): fix the release path for the closure-VALUE capture — the curry
env must be dec'd like any other curry env on this path, and the captured target
must be released through the closure's embedded drop glue, not a bare
`emit_rc_dec`. Land the shapes A/B/C above as unit + e2e pins (`/qa` will want a
`{immediate, let-bound, escaping} × {no capture, heap capture}` matrix — the
standing coverage-by-variants category: one shape passing masked the other two).

## Context

Found by `/review`(backend) probing the W3 change-set's totality arm
adversarially. All numbers reproducible from the commands above at `4ea5c758`.
