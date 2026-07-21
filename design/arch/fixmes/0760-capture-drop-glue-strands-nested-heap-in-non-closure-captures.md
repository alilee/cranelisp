---
number: 0760
target: /design
filed_by: /dev (cranelisp-backend, S115 W3b)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::emit_capture_dec_glue; crates/cranelisp-backend/src/compiler/control_flow/capture_rc.rs::CaptureRelease; crates/cranelisp-backend/src/compiler/rc_emission.rs::{emit_typed_rc_dec, typed_release_kind}
status: open
---

# The capture drop-glue releases a Vec-of-heap / ADT-with-heap-field capture with a bare dec — the last stranding site, and the one the borrowed-builder constraint blocks

## Severity

Important — a per-iteration leak in an ordinary shape (a closure capturing a
vec of strings, or an ADT with a heap field), scaling with the number of
closures created. Not a Blocker only because it is PRE-EXISTING, leak-only
(never a spurious dec), and independent of the 0749 arm.

## Issue

W3b closed three faces of one class — *"a release that frees the box and
strands what the box owns"*:

- `apply.rs::emit_post_call_decs` (FIXME 0753) → routed onto the new ONE
  type-directed release `rc_emission::emit_typed_rc_dec` (Vec → `vec_drop` +
  per-element dec; ADT → recursive inline glue; `Fn` → the box's embedded
  `DROP_GLUE_PTR`; else plain dec);
- `rc_emission::emit_field_decs` (the ADT drop-glue field walk) → its
  open-coded copy of that dispatch replaced by the shared helper;
- `lambda.rs::emit_capture_dec_glue` (FIXME 0749 mechanism (b)) → the CLOSURE
  case only, via `capture_rc::CaptureRelease::ClosureBox`.

**The capture glue's non-closure cases remain.** A capture classified
`HeapCategory::AlwaysHeap` that is a Vec-of-heap or an ADT-with-heap-fields
still takes `heap::emit_rc_dec(.., None)`.

Measured at W3b HEAD (`--run --no-cache`, `CRANELISP_RC_STATS=1`,
`PreludeVariant::PrimitivesOnly`, 100 iterations, IDENTICAL under both
ownership toggles):

```clojure
;; K — a closure capturing a Vec of Strings          LEAKS 2/iteration
(defn mk [] (let [v ["aa" "bbb"]] (fn [c] (add-i64 c (str-len (vec-get v 0))))))
(defn one [] ((mk) 2))
      allocs=401 deallocs=201        ; the two element strings, every iteration

;; L — a closure capturing an ADT with a String field  LEAKS 1/iteration
(deftype W (Wr [s]))
(defn mk [] (let [w (Wr "hello")] (fn [c] (add-i64 c (match w [(Wr s) (str-len s)])))))
(defn one [] ((mk) 2))
      allocs=301 deallocs=201        ; the field string, every iteration
```

Controls that are now EXACT (so the residual is specifically this seam): a
closure capturing a plain Vec of scalars (201/201); a closure capturing another
CLOSURE that captures a String (301/301 — the W3b `ClosureBox` arm); the same
Vec-of-Strings / ADT-with-String values passed as a `Borrowed` ARGUMENT rather
than captured (exact — the W3b `emit_post_call_decs` arm).

## Why `/dev` did not just fix it

`emit_typed_rc_dec` and everything it dispatches to
(`emit_rc_dec_with_inline_drop_glue` → `lookup_type_def` →
`emit_drop_glue_field_decs`, recursive; `emit_vec_aware_rc_dec` →
`build_elem_dec_fn`) are `&mut self` methods emitting into `self.builder`.
The capture drop glue builds its body in a **separate Cranelift context**
(`self.module.make_context()` + a local `FunctionBuilder`), which is exactly
why `CaptureRelease` exists at all and why `emit_closure_dec_into` had to be
extracted as a borrowed-builder free fn (that one was ~40 lines with no
recursion and no symbol-table probing; these are not).

Making the whole type-directed release borrowed-builder-shaped is a
design-scale refactor of the RC-emission spine (three interlocking recursive
emitters + the `drop_glue_depth` counter that lives on `FnCompiler`), with a
real alternative worth weighing: **emit a real named drop-glue FUNCTION per
type and have every release site `call` it**, which is what the
`emit_inline_drop_glue` rustdoc has called "a temporary measure until proper
drop glue functions are generated" since it was written. That is a `/design`
call, not a `/dev` one.

## Proposed resolution

`/design`(backend): rule between
(a) making the type-directed release borrowed-builder-parameterised (mechanical,
    keeps inline emission, ~3 emitters + the depth counter to thread), and
(b) per-type named drop-glue functions called from every release site (the
    long-signalled end state; collapses ALL of `emit_typed_rc_dec`'s arms and
    the `MAX_DROP_GLUE_DEPTH=4` truncation, whose own comment already admits
    "fields leak" past the limit — a second, independent instance of this class).

Then `/dev` implements against the ruling and the K/L shapes above become the
acceptance pins.

## Instrumentation (METHOD §2.2)

**(c) — NONE exists.** No standing mechanism asserts that a release reaches
everything the released value owns. The three W3b faces were all found by
hand-measuring `allocs == deallocs` on shapes someone thought to write.

The instrument that would catch the whole class: an **exact-balance lane** —
`allocs == deallocs` asserted absolutely, over a shape matrix crossing
{owning type: Vec-of-heap, ADT-with-heap-field, closure-with-capture, nested}
× {position: captured, `Borrowed` argument, returned, loop-carried}. Routed to
`/qa` as FIXME 0761. The existing `SafetyMatrix` RC face is **blind to this
class by construction**: it asserts the ON and OFF imbalances are EQUAL, and
every leak in this family is toggle-independent, so it passes on both.

The in-crate half landed with the fix: `typed_release_kind` is now the ONE
classification and `emit_typed_rc_dec` matches it exhaustively, so a new
owning shape is a compile error at the dispatch rather than a silent
fall-through to the stranding plain dec. What it cannot do is force a
SITE to use it — that is what the balance lane is for.

## Context

Found by `/dev`(backend) while diagnosing FIXME 0749 mechanism (b): the
closure-capture stranding it names is one member of a family, and the
measurement battery above fell out of isolating it.
