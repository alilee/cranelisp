---
number: 0474
target: /qa
filed_by: /review
filed_at: 2026-07-03
sprint_filed: 101
refers_to: crates/cranelisp-backend/src/compiler/vec_codegen.rs (emit_vec_query_into, emit_vec_set_cow_core, emit_vec_push_cow_core), design/backend/ownership-codegen.md §12.7
status: open
---

# vec-set/vec-push value-use wrapper: COW copy branch leaks the consumed Vec's owned reference

## Severity
Important

## Issue

The S101 Wave-3 NULL-slot fix routes `vec-set`/`vec-push` value-use through
`emit_vec_query_into`, whose RC contract is "every wrapper param arrives OWNED
(consuming closure protocol)". The `vec-get` arm honours this: element inc,
then `emit_vec_rc_dec_with_drop` releases the consumed Vec. The `vec-set` /
`vec-push` arms delegate to the shared COW cores, which release the Vec only
on the **mutate/grow branches** (ownership transfers into the returned same
pointer). On the **rc>1 copy branch** (`vec-set-copy` / `vec-push-copy`
externs, which by the FIXME-0417 division of labour do NOT dec the source
Vec), nobody releases the wrapper's owned reference — one leaked Vec
reference (plus its transitively held elements) per invocation.

At **static** sites this is not a leak: the Vec arg is compiled borrowing
(`compile_arg_list`, no consuming inc) and the binding's scope-exit dec (or
`protect_return_value` machinery) balances it — the cores are line-identical
to the pre-S101 static bodies, so the static path is byte-identical pre/post.
The unbalanced polarity exists only on the **new** wrapper/curry paths, where
the release duty falls on the wrapper itself and the copy branch has no
release.

Concrete shapes that leak (verified by RC accounting against
`emit_capture_inc_into` / closure consuming protocol; not yet reproduced by a
test — the S101 guards all use temporary rc==1 vecs, which take the
non-leaking mutate branch):

- `(defn upd [f v] (f v 0 9))` + `(upd vec-set shared-v)` where `shared-v`
  is still live (rc>1 → copy branch → wrapper's owned ref leaked).
- Curried: `(let [s (vec-set v)] (s 0 9))` — the capture holds one ref, each
  call incs the capture (owned arg) → rc≥2 always → **every call** of a
  curried `vec-set`/`vec-push` closure takes the copy branch and leaks one
  reference on the captured Vec.

Leak-only (no UAF/double-free — the polarity errs on the retain side).

## Proposed resolution

`/qa` authors the narrow repro first (failing-not-ignored, per
`memory/feedback_failing_not_ignored.md`): a heap-balance or
`CRANELISP_RC_STATS` lane over the shared-vec value-use shape above, plus the
curried-call-loop shape, `FIXME(/backend)`-annotated. Resolver is
`/dev`(cranelisp-backend): the cores need a consumed-vec polarity (e.g. a
`vec_is_owned: bool` on `VecSetCow` / a core parameter) so the copy branch
emits an rc-dec of the source Vec when the caller owned it (wrapper/curry
paths) and stays dec-free at static borrowing sites. Sequencing note: this
seam is exactly where increment I's R2-wrapper + `str-len$borrowed` work
lands (backend §12.7 sequencing rationale) — fixing before/with that work
avoids compounding.

## Operational implication / Context

Flagged to `/review` by Wave-3 `/dev` itself (SPRINT Notes, finding (iv):
"COW copy-branch vec-release polarity — shared pre-existing, now
single-sourced"). Review verdict: the *core* is faithfully pre-existing, but
the caller-side release duty is NOT symmetric — static sites had scope
machinery releasing the original; the wrapper has nobody. So this is a real,
new-on-this-path leak class, bounded to leaks. Does not affect the Wave-4
substrate (trap stub / slab / toggle) and does not block Wave 4.
