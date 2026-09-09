# Binding scope — binder identity in the backend

> **Status**: Live. The S121 binder-slot repair and approved tail-transfer
> correction are delivered.
> **Owner**: `design` (cranelisp-backend). **Surface**: backend interior only.
> **Authority**: `spec/04-expressions.md` §4.3 (sequential visibility,
> repeated names, shadowing), and `spec/12-runtime.md` §12.3.1 and §12.4.3
> (release of unreachable heap values and lenient-binding independence).

## Purpose and invariant

The backend identifies a binder by its slot, never by its spelling. A name is a
lexical-resolution query, not the key for a binder's value, type, borrow mark,
or release obligation. Consequently, leaving a scope removes only that frame's
slots, and same-name binders in a binding vector retain separate obligations.

This is an interior correction only: it changes neither language semantics nor
any public facade, persisted schema, or cross-crate edge.

## Binding environment

`ScopeChain` is a stack of ordered frames. Each `BinderSlot` owns one binder's
Cranelift `Variable`, optional type, borrowed mark, borrow root, and name for
resolution. The latest matching slot in the innermost applicable frame denotes
a name. Frame cleanup consumes `(Variable, Type)` directly from each slot; it
does not resolve a name again.

`CaptureEnv` is distinct from the chain. It is seeded once for an inner
compiler and is owned by the closure environment's drop glue, rather than by a
body frame. Resolution consults a live local slot before a capture, so a local
shadow does not release or overwrite its capture.

`bind_local` publishes a local's value and optional type together after its
initializer has compiled. A repeated binder's initializer therefore observes
the preceding binder's complete facts. `fresh_variable` is private and its only
construction paths are `bind_local` and `bind_capture`; slots consequently get
their `Variable` through that single mint boundary.

Per-binding-vector lenient state is positional. Spark admission and dependency
lookup ask which binder is denoted before a position, so a later rebinding
displaces an earlier spark record instead of colliding by name.

The obsolete per-binding closure-glue fields are absent: canonical,
type-directed release has no per-binding glue identifier to retain.

## Tail transfer

A bare, top-level variable argument to a direct tail self-call moves the exact
binding it denotes into the next iteration. The tail cleanup must skip that
binding alone; it must release every displaced same-name binding.

At the direct-tail-call site, after arguments are compiled and before any tail
cleanup, resolve each literal top-level `MonoExpr::Var` against the live
`ScopeChain`. Collect the resolved `SlotRef`s in a private per-call transfer
set. An unbound name or capture yields no local transfer target. Thread that
set to both let-frame cleanup and superseded-parameter cleanup. A cleanup site
skips an old owner only when its own `SlotRef` is in the set.

This makes `(let [x discarded x carried] (go … x))` move only `carried`; the
first `x` remains unreachable and is released before the backedge. It also
prevents a local `x` from licensing a skip for a parameter `x`.

The slot set replaces only the old-owner transfer decision. Existing TCO
controls keep their separate responsibilities and inputs:

- Only literal top-level variables are transfers. `if`/`match` aliases stay
  outside the set and retain the established branch protective-inc followed by
  uniform flush.
- Borrowed-alias validation and escaping-borrow protection remain the existing
  controls; this visit does not weaken or widen their diagnostic policy.
- The in-place-COW exemption and TCO-promoted-parameter ownership remain
  independent decisions.

## State and assurance

| Property | Grade and evidence |
|---|---|
| A frame pop cannot delete an outer binder's facts | **Structural**: a frame owns its ordered slots and pop removes that frame only. The `ScopeChain` matrix is armed against the former delete-by-name pop. |
| Same-name binders retain separate cleanup obligations | **Structural**: release collection enumerates slots and carries each slot's variable and type directly. |
| Fresh `Variable` construction enters through bind sites | **Structural**: the allocator is private; `bind_local` and `bind_capture` are its only construction paths. |
| A repeated initializer observes the preceding bind's type | **Measured (M2)**: the module seam compares the repeated-name program with its one-name rename control and a scalar negative cell. Its recorded post-implementation fault plant fired but is not re-executable without adding a production seam. |
| Positional lenient state displaces an earlier rebinding | **Structural**: admission state is indexed by binding position and queried through the before-position resolver. |
| Par continuation capture of a consuming heap value | **Measured**: `tests/par_cont_capture_consuming_use.rs` permanently guards the accepted codegen change in both `--run` and `--link`; its old-RED/new-GREEN and controls prove the retained capture reference. |
| Tail transfer releases a displaced same-name heap binder | **Measured**: `same_name_tail_transfer_releases_the_displaced_binding` and `tail_transfer_releases_the_displaced_same_name_binder_run_and_link` are GREEN module and terminating runtime witnesses in both `--run` and `--link`. |

The six full compared frames and truncated lane windows are bounded evidence,
not a universal non-shadowing CLIF-identity claim. Par captures are an intended
codegen change, so their CLIF need not match a pre-capture baseline.

Capture-membership remains a conservative last-use-transfer veto. QA found no
available module witness for the inner continuation's decision: the current
probe exposes the enclosing definition's CLIF, while the continuation compiles
in another context. This is an observation limit, not a measured defect or a
hidden carry obligation; no observer or product seam is introduced here.

## Out of scope

No public-API or cache-schema decision is implied. This record does not alter
last-use policy, COW retention, frame-index arithmetic, capture-membership, or
the canonical drop-glue registry beyond the slot-based cleanup and approved
tail-transfer correction described above.

## References

- `design/backend/backend.md` §8 — backend design index.
- `design/backend/lenient-eval.md` — spark admission and dependent emission.
- `design/backend/ring2-rc.md` and `design/backend/transitive-drop-glue.md` —
  type-directed release and established TCO controls.
- `crates/cranelisp-backend/CLAUDE.md` — as-built backend seam guidance.
