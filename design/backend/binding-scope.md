# Binding scope — binder identity in the backend

> **Status**: Live. The S121 binder-slot repair is delivered. Ownership is keyed
> by the [uniform counting](uniform-counting.md) plan's binder identity, which
> the emitter maps to a slot here; verified against source on 2026-11-15.
> **Owner**: `design` (cranelisp-backend). **Surface**: backend interior only.
> **Authority**: `spec/04-expressions.md` §4.3 (sequential visibility,
> repeated names, shadowing), and `spec/12-runtime.md` §12.3.1 and §12.4.3
> (release of unreachable heap values and lenient-binding independence).

## Purpose and invariant

The backend identifies a binder by its slot, never by its spelling. A name is a
lexical-resolution query, not the key for a binder's value, type or release
obligation. Consequently, leaving a scope removes only that frame's slots, and
same-name binders in a binding vector keep separate obligations: the plan gives
each its own binder identity.

This is an interior correction only: it changes neither language semantics nor
any public facade, persisted schema, or cross-crate edge.

## Binding environment

`ScopeChain` is a stack of ordered frames. Each `BinderSlot` owns one binder's
Cranelift `Variable`, type, and name for resolution. The type is optional as
built; S124 makes it a `ConcreteType` for every slot and capture
([release contract](non-concrete-release-contract.md) §7.4 step 2). The latest
matching slot in the innermost applicable frame denotes a name. Leaving a scope
pops its frame and releases nothing; every binder was already dropped where it
died.

`CaptureEnv` is distinct from the chain. It is seeded once for an inner
compiler and is owned by the closure environment's drop glue, rather than by a
body frame. Resolution consults a live local slot before a capture, so a local
shadow does not overwrite its capture, and a use of a capture duplicates.

`bind_local` publishes a local's value and type together after its
initializer has compiled. A repeated binder's initializer therefore observes
the preceding binder's complete facts. `fresh_variable` is private and its only
construction paths are `bind_local` and `bind_capture`; slots consequently get
their `Variable` through that single mint boundary.

Per-binding-vector lenient state is positional. Spark admission and dependency
lookup ask which binder is denoted before a position, so a later rebinding
displaces an earlier spark record instead of colliding by name.

The obsolete per-binding closure-glue fields are absent: canonical,
type-directed release has no per-binding glue identifier to retain.

## State and assurance

| Property | Grade and evidence |
|---|---|
| A frame pop cannot delete an outer binder's facts | **Structural**: a frame owns its ordered slots and pop removes that frame only. The `ScopeChain` matrix is armed against the former delete-by-name pop. |
| Same-name binders keep separate release obligations | **Structural**: the plan introduces one binder identity per binding, and a drop names that identity, not a name. |
| Fresh `Variable` construction enters through bind sites | **Structural**: the allocator is private; `bind_local` and `bind_capture` are its only construction paths. |
| A repeated initializer observes the preceding bind's type | **Measured (M2)**: the module seam compares the repeated-name program with its one-name rename control and a scalar negative cell. Its recorded post-implementation fault plant fired but is not re-executable without adding a production seam. |
| Positional lenient state displaces an earlier rebinding | **Structural**: admission state is indexed by binding position and queried through the before-position resolver. |
| Par continuation capture of a consuming heap value | **Measured**: `tests/par_cont_capture_consuming_use.rs` permanently guards the accepted codegen change in both `--run` and `--link`; its old-RED/new-GREEN and controls prove the retained capture reference. |
| A displaced same-name heap binder is released before a tail jump | **Measured** end to end: `tail_transfer_releases_the_displaced_same_name_binder_run_and_link` in both `--run` and `--link`. Its module witness was deleted with the tail flushes; the plan's own cells carry the unit tier. |

The six full compared frames and truncated lane windows are bounded evidence,
not a universal non-shadowing CLIF-identity claim. Par captures are an intended
codegen change, so their CLIF need not match a pre-capture baseline.

## Out of scope

No public-API or cache-schema decision is implied. Counting policy is
[uniform counting](uniform-counting.md)'s; release discharge is the canonical
drop-glue registry's.

## References

- `design/backend/backend.md` §8 — backend design index.
- `design/backend/lenient-eval.md` — spark admission and dependent emission.
- `design/backend/uniform-counting.md` — the ownership plan that keys counting
  on binder identity.
- `design/backend/transitive-drop-glue.md` — type-directed release.
- `crates/cranelisp-backend/CLAUDE.md` — as-built backend seam guidance.
