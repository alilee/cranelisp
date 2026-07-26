---
number: 0923
target: /arch
filed_by: /design (backend)
filed_at: 2026-07-26
sprint_filed: 119
refers_to: design/backend/non-concrete-release-contract.md §4.4 + §5.3 (the ruling);
  crates/cranelisp-intrinsics/src/drop.rs::consume_io_tree (:338-460) and
  ::free_io_branches (:505, call sites :419/:467/:620);
  crates/cranelisp-backend/src/drop_glue.rs:497-505 (the refusal being retired);
  src/bootstrap.rs:767-783 (the manual Bind seed);
  design/arch/fixmes/0907-*.md (the 7 REDs this unblocks)
status: open
---

# The IO tri-context seam needs one `cranelisp-intrinsics` entry point — the tag-walk without the dec

## Issue

`non-concrete-release-contract.md` §4 assigns the IO existential `Bind` face the
**runtime-directed teardown** disposition: backend's drop-glue registry stops
deriving `ctor_shapes` for `primitives/IO` (which is structurally unsatisfiable —
`Bind` is seeded with fresh existential vars at `src/bootstrap.rs:767-783`, so no
per-ctor substitution can type its fields) and instead calls the tag-directed
walker `cranelisp-intrinsics` already owns.

That requires one thing intrinsics does not currently expose. `consume_io_tree`
does **dec → last-ref test → fence → tag-walk → dealloc** in one body. Backend
must interpose between the last-ref test and the tag-walk, because `Pure`'s
payload is the one field whose type IS determined by the concrete `IO T` and
which the runtime deliberately treats as opaque
(`drop.rs:340-344,395-399` — "the trampoline returns the payload's ownership to
the caller"). Backend alone can name `T`; the runtime alone can walk the tags.

## Proposed resolution

Split the existing body; do not add a mechanism.

```
// unchanged in behaviour, re-expressed over the new half:
consume_io_tree(ptr) == { if !last_ref(dec(ptr)) { return } ; fence ; free_io_node(ptr) }

// NEW public entry point — the tail half:
free_io_node(ptr)   // tag-walk (incl. free_io_branches for PAR/SELECT,
                    // consume_closure for Bind's continuation) + dealloc.
                    // NO dec, NO fence.
                    // Precondition: caller has dec'd to zero and fenced.
```

Backend then emits, for `ADT(primitives/IO, [T])`:

```
drop<IO T>(p):
    if p < NULLARY_TAG_THRESHOLD: return
    old = atomic_rmw sub [p+8], 1
    if old != 1: return
    fence
    if load(p, TAG_OFFSET) == IO_TAG_PURE: drop<T>(load(p, FIELDS_START))
    call runtime/free_io_node(p)
```

`drop<T>` is the ordinary canonical glue — **no IO-specific payload releaser is
minted**, so the ruling adds no second glue identity home.

## What `/arch` is asked to rule

1. **The public-API delta.** `cranelisp-intrinsics` gains one `pub fn` plus one
   `#[export_name]` C-ABI shim (backend emits a `Linkage::Import` call, and the
   symbol must resolve in `--link` as well as JIT). This is a `public-api.txt`
   change and a new extern name; `SPRINT.md` §Risk routes any new extern back to
   `/arch`. No `cranelisp-types` delta.
2. **The tri-context seam.** IO is seeded by int (`bootstrap.rs`), torn down by
   intrinsics, and refused by backend. This FIXME moves the teardown authority
   wholly to intrinsics and leaves backend contributing exactly one statically
   known field. Confirm that split is the one `/arch` wants before `/dev` builds
   to it.
3. **The named residual.** A `Pure` node nested inside an *unrun* `Bind`
   sub-tree has payload type `b` — the existential — which neither side can
   name, so its payload is not discharged. This is a bounded leak on unrun IO
   trees, strictly better than today's hard refusal, and `/qa` owes it a
   failing-not-ignored guard rather than silence
   (`non-concrete-release-contract.md` §7.1). Confirm the residual is
   acceptable-with-a-guard rather than blocking.

## Also owed by `/arch` from the same ruling (separable)

Two new rows for `design/arch/safety-invariants.md` §4, both measured this
sprint and both currently unrepresented in the register:

- **R-1 — category before operation.** No RC operation may be emitted on a word
  whose heap category codegen cannot name from its own static type. Status:
  *unasserted* today; the violating seam is
  `cranelisp-backend/src/compiler/rc_emission.rs:493`
  (`Err(_) => HeapCategory::Mixed`), measured at 3,646 bare-`Var` licences
  across the suite, with two reproduced SIGSEGVs.
- **R-2 — no fabricated concreteness.** No component may present a downstream
  gate with a type/category/shape more concrete than what it knows in order to
  pass that gate. Three measured instances in two crates
  (`non-concrete-release-contract.md` §3.2). This is Principle 25 applied to the
  type channel.

## Context

- Unblocks the 7 `0907` REDs (`spec_10_io` ×3, `ctor_as_value` ×2, `examples` ×1
  covering two example programs, `stdlib_conformance` ×1 covering the two named
  modules `core.io` and its parent `core`).
- `/stdlib` proved there is **no legal re-spelling** of the affected combinators
  and `/examples` proved the one spelling that compiles — the
  `(impl (Functor IO))` trait instance — is the leak, not a workaround
  (~68 bytes/call, linear to 82.7 MB at 800k iterations). 0907's third candidate
  direction (admission exclusion) restores that silent leak and is **rejected**
  by the ruling under R-2.
- `/repl`'s appendix item 5: `Bind` is seeded manually and is not enrolled the
  way `Pure`/`Effect` are, so a diagnostic naming `Bind` is followed by the REPL
  denying it exists. Whatever the fix does to that seed must leave `Bind`
  introspectable — `non-concrete-release-contract.md` §5.3 makes it an
  obligation because R-4 requires a refusal's nouns to be lookup-able.
