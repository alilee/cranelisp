# Per-module GOT

> **Owner**: `design` (backend). **Status**: implemented; this is the standing
> record of the emitted shape and of *why* it is that shape.
>
> Authoritative on Decision 23's two-GOT model as the backend emits it. The
> boundary statement is `design/arch/bounded-contexts.md` §3 invariant 6; the
> per-module GOT table itself (`GotTable`, slot bounds, atomic slots) belongs to
> `cranelisp-types`. Read alongside `compile-to-module.md` §5.

## 1. The constraint: ADRP cannot reach a heap-allocated table

On aarch64, a PIC `global_value(DataId)` lowers to ADRP+LDR with ±4GB of reach.
A live GOT table is heap-allocated and may sit further than that from loaded
object code, so codegen cannot address the table directly. Everything below
follows from working around that, which is why the shape looks indirect.

## 2. The emitted shape — one load, two resolvers

**The symbol `__cranelisp_got_{M}` IS the slab base.** Not a pointer cell
holding the base; the address of the symbol is the address of the slab. That
collapses what was once a two-load sequence into one, and — because both modes
resolve the *same* data-symbol reference — it is what makes the CLIF
mode-agnostic.

The call sequence at every GOT-indirect site:

```
slab_base = global_value(__cranelisp_got_{M})   # the slab's address
slot_addr = slab_base + slot * 8
fn_ptr    = load(slot_addr)
call_indirect(fn_ptr)
```

On aarch64 that is ADRP+LDR (materialising the slab address through the
system's own GOT-load relocation) + LDR (the slot) + BLR. The backend emits
this identically in both modes; it does not know which `Module` impl will
resolve the symbol.

| Mode | Resolver |
|---|---|
| JIT | The symbol is registered with the JIT builder at the module's live `got().base_ptr()`, so the `Linkage::Import` data reference resolves straight to the slab. |
| Object | `CodeFinalizer::define_module_got_data` defines the symbol as `Linkage::Export` data of `slot_count * 8` bytes with function-address relocation initialisers at offset `slot * 8`. The system linker (`--link`) or the in-process cache `Linker` materialises them at load. |

Decision 36's bare names make the object-mode initialisers safe: they point at
intra-`.o` `Linkage::Local` function symbols, which cannot collide across
objects.

**Object mode must use regular `__DATA`, never `__bss`.** macOS `ld` segfaults
on a `.o` carrying relocations in an `S_ZEROFILL` section — BSS has no file
content for the linker to patch, so the bytes must land in `__DATA,__data`.
Define the symbol with explicit zero bytes; a zero-init definition produces the
wrong section affinity. This is a live trap, not history: the failure is a
linker crash, not a diagnosable error.

## 3. Mutability

- **The slab is immovable.** Its base is fixed once — at module build in JIT
  mode, at load in object mode — because finalized machine code has baked the
  address. Movement would dangle it.
- **Slot contents are mutable.** Slots are atomic pointers, swapped on REPL
  redefinition so every existing caller picks up the new target through the same
  indirection. This is what buys redefinition of object-loaded functions.
- Only contents mutate. Nothing rewrites the slab's address.

## 4. Consequences worth knowing

- A cached or linked function is still redefinable, because callers reach it
  through the slot rather than a relocation against its symbol.
- An AOT release mode can fold the base materialisation away when the slab base
  is a link-time constant, reducing dispatch to one absolute-address load. Not
  done, and not scheduled.
- Parallel codegen needs no coordination: slot *indices* are assigned before any
  codegen runs, so workers only write disjoint contents.

## Cross-references

- `design/arch/bounded-contexts.md` §3 invariant 6 — the boundary statement
- `compile-to-module.md` §5 — where the data symbol is declared and emitted
- `jit-object-convergence.md` §1 — the convergence invariant this shape serves
- `module-caching.md` — slab re-establishment on cache-hit
