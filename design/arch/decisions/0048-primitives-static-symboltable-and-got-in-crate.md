---
number: 0048
title: Primitives own a statically constructed symbol table and GOT and dispatch like any other module; primitives and backend do not depend on each other
status: operative
---

# 0048 — Primitives' symbol table and GOT are statically constructed in the primitives crate

This record is a citation anchor, not an authority. The current contract is
the [primitives context](../bounded-contexts.md#4a-primitives-cratescranelisp-primitives)
(the boundary statement and invariants 2, 3, 5 and 6), the
[intrinsics context](../bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics)
(invariants 9 and 11) and the crate-root rustdoc of
`crates/cranelisp-primitives/src/lib.rs`. The section headings below keep the
identities that tests and source cite.

## Shape

- The primitives crate publishes one static, `PRIMITIVES_TABLE`: a symbol table
  in the unit code-store flavour, built once per process, whose GOT holds the
  address of every slot-dispatched primitive.
- Primitives never names backend's `Code`. The binary concretises the table to
  the session flavour at the session mount and on cache restore through the
  types-owned `into_concrete` bridge, which carries the one shared GOT through.
  The process therefore has exactly one primitives GOT, however many sessions
  exist.
- Every primitive entry has no code handle. `code` means an owned, reclaimable
  compiled resource, and a primitive owns none: the static is the owner.
  Primitive-ness is a fact of the entry's kind and origin, never of `code`.
- The GOT slot is the only home of a primitive's callable address.

## The invariant

From session start, primitive dispatch is the ordinary cross-module sequence:
emitted code loads the slot from the `primitives` module's GOT symbol and calls
it. Backend's symbol resolution has no primitives branch. Direct JIT symbol
registration is reserved for intrinsics, which are not a module. That asymmetry
is deliberate and is the categorical line between the two runtime crates.

## Structural invariant — backend dep-ban

`cranelisp-primitives` and `cranelisp-backend` do not depend on each other, in
either direction, under `[dependencies]` or `[dev-dependencies]`.

- Backend has no Rust-path visibility into a primitive's extern function, so it
  cannot emit a direct call to one. The GOT-dispatch rule is a property of the
  workspace graph, not of emitted code
  ([Principle 18](../principles/18-enforce-invariants-structurally.md), for
  which this is the worked example).
- The reverse edge went when primitives stopped naming `Code` (S73). Session
  type uniformity is achieved at the binary's mount, not at the primitives
  build.
- The manifests are the contract. The fence is
  `crates/cranelisp-backend/tests/no_primitives_dep.rs`, which parses backend's
  manifest, with a source-side companion in `tests/s68_primitives_uniform.rs`.
- A behavioural fence — inspecting emitted CLIF for a direct call to a
  primitive — was considered and rejected: it checks one compilation path,
  where the dependency ban forecloses every path.

## Consequences

- `ring0_jit_symbols()` is retired, and backend's intrinsic symbol enumeration
  names no primitive.
- The primitives crate's published Rust surface is the one static.
- Extern wrappers survive `--link` dead-code elimination through their export
  names, the startup force of the static, and the table initialiser taking
  every wrapper's address. `#[used]` is not the mechanism. The crate-root
  rustdoc section "Link survival" is the authority.
- Primitives are process-static: never cached, never reclaimed, and outside the
  per-batch JIT reclaim rule. The cache carve-out is recorded in
  `design/backend/module-caching.md`.
- `not` is a primitive.

## Cascade

The executable bundle no longer force-links primitives through `pub use`
re-exports. Its startup stub calls `cranelisp_init_primitives()`
unconditionally before user code, which forces `PRIMITIVES_TABLE` and so
populates the link-time primitives GOT. The authority is the crate-root rustdoc
of `crates/cranelisp-exe-bundle/src/lib.rs`. The original section also listed
the documents the ruling touched; that propagation is complete.

## Rejected alternatives

Each was argued and must not return without a new ruling:

- **A per-batch primitives table and GOT**, lifecycle-aligned with user
  modules. The addresses are stable for the process; rebuilding them per batch
  repeats identical work
  ([Principle 07](../principles/07-single-source-of-truth.md)).
- **A third "static GOT" category.** A GOT in static memory is operationally
  the ordinary per-module GOT; a new category would reintroduce the
  primitives branch in symbol resolution that this ruling removes.
- **A payload-bearing extern variant of `Code`.** It would either duplicate the
  GOT's address or wrap only a name.
- **A `Code::Primitive` marker variant.** Adopted 2026-05-17 and reversed
  2026-05-31 by the user: it copied a kind fact into the lifecycle field, no
  match site did real work on it, and it was the only reason primitives
  depended on backend. `tests/s68_primitives_uniform.rs` guards its absence.

## Retirement

One item awaits extraction before this record deletes: the four rejected
alternatives have no other home, and belong as a short rationale note in the
primitives context. The rest is already in the homes named at the top.

| Citation | Repoint to |
|---|---|
| `tests/spec_appendix_a_builtins.rs`, two `// spec:` blocks citing "The invariant" | primitives context invariant 3 |
| `tests/s68_primitives_uniform.rs`: "The invariant" (one block) | primitives context invariant 3 |
| `tests/s68_primitives_uniform.rs`: "Shape" (three blocks, plus the module header and one assertion message) | primitives context boundary statement and invariant 6 |
| `tests/s68_primitives_uniform.rs`: "Consequences" (one block) | primitives context invariant 3 |
| `tests/s68_primitives_uniform.rs`: "Cascade" (one block, plus two assertion messages) | the executable-bundle crate-root rustdoc |
| `tests/s68_primitives_uniform.rs`: the dep-ban section (one block, plus two assertion messages) | primitives context invariant 3 and Principle 18 |
| `crates/cranelisp-backend/tests/no_primitives_dep.rs`: module header, `// spec:` block and assertion message | primitives context invariant 3 and Principle 18 |
| `crates/cranelisp-backend/Cargo.toml` comment; `crates/cranelisp-backend/src/compiler/apply.rs` comment | primitives context invariant 3 |
| `crates/cranelisp-exe-bundle/src/lib.rs` (crate rustdoc, hook rustdoc and one comment); `crates/cranelisp-exe-bundle/CLAUDE.md` | drop the citation; that rustdoc is itself the authority |
| `design/intrinsics/intrinsics-table.md` cross-reference | intrinsics context invariant 9 |
| [Principles index](../principles.md) entry 18 and the Principle 18 body | primitives context invariant 3 |
| [Label index](README.md) row 48 | the primitives context link alone |
