---
number: 0907
target: /design (backend)
filed_by: /qa
filed_at: 2026-07-26
sprint_filed: 118
refers_to: crates/cranelisp-backend/src/drop_glue.rs:497-505 (ctor_shapes identity check);
  src/bootstrap.rs:767-783 (the seeded Bind ctor scheme);
  crates/cranelisp-intrinsics/src/drop.rs::free_io_branches (the live runtime IO-tree owner);
  design/backend/transitive-drop-glue.md §4.1; design/arch/fixmes/0903-*.md (sibling class);
  tests/plan/s118-test-plan.md §11 (attribution record)
status: open
---

# `IO`'s existential `Bind` ctor defeats canonical per-concrete glue derivation — every release of a concrete `IO T` value hard-refuses

## Severity

Important — 7 committed e2e cells RED (`spec_10_io` ×3, `ctor_as_value` ×2,
`examples` ×1 [two example programs: 21-hello-io, 23-io-sequence],
`stdlib_conformance` ×1 [core.io/when-io, taking `core` and `core.io` down]),
and the whole class of user programs with an IO-typed *binding or temporary*
(any IO combinator: `when-io`, `then`, `map-io`) refuses to compile.

## Minimal repro (one line, PrimitivesOnly prelude, verified at HEAD `49a20269`)

```
(match (Pure 5) [(Pure x) x (Effect e) 0])
→ Error: codegen failed for user/__expr: codegen error at 0..0:
  constructor 'Bind' disagrees on declared parameter identity for 'primitives/IO'
```

Scope-exit face, same signature:

```
(defn f [] (let [x (Pure 5)] 1))
```

Any release site of a concrete `IO T` value reproduces it — the match
temporary-scrutinee dec and the scope-exit dec both route through
`emit_typed_rc_dec` → `DropGlueRegistry::request_if_owning(IO(Int))`.

## Mechanism (attributed, read at source — two layers)

1. **The proximate error.** `drop_glue.rs::ctor_shapes` builds one shared
   substitution over ALL of a type's constructors and hard-errors when two
   ctors' result-type ADT args bind different `TypeId`s (`existing !=
   &ctor_subst`, :497-505). `Pure`/`Effect` are seeded through
   `register_synth_adt` sharing `Var(io_a)`; `Bind` is seeded MANUALLY
   (`src/bootstrap.rs:767-783`) with fresh `bind_a`/`bind_b` — an intentional
   existential encoding ("HM cannot express the existential, so Bind bypasses
   the normal ctor scheme path"). The identity precondition is therefore
   structurally unsatisfiable for `primitives/IO`; the check fires on the
   first concrete `IO T` glue request, always.

2. **The deeper fact — a per-ctor substitution does NOT fix it.** Even
   substituting each ctor's own result vars positionally, `Bind`'s field
   types (`inner: IO b`, `cont: Fn [b] (IO a)`) keep `Var(bind_b)` free:
   the existential `b` is not determined by `IO a`'s parameter, so
   per-concrete static glue for `IO T` cannot type Bind's fields from ctor
   shapes at all. This is a modelling gap, not an implementation slip.

## Why it surfaced at W3 (honest provenance)

The S116 registry had **zero consumers** until W3 (the D1 borrow-conflict
finding), so `ctor_shapes` was unreachable and these programs compiled —
IO-typed scope releases went through the legacy inline emitter, which did
not derive IO glue this way (silent shallow teardown, the leak direction).
W3's migration routed every typed release through the registry and turned
the silent-wrong into loud-refusal — D2's no-fallback discipline working as
designed on a type it cannot yet model. These 7 REDs are therefore
W3-surfaced (not in the sprint-open 28; proven not-W4's by stash/pop at the
W4 review). A revert is not the fix; a ruling is.

## Relation to FIXME 0903 — same class, third face

0903's two censused escapee families (synthetic accessors of
generic/undeclared-field products; generic trait-method instances) reach the
release machinery with *residual signature vars* and silently leak. The
IO/Bind face reaches it with an *existential ctor field* and loudly refuses.
One class: signature-driven, compiled-once artifacts whose field/parameter
types are not determined by the concrete type the release is keyed on. The
`/design`(backend) ruling 0903 already owes should co-rule this face — ruling
the accessor/trait families without IO leaves the loudest member unfixed.

## Candidate directions (for the ruling; none costed here)

- **Route IO to the runtime teardown owner.** `cranelisp-intrinsics` already
  owns dynamic, tag-directed IO-tree teardown (`drop.rs::free_io_branches`,
  three call sites, incl. the PAR branch walk); a closure field is already
  dynamically releasable via its embedded `DROP_GLUE_PTR`. The registry
  would classify `primitives/IO` as runtime-owned and emit a call to the
  intrinsic instead of deriving ctor shapes. Note `Pure`'s payload (`a`) is
  the one field that IS determined by the concrete arg — the ruling must say
  who discharges it and how the runtime knows its category.
- **Per-ctor substitution + dynamic escape hatch for existential fields** —
  relax the identity precondition to positional per-ctor mapping and give
  unresolvable fields a dynamic disposition (closure via embedded ptr; ADT
  fields would need information that does not exist without a header
  type-word, rejected R15). Likely unsound for the general case; recorded
  for completeness.
- **Special-case exclusion at admission** (`HeapCategory`/registry refuses
  to own IO; the S116-era behaviour) — restores compilation but restores the
  silent leak too; if taken it MUST land with a failing-not-ignored leak
  guard so the leak stays visible.

## Sequencing

`/qa` recommends the ruling ride the S119 0903 window (`/design`(backend),
with `/arch` adjacency: IO is seeded by int's bootstrap, torn down by
intrinsics, refused by backend — three contexts meet here). Until then the 7
cells are attributed carries; `tests/plan/s118-test-plan.md` §11 carries the
name-for-name list.
