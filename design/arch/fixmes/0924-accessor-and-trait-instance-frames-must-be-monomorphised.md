---
number: 0924
target: /design (typecheck)
filed_by: /design (backend)
filed_at: 2026-07-26
sprint_filed: 119
refers_to: design/backend/non-concrete-release-contract.md §4 faces 2+3, §4.3 (the
  impossibility proof), §5.2 (the obligation);
  crates/cranelisp-typecheck/src/adt.rs:136,241-245 (accessor synthesis — the
  0867 seam);
  the trait-method instance mangle (`Functor.fmap$primitives/Option`);
  design/arch/fixmes/0903-*.md families 1+2, 0916, 0867
status: open
---

# Synthetic accessors and generic trait-method instances must be monomorphised per instantiation — backend cannot release them, by any disposition

## Issue

`non-concrete-release-contract.md` (S119 Spine 1, `/design`(backend)) rules that
a frame whose parameter or result types are not fully concrete is **not a legal
codegen target** (R-3), and that the two families reaching backend that way are
a **producer** defect, not a backend handling gap.

Two families, measured exhaustively this window (§2.2/§2.3 of the ruling —
2,497 release admissions and 5,499 category licences censused across the full
suite):

- **F1 — synthetic field accessors** of a generic or undeclared-field product.
  Frame `Type.field`; `self : ADT(<concrete FQ>, [Var…])`; result often a bare
  `Var`. Measured frames: `Grid.cells` (×164), `Box.v`, `Box.val`, `Pair.first`,
  `Pair.second`, `Pair2.x`, `Pair2.y`, `Pz.v`, `Bx.val`, `Box.cells`,
  `Pair.fst`, `Pair.snd`.
- **F2 — generic trait-method instances.** Frame `Trait.method$Type`; parameters
  `Fn([Var…], Var)` or `ADT(<concrete FQ>, [Var…])`. Measured frames:
  `Functor.fmap$primitives/Option`, `$user/Box`, `$m/Option`,
  `$30-parallel-map-reduce/Pair`, `$26-functor/Option`.

**Severity is higher than the record states.** 0903 files F1 as a *silent leak*.
It is not: it is **memory-unsafe**, at exactly the same 1023/1024 boundary `/qa`
measured for F2 (0916). Four-line free-standing repro, `PrimitivesOnly`,
`--run --no-cache`:

```lisp
(import [primitives [IO Pure]])
(deftype (Bx a) [:a v])
(defn get [b] (v b))
(defn main [] (Pure (get (Bx 1024))))
```

`1023` → exit 255 (correct). `1024` → **SIGSEGV**. `5000` → **SIGSEGV**. The
accessor's CLIF loads the field (static type `Var(0)`), compares it against
`NULLARY_TAG_THRESHOLD`, and on the `>=` branch does `atomic_rmw add [field+8]` —
a wild atomic write, because the guard discriminates tags from pointers and not
scalars from pointers.

## Why this cannot be fixed in backend (the impossibility proof)

Reproduced from the ruling §4.3, because it is the reason this is filed on
typecheck rather than absorbed:

| In-frame policy | scalar payload | heap payload | duplicating arm (`(Pair x x)`) |
|---|---|---|---|
| count it (today) | wild atomic write → SIGSEGV | correct | correct |
| do not count it | correct | leak | **UAF** (two boxes, one count) |
| runtime-discover it | impossible — a raw scalar carries no header; R15 (header type-word) is rejected architecture | | |

Every column has a failing row and the failures are on different axes, so no
in-frame test separates them. The missing fact — the word's heap category —
exists only at the call site.

Refusing instead is measured and unlandable: the frame-keyed gate costs **+16
hard codegen refusals** over the `spec_*` corpus (893 run, 8 → 24 failed), the
same number S118 measured, re-run at S119 HEAD.

## Proposed resolution

Remove the compile-once-per-declaration exemption. Both families join the
monomorphisation the compiler **already performs** for ordinary generic `defn`s
— the census's own frame list carries `ct/ap$Fn(Int;ct/Bx$Int)+Int` next to
`Bx.v`. This is not a capability the compiler lacks; it is an existing
capability two frame kinds are exempted from.

1. **F1 — accessors.** `adt.rs` mints one accessor `Def` per declaration with
   `self : ADT(T, [Var…])`. Mint instead one per concrete instantiation actually
   demanded, under the existing monomorphic mangle, with `self` and the result
   substituted.
2. **F2 — trait-method instances.** The instance name is keyed on the type
   *constructor* (`$primitives/Option`). Widen the key to the full concrete
   instantiation (`$primitives/Option$Int`). This is a **key widening on an
   existing mangle**, structurally the same change as S110's alias-class close
   (`backend-keyed-consumer.md` §1.1.2) — not a new naming scheme and not a
   second identity home.
3. Neither is a `cranelisp-types` delta; neither changes an extern name or the
   ABI. Both change how many bodies are emitted and under what names.

## Sequencing consequences

- **This gates rider 0867.** 0867 widens accessor minting to every sum type and
  distinct-name product — i.e. it *widens F1's surface*. `SPRINT.md`
  §Must-not-interleave already gates 0867 behind the accessor disposition; this
  FIXME is that gate's content. Landing 0867 first manufactures new members of a
  memory-unsafe class.
- **This gates 0916 ×1.** The ruling's staging table (§7) makes 0916
  producer-gated: 10 of the 11 Spine-1 REDs (0917×3 + 0907×7) close with
  backend-only changes; 0916 does not close without this obligation.
- **The backend-side flip is census-gated, not review-gated.** Backend keeps its
  fabricating arm (`signature_heap_category`'s `Err ⇒ Mixed`) instrumented until
  the measured licence count for each family reads **zero** across the corpus,
  and only then converts it to a located error (ruling §5.1). So this FIXME's
  landing is observable from backend's own instrument.

## Related, same rule at a different altitude

FIXME 0913 (the lenient view's fabricated `ConcreteType::Int`) is the same rule
one level down — *do not hand codegen a type you have not got*. Its obligation is
specified at `non-concrete-release-contract.md` §5.4 and is the other half of
`/design`(typecheck)'s Round-2 window.
