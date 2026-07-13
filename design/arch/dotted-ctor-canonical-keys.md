# Dotted-ctor canonical keys — the types-side contract for the S109 Phase-5 registration change

**Status: WORKING (S109 Phase 3, `/arch`).** The binding spec for the two
`cranelisp-types`-adjacent obligations that are **coupled to the Phase-5
typecheck registration change** (SPRINT.md bucket 2 — the field
inverted-model mirror) and therefore did NOT land with the Phase-3 `/arch`
change-set. **Archive trigger:** the Phase-5 dotted-ctor wave lands (both
items below in the SAME change-set as the `adt.rs` registration keying
change); the surviving contract folds into the `type_ctor_names` rustdoc +
BC §7, and this file moves to `design/arch/archive/`.

What DID land in Phase 3 (S109 `/arch` change-set, for context):

- `cranelisp_types::member_key(&TypeName, &str) -> Symbol` — the ONE mint
  point for the canonical dotted `Type.member` key (`resolve.rs`;
  `interfaces.md` §"Resolution primitive" S109 amendments).
- `ModuleEntry::type_def_info() -> Option<&TypeDefInfo>` — the single
  "answers as a type" reader over the S79 dual facet (`module.rs`; BC §7).
- The FIXME-0567 prelude head-visibility fix (unrelated to keying; recorded
  in `prelude-import-convergence.md` §3.5.2).

## 1. The mechanism being landed in Phase 5 (context, arch-ruled Phase 2)

Registration (`cranelisp-typecheck/src/adt.rs`) mints the canonical
`Type.Ctor` key — via `member_key` — as the REAL got-slotted constructor
`Def` in the type's home module; the bare ctor name becomes a convenience
ALIAS entry, poisoned to `ModuleEntry::Ambiguous` on §8.6.5
distinct-terminal collision — exactly the existing field-accessor machinery
(`Box.v` canonical / bare `v` alias). The dotted resolver then probes the
canonical key for ctors exactly as it does for fields — one
member-resolution codepath. Product dual-facet corner: a product ctor
(type-name == ctor-name, `type_def: Some(..)`) keeps its SINGLE key at the
type name; the canonical dotted form is degenerate (`/design` typecheck
settles the exact treatment).

## 2. Obligation A — `type_ctor_names` walks to canonical keys

`cranelisp_types::type_ctor_names` (`crates/cranelisp-types/src/heap.rs:269`)
is the ONE `TypeDef`-vs-product-facet ctor-name reader (FIXME 0528 mirror
cure). Its three consumers all use the returned `Vec<Symbol>` as **storage
keys** — `table.get(name)` — to reach each ctor's `DefKind::Constructor`
`Def`:

- `value_layout` → `ctor_field_concrete_types` (`cranelisp-types/src/heap.rs:212/296`),
- backend `is_mixed_adt` (`cranelisp-backend/src/heap.rs:665` → `ctor_field_count`),
- backend `classify_adt` → `classify_from_ctor_names` (`cranelisp-backend/src/heap.rs:857`).

Today those keys are the bare ctor names because registration stores the
real ctor `Def`s under bare keys. After the Phase-5 keying change the bare
key holds an ALIAS — possibly `Ambiguous`-poisoned — and a bare-key probe
would land on the alias (or the poison) instead of the real `Def`,
breaking `value_layout` (soundness-coupled: typecheck `Copy` classifier and
backend `HeapCategory::Value` both delegate) and the heap classifiers.

**Ruling (contract, `/arch`):** `type_ctor_names` returns **the storage
keys of the ctor `Def`s**, not display names. Concretely, in the same
change-set as the registration keying change:

- `ModuleEntry::TypeDef { info, .. }` arm: return
  `info.constructors.iter().map(|c| member_key(&fqtn.name, c)).collect()`
  (`TypeDefInfo.constructors` itself continues to carry bare ctor names —
  the display/identity list; the mapping to storage keys happens HERE, in
  the one reader, never per consumer).
- Product-facet arm (`DefKind::Constructor { type_def: Some(td), .. }`):
  return the surviving single key — the type name itself (per the §1
  product corner; i.e. `vec![Symbol::from(fqtn.name.as_ref())]`), matching
  wherever `/design` settles the degenerate product key.
- **No signature change** (`&SymbolTable, &FQTypeName -> Option<Vec<Symbol>>`
  stays); consumers keep probing `table.get(returned)` unchanged. Any
  consumer that wants a ctor's *display* name reads it off the resolved
  `Def`'s own metadata, not off this list.
- Sequencing: this arm-level change MUST land in the SAME change-set as
  the `adt.rs` keying change — landing either side alone breaks the
  `get(returned)` round-trip (Principle 8: no interim state where reader
  and writer disagree on the key grammar).

The `member_key` sweep rides the same wave: `adt.rs:599` (accessor
registration), `checker.rs:1434` (canonical-key probe), the new ctor
registration site, and opportunistically the `infer.rs:235` diagnostic
hint all call `member_key` instead of hand-rolled `format!("{}.{}", ..)`.

## 3. Obligation B — `CACHE_SCHEMA_VERSION` bump (16 → 17)

The serde shape of `SymbolTable`/`ModuleEntry` does not change, but the
**meaning of the key under which a ctor `Def` is stored** does — a
`.meta.json` content-meaning change, which per the cache contract
(`crates/cranelisp-types/CLAUDE.md` §"The serde shape IS the cache
contract") bumps `CACHE_SCHEMA_VERSION` in
`crates/cranelisp-backend/src/cache/mod.rs` (currently 16) in the SAME
change-set. Rationale: a cached pre-change module carries its ctor `Def`s
under bare keys; the post-change resolver and `type_ctor_names` probe
canonical `Type.Ctor` keys and would silently miss (unresolvable ctors,
mis-classified heap categories) — exactly the silent-skew class the bump
exists for. Owner: the Phase-5 typecheck/registration change-set (the
constant lives in backend; the bump is part of that change-set's
definition of done, NOT a follow-up).

## 4. Phase-5 delegation reminders (read-side, decoupled — may land in any order)

- typecheck `type_def_view_of` (`checker.rs:91`) reduces to
  `entry.type_def_info()` (delete the local match body; keep the wrapper or
  inline at call sites — `/dev` typecheck's call).
- int `save.rs:696 generate_types` keys on `entry.type_def_info().is_some()`
  instead of matching `ModuleEntry::TypeDef` — the 0573 fix (sum types
  still emit once: their ctor `Def`s have `type_def: None`).
- Stale comment sweep: `src/repl.rs:728` still says "head filter is the
  separate FIXME 0567" — 0567 is fixed (S109 P3); reword when touching
  that file.
