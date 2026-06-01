---
number: 0244
target: /arch
filed_by: /sprint
filed_at: 2026-05-31
sprint_filed: 73
refers_to: design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md §"Shape"/§Consequences/§Rationale(A1b), design/arch/facades/primitives.md §"Type shape"/§"Static-init contract"/§"Bounded-context invariants"(6), crates/cranelisp-backend/src/code.rs (Code::Primitive variant + tests), crates/cranelisp-primitives/src/lib.rs:152/192/338-348, src/CLAUDE.md §"JIT Symbol Names"
status: open
---

# Revert Decision 0048 A2 — drop the `Code::Primitive` marker; derive primitive-ness from `DefKind::Primitive`

## Decision (user-arbitrated 2026-05-31, S73 Phase 1)

Decision 0048 A2 (S68 Phase 3, 2026-05-17) added a payload-less `Code::Primitive`
marker variant so that "process-static lifecycle" would be visible at every
`match` site over a `ModuleEntry::Def.code` field, rather than being encoded as
the absence of a `Code` value (`code: None`). **That reasoning is reversed.**
Primitives entries carry `code: None`; primitive-ness is read from the already-
canonical `kind: DefKind::Primitive { .. }`.

The user (who made the A2 call in S68) has reviewed substance + rationale +
alternatives and approved the reversal.

## Issue — the marker is redundant and never cashed out

`Code::Primitive` is referenced **functionally in exactly two non-test places**,
both trivial no-ops equivalent to `None`:

- `crates/cranelisp-backend/src/code.rs:106` — `Debug` arm prints
  `"Code::Primitive"`; `Option::<Code>::None` already Debug-prints `None`.
- `crates/cranelisp-backend/src/code.rs:151` — `ptr()` returns
  `std::ptr::null()`, i.e. "I carry no address; use the GOT." `None` says the
  same. (Decision 35: the GOT is the single source of truth for a primitive's
  address; nothing reads the primitive's address from `code`.)

Everything else referencing the variant is either (a) the two construction sites
in `cranelisp-primitives/src/lib.rs` (152, 192), (b) the primitives unit test
asserting the marker (338–348), or (c) a block of unit tests in `code.rs`
(237–305) **that exist solely to exercise the variant**.

Meanwhile `DefKind::Primitive` — the canonical "this symbol is a primitive" fact —
is already read in **34 places**. The marker duplicated that fact into the
lifecycle field; the A2 goal ("make the category visible at match sites over
`code`") never produced a single match site that does real work on it.

## Proposed resolution

1. **Delete the `Code::Primitive` variant** from the `Code` enum
   (`cranelisp-backend/src/code.rs`). The two functional arms (Debug, `ptr()`)
   fold into the existing `None`/null path — behavior-preserving, because any
   reader of a primitive's address already routes through the GOT per Decision 35.
2. **Primitives entries carry `code: None`** — the `ModuleEntry::def(..).build()`
   builder default (FIXME 0241 / 0242). No `.primitive()` setter, no `.code()`
   setter, no `CodeStore` constructor, no extension trait. The builder's
   deliberate "`code` is not settable; it is runtime-state written downstream"
   invariant is **vindicated**, not worked around — primitives stop being the
   one exception that bent it.
3. **Restore `code`'s single responsibility.** `code: Option<C>` is the per-entry
   *runtime resource handle*: `Some(Jit{..}/Linker{..})` when there is owned
   compiled code to retain/reclaim, `None` when there is not. "Is there code to
   reclaim?" → `code.is_some()`. "What kind of symbol is this?" → `kind`. The two
   fields stop overlapping; primitive-ness (a *kind* fact) is no longer smuggled
   into the *lifecycle* field.
4. **`code: None` is not ambiguous in practice.** It denotes either "primitive —
   never has code" or "user fn — not yet compiled"; `kind` (non-optional,
   authoritative) disambiguates, and the sites that care already hold `kind`.
5. **Delete** the dedicated `Code::Primitive` unit tests in `code.rs` (237–305);
   **rewrite** the primitives test `every_entry_carries_code_primitive_marker`
   (lib.rs:335–352) to assert `matches!(kind, DefKind::Primitive { .. })`.

## Alternatives considered (rejected this session)

- **(a) post-`build()` mutation in primitives** (`if let Def { code, .. } = &mut e
  { *code = Some(Code::Primitive) }`) — keeps the marker; preserves the field
  redundancy.
- **(b) a narrow `.primitive()` builder method** — either via a `CodeStore`
  marker-constructor (drops the blanket `impl<T> CodeStore for T`; 2 explicit
  impls; disturbs Decision 32; `Some(())` noise for pure-data tables) or an
  extension trait in `cranelisp-primitives`. Both keep the redundant marker.

(c) is strictly simpler than (a)/(b): it removes the variant rather than finding
a tidier way to set it.

## Manifestation sites (where /arch records the reversal)

Per the manifestation-site discipline (no separate Decision log; commitments live
at their natural home):

- **`design/arch/decisions/0048-...md`** — A2 is in the draining Decisions
  backlog. Strike/amend the A2 ruling and the §Consequences "`Code::Primitive`
  marker variant added" bullet; the §Rationale A1b ("`code: None`") position is
  now the accepted shape. Migrate the residual substance to the facade per the
  drain.
- **`design/arch/facades/primitives.md`** — §"Type shape", §"Static-init
  contract" item 1 (`code: Some(Code::Primitive)` → `code: None`), §"Bounded-
  context invariants" #6 (process-static lifecycle no longer references a marker
  variant), §Cross-references.
- **`crates/cranelisp-backend/src/code.rs`** rustdoc on the `Code` enum (the
  `Primitive` variant doc-comment and its narrative go).
- **`src/CLAUDE.md` §"JIT Symbol Names"** — if it cites the marker.

## Operational implication / sequencing

- This is the construction-design ratification for the S73 primitives work
  (builder adoption + `code: None`). It pairs with FIXME 0242 (int's mount uses
  `ModuleEntry::def`) and the broader primitives facade-alignment.
- Backend dep is unchanged: primitives still names `Code` as the *type* parameter
  on `SymbolTable<Code, ()>` (it just never constructs a `Code` value), so the
  `cranelisp-primitives → cranelisp-backend` edge and the build-order spine
  (backend green → primitives green → int mount) are untouched.
- Source edits (delete variant, update construction, tests) are Phase 5
  `/dev backend` + `/dev primitives` work, gated on the backend cascade reaching
  green so primitives compiles.
