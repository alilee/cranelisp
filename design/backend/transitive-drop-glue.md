# Transitive drop glue and owned-value displacement

**Status:** DESIGN — authored S116 Phase 3; **refreshed S118 Phase 3** to
implementation-ready state for the Track B consumer migration.
**Subordinate to:** `backend.md`.
**Architecture inputs:** `design/arch/safety-invariants.md` R15;
`design/arch/bounded-contexts.md` §4b invariant 16; S116 arch rulings 1, 2, 7,
8, 9 (`sprints/archive/sprint-116.md`); **S118 arch rulings 9 and 10**
(`sprints/SPRINT.md`) — ruling 10 makes the atomic legacy-emitter deletion
architecturally binding, not capacity policy.
**QA contract:** `tests/plan/s118-test-plan.md` §4 (carried S116 matrix, the
ruling-10 structural fence §4.3, armed-detector acceptance legs §4.1, verified
consequents §4.4).

This document resolved the backend design obligations in FIXMEs 0760 and 0796
(both closed by this refresh — §7.4 carries their acceptance forward) and
supplies the common mechanism the 0835/0810/0782 and 0688 implementation waves
consume. The defect records are the committed failing tests, not FIXME files.

---

## 0. What this refresh changes

S116 Wave 3 landed the **foundation** (`crates/cranelisp-backend/src/drop_glue.rs`
— the declaration-first `Declared | Defining | Defined` registry, exported
per-concrete bodies, `CompilationArtifacts.drop_glues`) and `/review` PASSed it.
Waves 4–5 (consumer migration) never ran. At HEAD the canonical registry has
**zero consumers**: it is requested only for result roots in
`lib.rs:672–700`, and every ordinary release site still runs the legacy inline
recursive emitter with `MAX_DROP_GLUE_DEPTH = 4` (`compiler/rc_emission.rs:492`).

| Concern | S116 design said | HEAD is | S118 does |
|---|---|---|---|
| Registry shape | "module-compilation-owned registry … shared by ordinary function lowering and all compiler-synthesised environments" (§3.1) | `DropGlueRegistry<'a, M, …>` holds `&'a mut M` and is `finish()`ed **before** body compilation | §3.4 D1 — reshape to a module-borrow-free state object, threaded through body compilation |
| Release seams | one glue-call emitter (§4) | four independent glue mechanisms (§1.1) | §7 slices S1/S3/S4/S5 |
| Depth bound | removed, not raised (§1) | live, explicitly transitional | §8 — atomic deletion, ruling 10 |
| Match lifetimes | per-arm plan (§5) | whole-match `any`-arm approximation + a double-release under var patterns | §5 + §7.3 |
| TCO predicate | one pure predicate (§6) | three uncoordinated fragments | §6 + §7.5 |
| Consumer census | 0835, 0810, 0760/0796, 0688 | plus `apply::emit_post_call_decs`, plus the second named-ADT-glue identity home in `vec_codegen` | §1.1, §7 |

Sections 1–6 are the S116 contract, refreshed against HEAD and re-verified.
Sections 7–10 are new: the migration slices, the atomic deletion condition, the
acceptance mapping, and the refreshed unit matrix.

---

## 1. Binding outcome

Backend emits one **named drop function for each concrete owning type** and every
generated-code release site calls that function. The function has the semantic
shape `drop<T>(owned_word)`: decrement the outer value; only on the final
reference, recursively release each field owned by the value and then deallocate
the outer storage. Scalar/value-layout types need no glue. `String`, `Fn`, `Vec`
and concrete ADTs use the same call contract even where their bodies delegate to
an existing layout-specific operation.

This replaces recursive inline expansion. `MAX_DROP_GLUE_DEPTH`,
`drop_glue_depth`, and the shallow-dec fallback are removed, not raised or
renamed. A release site may not retain an inline, borrowed-builder, or
TCO-specific deep-release implementation. This is the end state required by
**No interim implementations of later-ring capabilities** and gives one owner to
the behavior under **Single source of truth**.

The universal heap header remains two words (S116 ruling 2). Glue identity comes
from the static concrete type; no type id or function pointer is added to
ordinary allocations. Closure boxes retain their existing embedded capture-glue
pointer because the capture tuple is closure-instance shape rather than a
language type carried in the header.

### 1.1 The mechanism census at HEAD — what "one owner" has to absorb

The migration is not "registry replaces inline emitter". Five mechanisms mint or
perform deep release today; the ruling names one survivor plus two retained
runtime dispatches.

| # | Mechanism | Home | Identity | Disposition |
|---|---|---|---|---|
| M1 | Canonical registry | `drop_glue.rs` | `cranelisp_types::drop_glue_symbol_name(module, ConcreteType)`, `Linkage::Export` | **the survivor** |
| M2 | Inline recursive emitter | `rc_emission.rs:116/210/270/476` (`emit_inline_drop_glue`, `emit_drop_glue_field_decs`, `emit_field_decs`, `emit_rc_dec_with_inline_drop_glue`) | none — emitted per site, depth-bounded | **DELETE (§8)** |
| M3 | Named per-instantiation ADT glue + Vec element dec | `vec_codegen.rs:1137/1054` (`build_adt_drop_glue_fn`, `build_elem_dec_fn`), named by `resolution::adt_drop_glue_name` / `adt_instantiation_mangle`, `Linkage::Local` | a **second** identity home for the same concept | **DELETE (§8)** — M1's `define_vec_elem_adapter` (`drop_glue.rs:170`) already supplies the `vec_drop` callback ABI over canonical glue |
| M4 | Capture drop-glue envelope | `lambda.rs:245` (`emit_capture_dec_glue`) + `capture_rc.rs::CaptureRelease` | span + mono discriminator | **SURVIVES as the capture-LAYOUT owner**; its per-slot release becomes an M1 call (§7.4) |
| M5 | Closure box embedded `DROP_GLUE_PTR` dispatch | `rc_emission.rs:31` (`emit_closure_dec_into`) | runtime-carried pointer | **SURVIVES** — §1's explicit exception; M1's `GlueShape::Closure` arm should call it rather than re-implement it (§3.4 D8) |

M3 is the same class as M2, not a lesser one: it is a per-INSTANTIATION compiled
artifact under a backend-local mangle that is not the types-owned identity — the
`drop-glue-underkey` class (FIXME 0633) with a second key scheme. Leaving it
alive after the migration would satisfy QA's fence text while breaking
**Single source of truth** and re-opening the identity question ruling 9 closed.
`/review` rejects a wave that deletes M2 and keeps M3.

---

## 2. Actors and lifetime events

| Actor / event | Value before event | Owner after event | Required action |
|---|---|---|---|
| lexical/scope cleanup, post-call cleanup | owned typed word | none | call `drop<T>` once |
| closure/curry/poll-state capture teardown | owned capture slot | none | generated environment glue calls `drop<T>` for every owning capture |
| constructor-pattern match on owned temporary | wrapper owns its fields | arm bindings borrow fields unless explicitly protected/transferred | after the arm's last use, call wrapper `drop<T>` once; protect each escaping field before that call |
| var-pattern match on owned temporary | binding aliases the whole value | binding/body or none | transfer the one owner when forwarded; otherwise call `drop<T>` **exactly once** after the arm |
| TCO loop-slot replacement | old parameter slot owns `T` | next slot value or none | one replacement/transfer predicate decides; if replaced, call `drop<T>` before overwrite |
| Vec element teardown | Vec owns each live element | none | Vec body iterates runtime length and calls element `drop<E>` |
| ADT teardown | box owns fields selected by runtime tag | none | ADT body branches on tag and calls each field's glue |

The match rule deliberately separates *field survival* from *wrapper release*.
Extraction is borrowing by default. If an arm result or tail argument carries an
extracted heap field beyond the match, backend emits the existing protective
increment/transfer before wrapper teardown; only then may wrapper glue discharge
its field reference. Inline and let-bound scrutinees use this identical lifetime
plan. This cures both 0810 polarities (leak and premature free) and 0782's
double-release without choosing one hazard over the other.

---

## 3. Identity, construction, and recursion

### 3.1 Canonical identity

The registry key is `ConcreteType`, including fully-qualified ADT identity and
all concrete arguments. The cross-crate symbol authority is exactly
`cranelisp_types::drop_glue_symbol_name(&ModuleFullPath, &ConcreteType) ->
LinkerSymbol`. Its encoding is injective over the complete concrete type and
module-qualified as an emission namespace: two module objects that both need
`String` glue export distinct symbols, while repeated requests for the same type
inside one module return the same declaration. Span, call site, source spelling,
traversal depth, requesting function, and process address are not identity
inputs. Backend does not mirror this grammar.

A module-compilation-owned registry maps concrete type key to
`Declared | Defining | Defined` plus `FuncId`. It is shared by ordinary function
lowering and all compiler-synthesised environments in that `Module` instance.
The registry, not a per-`FnCompiler` cache, is the sole construction authority.
This keeps closure, curry, Vec-element, match and TCO callers coherent.

### 3.2 Finite construction for recursive types

Construction is declaration-first:

1. Canonicalise and validate the requested type as concrete.
2. Insert its declaration and `Defining` state before walking fields.
3. Emit the body. A recursive field requests the same key and receives the
   already-declared `FuncId`; mutually recursive types likewise close through
   declarations already placed in the registry.
4. Mark the body `Defined` after successful definition.

Thus compiler traversal visits a finite graph of concrete type nodes, while the
generated functions recurse over the finite runtime value graph. It never
expands a recursive type tree in the compiler. A `Defining` re-entry emits a
call, not another body. A duplicate body definition, non-concrete key, missing
type definition, or unresolved field substitution is a located compilation
error; it never selects shallow release.

Ordinary acyclic nesting of depth 1, 2, 4, 5, or greater produces one function
per distinct concrete type and calls between them. Recursive nullary termination
performs no recursive call; recursive data constructors call glue only for the
runtime-present child. Language values cannot contain an ownership cycle without
an explicit cycle-forming feature; this sprint does not invent cycle collection.

### 3.3 JIT, object, cache, and link behavior

Glue is backend-emitted `Linkage::Export` code in the same Cranelift module and
compilation transaction as its callers. `compile_to_module` keeps its existing
signature and proactively requests glue for every concrete owning return type
reachable from its compiled targets, including the inner `a` of entry `IO a`.
The same declaration-first registry serves these result roots and all internal
displacement callers. JIT finalization and object emission therefore contain the
same module-qualified body with no alternate compilation path.

Backend projects the defined registry into its behavior-owned public carrier:

```rust
#[non_exhaustive]
pub struct DropGlueArtifact {
    pub symbol: LinkerSymbol,
    pub jit_address: Option<usize>,
}

pub struct CompilationArtifacts {
    // existing fields unchanged
    pub drop_glues: HashMap<ConcreteType, DropGlueArtifact>,
}
```

Every map key must agree with `artifact.symbol ==
drop_glue_symbol_name(module, key)`. Fresh JIT finalization records
`jit_address: Some(finalized_address)`; object mode records `None`. The address
is an observation, not a retention owner: it is valid only while int retains the
existing `Code::Jit(Arc<Jit>)`. A requested owning result type missing from the
projection, a symbol/key mismatch, or an unavailable fresh-JIT address is a hard
compilation/integration error.

Cache-hit execution serializes neither the map nor any address. Its object
already contains the exported glue body; int derives the same symbol through
`drop_glue_symbol_name` and performs one existing `Linker::get_symbol` lookup,
retained by `Code::Linker(Arc<Linker>)`. Linked startup declares an ordinary
relocation to that same module-qualified symbol, and the defining module object
supplies it to the system linker. Thus fresh JIT, cache-hit, and standalone link
invoke one backend-emitted body while using only their established code-retention
owners.

The registry lifetime is one `compile_to_module`/module construction, never
global mutable state. Concurrent compilations have disjoint registries. Cache
schema does not change: no serialized carrier or heap layout changes — S118's
schema fence (arch ruling 1 / QA §1) authorises exactly one 23→24 window and it
belongs to 0869, not to this migration. Forbidden alternatives are: a GOT slot
(glue is not language-callable or redefinable), arbitrary public JIT-symbol
lookup, a serialized address or artifact map, a cache-schema bump for this
carrier, a second compile entry, private compile-after-cache-miss glue, a
JIT-only helper, a generic type-erased releaser, or a heap/C-ABI change. These
choices apply **Single pipeline, mode parameters**, **Testability is
structural**, and **Parallel development is a first-class constraint**.

### 3.4 As-built reconciliation (2026-07-25, HEAD `fca20835`)

The S116 foundation was read line-by-line against this design. Line numbers rot;
the seam names are the durable reference.

**Conforming as designed** (no change owed): declaration-before-walk ordering
(`drop_glue.rs:93–101`); `Defining` re-entry returning the declaration
(`define`, `:105–110`); the completeness fence in `finish()` (`:440–451`); the
`ConcreteType`-keyed map; `Linkage::Export` + `drop_glue_symbol_name` identity
(`:86–92`); nullary-tag guarding derived from the type's own ctor set
(`guard_nullary`, `:475–477`) rather than from a caller-supplied flag; field
discharge strictly inside the `old_rc == 1` branch (`emit_outer_drop`,
`:239–271`); positional `TypeId → ConcreteType` substitution validated against
each constructor's declared ADT result (`ctor_shapes`, `:397–425`); the
artifact projection and JIT/object address polarity (`lib.rs:749–766`);
result-root discovery including the inner `a` of `IO a` (`lib.rs:672–684`).

**Drift and resolution direction:**

- **D1 — the registry cannot reach a consumer as shaped. BLOCKING; slice S0.**
  `DropGlueRegistry<'a, M, C, L>` holds `module: &'a mut M`
  (`drop_glue.rs:38`), and `FnCompiler` holds `module: &'a mut M`
  (`fn_compiler.rs:62`). Both cannot exist. Independently, the registry is
  constructed *and* `finish()`ed at `lib.rs:685–700`, before
  `compile_module_bodies` runs at `lib.rs:715`, so no body-compilation consumer
  could request glue even if the borrow allowed it.
  **Resolution — reshape M1 to be module-borrow-free**, not re-borrow the
  module: the registry becomes state only (`module_path`, `dealloc_id`,
  `vec_drop_id`, `entries`), and every method takes `module: &mut M` and
  `symbol_tables: &DashMap<…>` as arguments. `FnCompiler` gains one field
  `glue: &'a mut DropGlueRegistry`, disjoint from `module` and `ctx`, so
  `self.glue.request_if_owning(self.module, self.ctx.symbol_tables, ty)?` is a
  legal disjoint-field borrow. `compile_to_module_impl` owns the registry across
  Step 3 and calls `finish()` after `compile_module_bodies` and before
  `module.finalize_for_code_read()`, so `project_drop_glues` still sees
  finalized addresses. Rejected alternative: a per-`FnCompiler` cache or an
  `Rc<RefCell<…>>` — §3.1 names the registry as the *sole* construction
  authority, and interior mutability would hide the ordering the `finish()`
  fence checks.
  **Precedent that mid-body definition is safe:** `emit_capture_dec_glue`
  (`lambda.rs:245`) already declares and defines a function into the same
  `Module` while the enclosing body's `FunctionBuilder` is live, via a fresh
  `make_context()`. M1's `define` uses the identical pattern.

- **D2 — the key is `ConcreteType`; two seam families hold `Type`.** The match
  seam already has the concrete type natively (`MonoExpr::ty() -> &ConcreteType`;
  `match_codegen.rs:236` classifies off it and then converts *down* via
  `to_type()` only to feed the legacy emitter — the migration deletes that
  conversion). The scope/flush family reads `variable_types: HashMap<Symbol,
  Type>` and goes through `signature_heap_category`, whose `Err` arm maps a
  residual `Type::Var`/`TyConApp` to `Mixed` (FIXME 0394 — the generic
  constructor `Def`'s own template body).
  **Resolution:** the release seams take a `ConcreteType`; a
  `ConcreteType::from_type` failure at a *release* site is a located
  `CodegenError` naming the type and the requesting function (§3.2's
  non-concrete-key rule), never a shallow dec. **Entry check for slice S1:**
  `/dev` enumerates every release call site that cannot supply a concrete type
  *before* migrating. The expected answer is none — the residual-`Var` path is a
  *classification* path used by the generic ctor template, which constructs and
  never releases. If a release site is genuinely reached with a non-concrete
  type, **STOP**: that is a typecheck producer gap routed by FIXME, not a licence
  for a fallback arm. Re-typing `variable_types` to `ConcreteType` is a
  *candidate follow-on*, explicitly out of this wave's scope.

- **D3 — a second named-glue identity home survives in `vec_codegen`.** See
  §1.1 M3. Resolution: delete with M2 in the same wave; re-point
  `resolve_elem_dec_fn_ptr` / `resolve_elem_dec_fn_ptr_into` at M1's
  `define_vec_elem_adapter`.

- **D4 — a fourth inline consumer is unnamed in the sprint's slice list.**
  `apply::emit_post_call_decs` (`apply.rs:1419`) releases `Borrowed`-param
  temporaries through `emit_typed_rc_dec`, which is the inline emitter's
  dispatcher. Resolution: converting `emit_typed_rc_dec` itself (slice S1)
  migrates this consumer and the inline glue's own field walk together; no
  separate slice is needed, but the acceptance must name it.

- **D5 — request eagerness makes emission order input-dependent.** `request`
  declares and immediately `define`s (`drop_glue.rs:101`). After migration the
  first request for a type occurs mid-body of whichever function reaches it
  first, so the order of emitted glue functions varies with compilation input.
  This is harmless by construction (identity is the type; `entries` and
  `get_name` dedup), and it is the design's claim: **glue behaviour must be
  order-independent.** `/review` rejects any observable order dependence; the
  unit matrix pins "two callers share one body" and "repeated request is
  idempotent".

- **D6 — result-root pre-request stays, but no longer terminates the
  registry.** The `lib.rs:672–700` pre-pass is the ruling-9 obligation feeding
  0745 and remains a proactive superset of consumer demand. Only its `finish()`
  moves.

- **D7 — the legacy emitter carries dead complexity.**
  `emit_inline_drop_glue`'s `is_mixed` parameter is always `false` at its single
  call site (`rc_emission.rs:551`), so `emit_mixed_adt_heap_guard` is
  unreachable from it; the nullary guard is carried by the outer
  `needs_guard`. Nothing to preserve — it deletes with M2. Recorded because it
  is evidence for the deletion, not a separate fix.

- **D8 — M1 re-implements the closure free-path.** `emit_outer_drop`'s
  `GlueShape::Closure` arm (`drop_glue.rs:248–264`) duplicates the free-path of
  `rc_emission::emit_closure_dec_into` (`:31–100`). Fold M1's arm onto the free
  function during slice S4 (both are borrowed-builder-shaped, so it is a direct
  call). Zero behaviour delta; **Single source of truth**.

- **D9 — no semantic movement under S117.** `git diff -w` from the S116 close
  (`f24f258b`) to HEAD over `match_codegen.rs`, `rc_emission.rs`,
  `fn_compiler.rs`, `capture_rc.rs` and `lambda.rs` is **whitespace only** — the
  S117 close commit reformatted these files and changed no release, ownership,
  or lifetime logic. `cranelisp-types` has not changed since S116
  (`c81d0ce6`). S117's canonical trait identity and method carriers
  (`UnresolvedTraitMethodSig` / `TraitMethodKind`) are trait-surface types;
  drop-glue identity keys on `ConcreteType` / `FQTypeName` and constructor
  storage via `member_key`, none of which they touch. **§5 and §6 therefore
  survive contact with HEAD unchanged**; the refinements below are HEAD-specific
  seam detail, not corrections.

---

## 4. One release emitter, many releasing seams

`emit_typed_rc_dec` becomes a thin glue-call emitter: classify non-owning/value
representations as no-op, and call the canonical glue for an owned heap pointer.
It does not recursively inspect ADT fields itself, and it does not need a
caller-supplied `needs_guard` — the nullary-tag guard is a property of the
concrete type and lives once inside the glue body (`guard_nullary`). Removing
`needs_guard` from the call sites is part of the simplification, not an
optional tidy: it is the last place a *site* could disagree with a *type* about
how a value is released.

Environment glue (explicit lambdas, auto-curry, poll state and future capture
sets) is generated from one environment-body builder. Each capture descriptor
contains its concrete type and ownership disposition; owning captures call the
canonical type glue. This folds 0796 by construction: user-written and
compiler-synthesised closures differ only in who supplies the capture list.
Three copied drop-glue skeletons or a special explicit-`fn` repair are rejected.

Vec glue owns runtime iteration but delegates element discharge to the same
canonical glue identity, through M1's `(i64) -> i64` adapter over the
established `vec_drop` callback ABI. Closure-typed fields call the closure box's
embedded environment glue after their outer RC reaches zero. ADT glue branches on
the runtime constructor and walks exactly that constructor's concrete
substituted fields. Every path performs field discharge only in the
`old_rc == 1` branch.

**The seam map after migration** (each row is one release site and its single
mechanism):

| Seam | Home at HEAD | After |
|---|---|---|
| scope-exit cleanup | `fn_compiler::pop_scope_with_cleanup` → `emit_heap_binding_decs` | one `drop<T>` call per binding |
| let-scope tail flush | `flush_let_scopes_before_tail_jump` → `emit_heap_binding_decs` | same, shared body |
| superseded param flush | `flush_superseded_heap_params_before_tail_jump` → `emit_heap_binding_decs` | same, gated by §6's ONE predicate |
| match wrapper release | `match_codegen::dec_temporary_scrutinee` | per-arm `drop<S>` (§5) |
| moded-arg post-call dec | `apply::emit_post_call_decs` → `emit_typed_rc_dec` | one `drop<T>` call |
| ADT field walk | `rc_emission::emit_field_decs` | inside M1's generated body |
| Vec element dec | `vec_codegen::build_elem_dec_fn` + `build_adt_drop_glue_fn` | M1's `define_vec_elem_adapter` |
| capture slot release | `capture_rc::emit_capture_dec_into` (`Plain` arm) | one `drop<T>` call per owning slot |
| closure box release | `emit_closure_dec_into` | retained (§1.1 M5) |

---

## 5. Match-owned scrutinee protocol

`compile_match` records one lifetime plan before emitting arms:

- `Borrowed`: enclosing scope/callee owns the scrutinee; match emits no wrapper
  release and pattern bindings remain borrowed.
- `OwnedForwarded`: an arm transfers the whole scrutinee; that path suppresses
  wrapper release and carries exactly one owner.
- `OwnedConsumed`: match owns a temporary. Each arm protects/transfers any
  extracted field that outlives the wrapper, then calls `drop<S>` once at the
  arm-local lifetime end.

Release is per arm, not after the merge under a whole-match `any arm forwards`
approximation. Constructor and var patterns consume the same plan. No spelling
test (`Var` versus inline expression) is ownership authority. No arm may both
forward the wrapper and release it, or borrow an extracted field after wrapper
release. The common glue supplies deep discharge; match code owns only lifetime
placement.

### 5.1 What that costs at HEAD, and the 0782 owner ruling

The plan replaces three interacting HEAD mechanisms:

1. **The whole-match approximation.** `match_forwards_scrutinee(arms)`
   (`fn_compiler.rs:1683`) is a static `arms.iter().any(…)` predicate; a single
   forwarding var arm suppresses release for **every** path, including a
   constructor arm that genuinely consumed the temporary (FIXME 0726's mixed-arm
   leak; `binding-indirection-consume.md` §2). It is deleted as a *release* gate.
   It has a second, unrelated consumer — `operand_live_binding_root`
   (`fn_compiler.rs:1711`), a provenance trace, not a release decision — which
   keeps it. Deleting the predicate outright is wrong; deleting its use at
   `match_codegen.rs:149–152` is the change.
2. **The merge-block single release.** `dec_temporary_scrutinee`
   (`match_codegen.rs:232`) runs once, after the merge, for the whole match. It
   moves to a per-arm emission at each consuming arm's lifetime end, before that
   arm jumps to the merge block. The COW exception
   (`scrutinee_cow_retains_reused`, the balancing dec of the §13.7 escape-inc)
   travels with it **per arm** and keeps its polarity; it is the dec side of the
   same escape gate, never an independent exemption.
3. **The var-pattern alias registration.** `compile_var_pattern_arm`
   (`match_codegen.rs:190–196`) pushes the bound name onto `scope_stack` when
   `yields_owned_temporary(scrutinee)` is true, so `pop_scope_with_cleanup` decs
   it at arm exit — *and* the merge-block dec fires for the same pointer, because
   the two gates are exact complements on the ownership question but nothing
   reconciles their both firing. Two `atomic_rmw sub` on one value; `--link`
   exit 134 (FIXME 0782).

**Ruling — one owner, and it is the arm's lifetime plan (0782 resolution (a)).**
The var-pattern binder is a **borrow of a value the match frame owns for the
arm's duration**, exactly as a constructor pattern's field bindings are. The arm
does not register it for scope cleanup; the `OwnedConsumed` plan's per-arm
`drop<S>` is the single release, for both pattern kinds. Resolution (b) —
register the alias and suppress the arm's release — is rejected: it makes the
release owner depend on the *pattern kind*, which is the per-spelling rule §5
exists to eliminate, and it leaves the constructor arm and the var arm on
different owners for the same lifetime event.

Consequences that the acceptance must show, because they are the two polarities
the fix must satisfy simultaneously:

- a var arm that **forwards** the whole scrutinee (`[r r]`) is `OwnedForwarded`:
  no arm release, one owner travels out (control
  `control_var_pattern_arm_over_let_bound_scrutinee_linked` stays GREEN);
- a var arm that **consumes** (`[xs (vec-get xs 1)]`) is `OwnedConsumed`: exactly
  one release, at arm end (cell #10 flips);
- a constructor arm over an owned temporary whose payload **escapes** into a tail
  argument protects the field first, then releases the wrapper (cells #1–#9);
- a **mixed** ctor+var match where the var arm forwards no longer suppresses the
  ctor path's release (FIXME 0726's tripwire cells, QA §4.2).

`yields_owned_temporary` (the three-point provenance lattice,
`Fresh ⊑ OwnedTemporary ⊑ NotOwnedHere`) remains the ownership authority that
selects the plan; it is not re-derived per pattern kind. The plan is recorded
**once** before arms are emitted, so a reader can see the arms consume one
answer rather than two complementary tests.

---

## 6. TCO replacement/transfer predicate

`flush_superseded_heap_params_before_tail_jump` consumes one pure predicate per
old slot/new argument pair. The predicate returns `TransferOldOwner` only when
the exact old owner is carried into the next iteration:

| New argument / state | Verdict | Old-slot action |
|---|---|---|
| bare local `Var` rooted at that old slot, including a legal cross-slot move | transfer | no release; move bookkeeping prevents a second owner |
| control-flow expression proven by the existing tail protection to forward that exact root | transfer | no release |
| analysis-on in-place COW result proven to reuse that exact root | transfer | no release |
| borrowed alias/projection without an independently owned reference | not a transfer | reject/retain protection required; never use it to suppress release |
| fresh constructor/call/literal, copied COW result, unrelated variable, or unknown provenance | replacement | call `drop<T>` before slot overwrite |

Classification and release remain separate: the predicate decides owner
continuity; canonical glue performs discharge. The predicate feeds both
let-scope flushing and parameter-slot flushing where they ask the same owner
question, so `tail_transfer_skip`, control-flow protection, borrowed state and
in-place-COW cannot drift into competing exemptions. Unknown is conservative
replacement, but an ownership-invalid borrowed replacement is a loud compiler
error rather than a guessed release. This is the backend instance of
**Narrowing carries its check**.

### 6.1 The fragments to fold, at HEAD

The one predicate replaces four separately-evaluated conditions that today are
combined ad hoc inside two `collect_frame_heap_decs` filters:

| Fragment | Home | Table row it answers |
|---|---|---|
| `tail_transfer_skip(args)` — literal top-level `Var` args only | `apply.rs:54` | row 1 (bare move) |
| `tail_arg_protect` / `maybe_protect_tail_arg_alias` — the per-branch protective inc that makes control-flow args safe under a *uniform* flush | `fn_compiler.rs:1341` | row 2 (control-flow forward) |
| `param_flush_exempts_inplace_cow(args, name, analysis_off)` → `arg_is_inplace_cow_on` | `fn_compiler.rs:1628/1646` | row 3 (in-place COW) |
| `is_borrowed(name) && !tco_owned_params.contains(name)` | `fn_compiler.rs:1283` | row 4 (borrowed alias) |

Two design constraints on the fold, both load-bearing:

- **Row 2 must not become a `transfer` verdict that suppresses the dec.** At
  HEAD a control-flow-aliased binding is deliberately *not* skipped: it receives
  a protective inc at the branch tail and is then flushed uniformly, because
  `(recur (if c lo hi))` has distinct per-branch bindings and a single static
  skip would retain the dead branch's binding (the F1 UAF cure,
  `ownership-codegen.md` §13.3). The predicate therefore returns
  `TransferOldOwner` for row 2 **only where the existing tail protection proves
  the exact root forwards** — i.e. the predicate reports the classification, and
  the protect-plus-uniform-flush emission strategy is preserved wherever the
  root is not exact. A refactor that turns row 2 into a blanket skip
  re-introduces F1.
- **Row 3 keeps its toggle asymmetry.** Under `CRANELISP_NO_OWNERSHIP` the COW
  always copies, nothing is carried forward, and the dec is always owed (FIXME
  0695); the exemption is analysis-ON only and positional-blind (FIXME 0691).
  The predicate takes the toggle as an explicit input rather than reading it at
  two sites.

The predicate is a **pure free function over `(args, slot name, liveness/borrow
facts, analysis_off)`** returning a closed sum
`TransferOldOwner | Replace | BorrowedInvalid`, unit-testable without a live
`FnCompiler` (the `is_fresh_construction` / `cow_site_source` precedent). The
`BorrowedInvalid` arm is the **Narrowing carries its check** instance: a
borrowed alias offered as a replacement is a located compiler error, not a
guessed release and not a silent skip.

---

## 7. The migration — serial slices

One wave (`/sprint` W3), serial, single `/dev` agent. Slices are staged in this
order; §8 constrains where the wave may be split.

### 7.0 Slice S0 — registry reshape and threading (enabling; behaviour-neutral)

**Seams:** `drop_glue.rs:32–103` (struct + `new` + `request*`);
`lib.rs:685–700, 736` (construction, `finish`, projection);
`fn_compiler.rs:56–70` (struct), the `FnCompiler` constructors
(`fn_compiler.rs:425, 593`) and every inner-compiler construction site;
`lib.rs::compile_module_bodies` → `compile_defn_in_module` threading.

**Change:** D1's reshape. Registry state loses `&'a mut M` and the
`&'a DashMap`; methods take them. `FnCompiler` gains
`glue: &'a mut DropGlueRegistry`. `finish()` moves after body compilation and
before `finalize_for_code_read()`.

**Flips:** nothing. Canonical glue still has no consumer; every existing test
stays byte-identically coloured. This is the slice's acceptance: a behaviour-
neutral structural change, verified by "every currently-GREEN cell stays green
and every baseline RED stays RED with an identical signature" (the same
invariance pin QA applies to 0850, plan §3.2).

### 7.1 Slice S1 — `emit_typed_rc_dec` becomes the glue-call emitter

**Seams:** `rc_emission.rs:317–350` (`emit_typed_rc_dec`), its two callers
`rc_emission.rs:286` (`emit_field_decs`) and `apply.rs:1419`
(`emit_post_call_decs`); the D2 entry check across all release sites.

**Change:** the body becomes: classify the `ConcreteType`; `NeverHeap`/`Value`
→ no-op; otherwise request glue and `call` it. `needs_guard` leaves the
signature. `TypedRelease` / `typed_release_kind` are subsumed by the registry's
`shape()` and become dead (they delete in §8, with their unit module rehomed
onto the registry's shape classification so the Vec-before-ADT order rule keeps
its guard).

**Flips:** none directly; this is the mechanism swap that later slices stand on.
It does change emission for `Borrowed`-param temporaries (D4) — the acceptance
must show the 0753 controls (`moded_arg_rc_tests`) stay green.

### 7.2 Slice S2 — 0835 SList construction (arch-ruled first; **attribution-gated**)

Arch ruling 1(d) orders 0835 first; ruling 1(a) requires "controlled reduction
and permanent repro for the corruption face" *before* migration. **Neither
exists at HEAD**: there is no `tests/*0835*` file, no `// defect:` cell, no
`PLAN.md` row, and 0835 is absent from QA's 28-name baseline (plan §2.1) and
from the §4 Track-B matrix. FIXME 0765 ("no fix without a repro precondition")
therefore blocks this slice as written.

Worse for the ordering: **the leading mechanism candidate is not in this
crate.** Read at HEAD, `cranelisp_primitives::marshal::sconcat`
(`marshal.rs:195–217`) calls `deep_rc_inc_slist(ys)` — `+1` on every `SCons`
node *and* every element of `ys` (`marshal.rs:160–171`) — and balances it with
`consume_slist(ys)` (`cranelisp-intrinsics/src/drop.rs:134–155`), which
**returns at the first node whose `old_rc != 1` and never descends**. After the
deep inc no node's rc is 1, so `consume_slist` decrements the head only. Every
non-head node of `ys`, and every element it holds, retains a `+1` that no later
release can discharge: the caller's own release of `ys` stops at the same
early-return, and the result's release stops at the shared head. That is a
per-call deep leak proportional to `|ys|`, growing across chained `sconcat`
calls — which matches 0835's "hand-chained `sconcat` is fine, freshly-built
cells consumed in the same expression die around six cells" signature and its
`derive`-visible arity ceiling.

This is the S116 ruling-2 inventory's **second** row (known runtime protocol
trees → their intrinsics `consume_*` owner), not the first (generated lexical
ownership → backend type-directed glue). **The backend consumer migration does
not reach `sconcat`.**

**Design position:** slice S2 is *attribution-gated*, not cancelled. Its first
act is `/qa`'s attribution over a committed repro, with this falsification
recipe: run FIXME 0835 repro B under `CRANELISP_RC_STATS=1` and count
`allocs - deallocs` as a function of the number of `step` applications. A
residual growing with `|ys|` per `sconcat` call confirms the marshal/consume
asymmetry and re-owns the defect to `/dev`(runtime); a residual that is instead
proportional to the *type* nesting depth, or that vanishes when the backend
consumers migrate, confirms the transitive-discharge class and keeps it here.
Filed as FIXME 0877 (`target: /qa`). If attribution lands outside backend, the
Track-B slice order becomes S0 → S1 → S3 → S4 → S5 → deletion with no loss:
0835 is not a precondition of any other slice, and ruling 1(d)'s "0835 first"
was an ordering of *the transitive-discharge class*, which it may turn out not
to join.

### 7.3 Slice S3 — 0810 match-scrutinee lifetimes (all ten committed cells + 0782)

**Seams:** `match_codegen.rs:30–155` (`compile_match` — the plan record and the
per-arm release placement), `:159–215` (`compile_var_pattern_arm` — the alias
registration deletion), `:232–256` (`dec_temporary_scrutinee` — becomes a
per-arm helper on a `ConcreteType`), `:262–…` (`compile_constructor_pattern` —
the protect-before-release ordering); the release-gate use of
`fn_compiler.rs:1683` (`match_forwards_scrutinee`) at `match_codegen.rs:149`.

**Change:** §5 in full — record `Borrowed | OwnedForwarded | OwnedConsumed`
once from `yields_owned_temporary` before arms are emitted; emit the wrapper
release per consuming arm at its lifetime end; delete the var-arm alias
registration per §5.1's ruling; route the release through canonical glue with no
`needs_guard`; carry the COW-retain exception per arm.

**Flips:** baseline cells #1–#9 (0810: inline-call wrapper, inline constructor,
heap payload, wrapper-superseding-loop-param, and the let-bound payload/tag
faces, `--run` and `--link`) and #10 (0782 var-pattern double-release, `--link`
only). QA's 0726 tripwire ctor-path cells (§4.2) flip here. Green controls that
must STAY green: `control_let_bound_int_payload_scrutinee_balances(_linked)`,
`control_match_in_callee_on_borrowed_param_balances`,
`control_var_pattern_arm_over_let_bound_scrutinee_linked`.

**Note the instrument asymmetry** the test file records and the acceptance must
respect: 0782's `--run` leg reads 2/2 GREEN while `--link` aborts 134 — an
exact-balance instrument is blind to a double-release of a value that was going
to be freed anyway. The release-exactly-once face is a `--link` obligation, and
the unit tier must assert **exactly one** release instruction on the scrutinee
value per consuming arm, not "at least one" (the deliberately loose S115 pin
`fresh_vec_literal_scrutinee_still_releases` is superseded here).

### 7.4 Slice S4 — 0760 / 0796 capture and auto-curry teardown

**Seams:** `capture_rc.rs:66–117` (`CaptureRelease` + `emit_capture_dec_into`),
`lambda.rs:180–225` (`build_closure_drop_glue` — explicit `fn` captures,
`Type`-shaped), `fn_as_value.rs:1073–1110` (`build_auto_curry_drop_glue` —
compiler-synthesised captures, `ConcreteType`-shaped),
`lambda.rs:245–316` (`emit_capture_dec_glue` — the shared envelope, retained),
`par_bind.rs` / poll-state continuation captures (same envelope).

**Change:** `CaptureRelease` stops describing a slot by `HeapCategory` alone.
Its `Plain(HeapCategory)` arm becomes a canonical-glue reference — the enclosing
`FnCompiler` requests `drop<T>` for the slot's concrete type *before* the glue
body's builder is created, and `emit_capture_dec_into` emits a `call` to it.
`ClosureBox` is retained (§1.1 M5). The two mirrors differ only in who supplies
the capture list, which is exactly 0796's binding census requirement: the
auto-curry env is a compiler-synthesised capture set reaching the identical
seam, so "fix the `fn` path" was never a scoping option.

**Flips:** cells #11 (`closure_capturing_vec_of_strings_does_not_leak`),
#12 (`closure_capturing_adt_with_string_field_does_not_leak`),
#13 (`nested_adt_chain_past_glue_depth_limit_does_not_leak` — the depth-5 cliff,
which §8's deletion is what actually removes) and #14
(`transitive_drop_glue_s116::finite_recursive_values_zero_one_many_terminate_and_balance`).
Green controls that must stay green: Vec-of-scalars capture; closure-capturing-
closure; the `Borrowed`-ARGUMENT twins of K and L; depths 1–4.

**0796's acceptance, transcribed here so it survives the FIXME's deletion:**
`/testing` removes the `curried_partial_application` entry from
`tests/gen_ownership_flows.rs::balance_exclusion`, and the harness must then run
clean over that position for every owning type under both toggles. Removing the
exclusion **is** the 0796 acceptance check; a fix that flips #11–#13 while the
exclusion stays is incomplete.

### 7.5 Slice S5 — 0688-family TCO replacement/transfer predicate

**Seams:** `fn_compiler.rs:1267–1296`
(`flush_superseded_heap_params_before_tail_jump`), `:1218–1238`
(`flush_let_scopes_before_tail_jump`), `:1152–1197` (`emit_heap_binding_decs` —
the **last** inline-emitter consumer), `:1126–1150`
(`collect_frame_heap_decs`), `apply.rs:54` (`tail_transfer_skip`),
`apply.rs:2148–2156` (the call order at the jump),
`fn_compiler.rs:1628/1646` (the COW exemption).

**Change:** §6 — introduce the pure `TransferOldOwner | Replace |
BorrowedInvalid` predicate; both flushes consult it; `emit_heap_binding_decs`
emits one `drop<T>` per replaced slot through canonical glue (its three
special-case arms — closure / Vec / ADT — collapse into the one call, since the
type decides teardown inside the glue body).

**Flips:** cells #19/#20 (`ms_p8_conj_leak::conj_loop_does_not_leak`,
`conj_loop_parity_no_abort`) and #21
(`exemplar_ownership_residue_s116::sudoku_warm_serial_solve_residue_at_most_1400`)
are QA's **verified consequents** (§4.4): they are expected to flip as a
consequence of S3 + S5, are verified rather than patched, and a residual RED is
a new attribution routed to `/qa` — never a threshold change and never a
per-seam patch. Green controls: `adt_wrapped_supersede_leak_0720`,
`tail_transfer_skip_tests`, the bare-Vec and carry-forward controls named in
S116 ruling 7.

### 7.6 Slice S6 — the atomic deletion

See §8. It is the final act of the wave and may not be separated from S5.

---

## 8. The atomic deletion condition (S118 arch ruling 10)

The Principle-8 bridge — a canonical registry coexisting with the legacy inline
emitter — closes this sprint. The condition is: consumers migrate **and** the
depth constant plus the inline recursive emitter delete **atomically in the same
wave**. A partial migration leaving both mechanisms is a `/review` REJECT.

**Deletes in slice S6:**

| Symbol / path | Home |
|---|---|
| `MAX_DROP_GLUE_DEPTH` (the `const` and its guard block) | `compiler/rc_emission.rs:492–500` |
| `FnCompiler::drop_glue_depth` (field, both initialisers, both mutations) | `compiler/fn_compiler.rs:168, 425, 593`; `rc_emission.rs:501, 562` |
| `emit_rc_dec_with_inline_drop_glue` | `compiler/rc_emission.rs:476` |
| `emit_inline_drop_glue` | `compiler/rc_emission.rs:116` |
| `emit_mixed_adt_heap_guard` (unreachable per D7) | `compiler/rc_emission.rs:186` |
| `emit_drop_glue_field_decs` | `compiler/rc_emission.rs:210` |
| `emit_field_decs` | `compiler/rc_emission.rs:270` |
| `TypedRelease` + `typed_release_kind` (subsumed by the registry's `shape()`) | `compiler/rc_emission.rs:572, 587` |
| `build_adt_drop_glue_fn`, `build_elem_dec_fn` (the second identity home, §1.1 M3) | `compiler/vec_codegen.rs:1137, 1054` |
| `adt_drop_glue_name`, and `adt_instantiation_mangle` if it retains no other consumer | `compiler/resolution.rs:263, ~190` |
| `build_adt_type_substitution` (inline-glue-only helper) | `compiler/rc_emission.rs:604` |

**Explicitly NOT deleted:** `emit_closure_dec_into` (§1.1 M5),
`emit_capture_dec_glue` (§1.1 M4 — the capture-LAYOUT owner),
`closure_drop_glue_name` / `curry_drop_glue_name` (they name capture
envelopes, not type glue), `match_forwards_scrutinee` (retained for
`operand_live_binding_root`'s provenance trace — only its *release-gate* use
goes, §5.1), `substitute_type_inline` / `collect_var_ids_from_type` (live
consumers in `match_codegen` and `vec_codegen`).

**Where the deletion lands.** After S1 the inline emitter has exactly two direct
call sites left — `match_codegen::dec_temporary_scrutinee` (S3) and
`fn_compiler::emit_heap_binding_decs` (S5) — so the emitter becomes dead the
moment S5 lands. The deletion is therefore the **final commit of the same
change-set as S5**. The wave may be staged internally (S0 … S5 as successive
commits) but **may not be split between S5 and S6**: that split is precisely the
both-mechanisms-alive state ruling 10 declares a REJECT.

**Alignment with QA's structural fence** (plan §4.3, RED today by construction,
flips exactly at this change-set): grep-zero `MAX_DROP_GLUE_DEPTH` and
`drop_glue_depth` in `crates/cranelisp-backend/src/`, plus absence of the inline
recursive emission path asserted on its **named seam**
(`emit_rc_dec_with_inline_drop_glue` / `emit_inline_drop_glue`), not a line
number. The canonical registry already carries its own in-crate no-cutoff fence
(`drop_glue.rs:830–835`) and it stays.

**Fence gap (filed, not assumed).** The fence as specified would pass with §1.1
M3 alive. `/design` files FIXME 0878 (`target: /qa`) proposing the fence extend
to grep-zero `adt_drop_glue_name` / `build_adt_drop_glue_fn` / `build_elem_dec_fn`.
Independently of whether QA adopts it, **`/review` rejects a wave that leaves a
second named-glue identity home** — §1.1 and §11's no-interim list are the
in-crate authority.

---

## 9. Acceptance mapping

The e2e contract is `/qa`'s (`tests/plan/s118-test-plan.md` §4): the carried
S116 matrix, reconciled exists-vs-authors, with no re-derivation here. This
section maps it onto the slices and records the two obligations that are
design-visible.

| Slice | Baseline cells that flip | Controls that must stay green | Owner-unit obligation |
|---|---|---|---|
| S0 | none (invariance) | all | registry reshape identity/idempotency cells |
| S1 | none | `moded_arg_rc_tests` (0753 controls) | glue-call emitter cells (§10 row 3) |
| S2 | attribution-gated (§7.2) | — | none until attributed |
| S3 | #1–#10; QA 0726 ctor-path cells | C1/C1-link, C2, 0782 let-bound control | §10 row 5 |
| S4 | #11–#14 | Vec-of-scalars, closure-in-closure, `Borrowed`-arg twins, depths 1–4; **0796 exclusion removal** | §10 row 4 |
| S5 | #19–#21 (verified consequents) | `adt_wrapped_supersede_leak_0720`, `tail_transfer_skip_tests` | §10 row 6 |
| S6 | QA structural fence (§4.3) | — | §10 row 7 |

**Armed-detector acceptance (QA §4.1, the detectors-first dividend).** Each fix
slice must **re-demonstrate its flips under armed detectors**: `/dev`'s
acceptance run re-runs the flipped cells' programs in **child processes** with
M1+M2+M3 armed and shows clean exits. This is an acceptance-run obligation, not
a new committed-cell family — the committed cells stay unarmed and
deterministic. Two binding constraints, both owned by
`design/intrinsics/diagnostic-modes.md` §7.1 (the arming discipline is
intrinsics-design-owned; this is a cross-reference, not a restatement):

- arming is **lane/subprocess-scoped only, never suite-global** (S118 arch
  ruling 3): a globally-armed M3 aborts every still-red leak guard and destroys
  the baseline arithmetic;
- arming is by child `Command` + `env_clear` + explicit allow-list, **never**
  `std::env::set_var` — the `LazyLock` ledger makes `set_var` a silent no-op
  that *looks* armed, which would turn a clean-exit demonstration into no
  evidence at all.

An armed leg that cannot be produced because the detector proofs (Track A,
FIXME 0848) have not landed is a **sequencing failure, not a waiver**: Track B's
W3 runs after Track A's W2 for exactly this reason.

**Evidence discipline.** A cell that goes green without its owning slice landing
is treated with suspicion (QA §2.4, the S98 rule): perturbation reshapes layout,
so each flip must trace to the mechanism change-set. Conversely, S0's and S1's
acceptance is *invariance* — a baseline RED that flips during a
behaviour-neutral slice re-opens attribution rather than counting as a win.

---

## 10. Unit-test design: submodule × complexity/edge/negative matrix

Tests mirror module composition (**Tests mirror module composition**); `/dev`
places them beside the production owner rather than in one omnibus fixture, per
the crate `CLAUDE.md` sibling convention. Rows 1–2 and 7 largely exist from
S116 Wave 3 (`drop_glue.rs::tests`); rows 3–6 are the migration's new tier.

| Submodule | Complexity / positive cells | Edge cells | Negative cells |
|---|---|---|---|
| `drop_glue` identity | primitive-owning types; FQ ADT; two generic instantiations | repeated request is idempotent; same bare type name in two modules differs | non-concrete key rejected; collision witness; span/caller cannot alter identity |
| `drop_glue` registry/body builder | scalar leaf; ADT→String; ADT→Vec→ADT; depths 1/2/4/5/>5 | self-recursive list nullary/data arms; mutually recursive declarations; repeated field type emits one body; **request order permuted ⇒ same bodies, same keys (D5)** | no depth constant; no shallow fallback; duplicate definition and missing typedef fail loudly; **`finish()` rejects a `Defining` entry** |
| `rc_emission` glue-call emitter | owned heap pointer ⇒ exactly one `call` to the canonical symbol; final-ref body calls fields then dealloc; non-final ref touches no fields | Mixed ADT bare nullary tag guarded **inside** the body, not at the site; closure field; empty Vec | no field call on `old_rc > 1`; **no `needs_guard` parameter survives**; non-concrete type at a release site is a located error, never a plain dec; no deep owner routed to a bare dec |
| capture / environment glue | explicit closure over Vec/ADT; auto-curry equivalent; nested closure; poll-state capture | zero captures; repeated same-typed captures; a capture whose type is the enclosing closure's own | borrowed/non-owning capture not dropped; **every owning capture descriptor has a glue call** (the assertion 0760 says no instrument ever made); no second glue skeleton per mirror |
| `match_codegen` | inline and let-bound owned temporary; constructor and var patterns; the plan recorded once before arms | heap field forwarded into a tail call; whole-wrapper forward (`[r r]`); borrowed callee scrutinee; **mixed ctor+var match, ctor path selected** | no whole-match `any` suppression; no release-before-protect; no borrowed-scrutinee release; **exactly one release per consuming arm** (count, not existence — the 0782 face); var arm binder never registered for scope cleanup |
| `fn_compiler` / TCO predicate | unrelated fresh replacement releases; bare-Vec and ADT replacement use the same path | same-slot and cross-slot move; control-flow forward; analysis-on in-place COW (positional-blind); toggle-off copied COW | borrowed alias cannot license transfer (`BorrowedInvalid` is loud); fresh/unknown cannot suppress release; no TCO-private glue; **row 2 does not become a blanket skip** (the F1 regression fence) |
| `lib` compile orchestration | JIT and object request the same symbol set; registry survives body compilation and `finish()`es after it | recursive declaration finalizes once; two callers share one body; result-root pre-request is a superset of consumer demand | unresolved `Defining`/undeclared glue at finalize is a compilation error; no glue requested after `finish()` |

Unit tests assert emitted call identity and control-flow ordering, not only text
presence. Where a rule is pure (glue shape classification, the §6 predicate, the
§5 plan selection), the cell exercises the pure function without constructing a
live `FnCompiler` — the `typed_release_kind` / `cow_site_source` /
`is_fresh_construction` precedent, and the reason the deleted
`typed_release_kind` unit module is **rehomed** rather than dropped (its
Vec-before-ADT ordering rule is still load-bearing inside the registry's
`shape()`).

E2e acceptance remains `/qa`/`/testing`'s carried S116 matrix (§9).

---

## 11. Quality attributes and constraints

- **Simplicity / maintainability:** one type-keyed body registry replaces the
  inline recursive emitter, the second per-instantiation named-ADT identity
  home, and the per-site `needs_guard` negotiation. Complexity becomes
  proportional to distinct concrete owning types, not syntactic nesting depth or
  the number of release seams. Five mechanisms (§1.1) become one plus two
  explicitly-scoped runtime dispatches.
- **Observability:** construction failures name the concrete type, requesting
  function and missing definition/substitution. No silent fallback exists — the
  depth cutoff's shallow dec was precisely a silent, site-dependent change of
  release semantics for one runtime type, and it is the observability defect as
  much as the correctness one. Post-migration, `/clif <name>` shows a `call` to
  a named, type-derived symbol at every release site, which is legible in a way
  that inlined depth-N field walks were not.
- **Concurrency-safety:** registries are compilation-local (one per
  `compile_to_module`), never global; disjoint across concurrent compilations.
  Generated glue uses the same RC atomicity policy as the release it replaces.
  This sprint adds no shared mutable state and no backend-internal lock.
- **Performance:** one call per released outer owner and runtime traversal of
  exactly the owned graph; no depth-proportional code expansion. Glue inlining
  or specialization is out of scope until differential heap-balance evidence
  exists (**Complexity has a budget**).
- **Testability:** identity, registry state, the §5 plan selection and the §6
  predicate are pure and unit-testable; each lifetime seam has positive, edge
  and negative cells (§10). The armed-detector legs (§9) are the first time this
  class has an instrument that can *prove* a release reached everything the
  value owned — 0760 recorded that no such mechanism existed.

**No-interim constraints** (binding; `/review` reject criteria): no raised depth
constant; no shallow fallback; no borrowed-builder clone of recursive emission;
no 0835-, 0810-, capture-, or TCO-specific deep releaser; **no second named-glue
identity home**; no JIT-only helper; no third heap-header word; no global glue
registry; no generic type-erased release; no cache sidecar carrying process-local
glue addresses; no cache-schema delta from this migration (S118's single 23→24
window belongs to 0869); and no implementation that fixes only explicit `fn`
captures while leaving compiler-synthesised environments behind.

---

## Next skills

- `/qa` — attribute FIXME 0835 before slice S2 opens (FIXME 0877: the repro is
  missing and the leading mechanism candidate is `sconcat`'s deep-inc /
  `consume_slist` early-return asymmetry, outside this crate); consider the
  structural-fence extension in FIXME 0878.
- `/dev` (backend) — implement §7 in slice order S0 → S1 → (S2) → S3 → S4 → S5,
  with the §8 deletion in the same change-set as S5; add the §10 unit rows with
  each slice; produce the §9 armed acceptance legs per slice.
- `/review` (backend) — reject on: a surviving inline depth fallback or private
  releasing mechanism; a second named-glue identity home; a wave split between
  S5 and the deletion; a `needs_guard` parameter surviving on a release seam; a
  detector armed outside a child `env_clear` construction; a per-spelling
  release rule at the match seam.
- `/arch` — no new cross-crate interface is required by this migration
  (ruling 9's carrier is landed and unchanged); consult only if the D2 entry
  check finds a release site that cannot supply a `ConcreteType`.
