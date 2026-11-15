# Transitive drop glue and owned-value displacement

> **Owner**: `design`, narrow-deployed to `cranelisp-backend`.
> **Status**: current design, verified against source 2026-11-15. The S118
> consumer migration it once planned has landed. *When* a value is released —
> the move, duplicate and drop decisions — is
> [uniform counting](uniform-counting.md); this document owns *how* a release
> discharges what the value owns. §5 and §6 are retirement stubs.
> **Architecture inputs**: `design/arch/safety-invariants.md` R15;
> `design/arch/bounded-contexts.md` §3 and §4b, invariant 16.
> **Non-concrete releases** are owned by
> [the non-concrete release contract](non-concrete-release-contract.md), not by
> this document.
> Source and tests cite this document's section numbers and the positions of
> rows in its predicate and unit-test tables; do not renumber or reorder them.

## 1. Binding outcome

The backend emits one **named drop function for each concrete owning type**,
and every generated-code release site calls it. The function has the shape
`drop<T>(owned_word)`: decrement the outer value; only on the final reference,
release each field the value owns and then free the outer storage. Scalar and
one-word value types need no glue. `String`, `Fn`, `Vec`, `IO` and concrete ADTs
share the one call contract, even where their bodies delegate to a
layout-specific operation.

- **No depth bound and no shallow fallback.** Release reaches everything a
  value owns at any finite depth. The former inline recursive expansion, its
  depth constant and its shallow-dec fallback are deleted (§8).
- **Identity is the static concrete type.** The universal heap header stays two
  words; no type id or function pointer is added to ordinary allocations.
- **One exception carries a runtime pointer.** A closure box keeps its embedded
  capture-glue pointer, because its capture tuple is closure-instance shape,
  not a language type.

This is the end state under **No interim implementations** and **Single source
of truth**.

### 1.1 The mechanism census

Five mechanisms once minted or performed deep release. One survives as the type
glue authority; two are retained runtime dispatches.

| # | Mechanism | Standing |
|---|---|---|
| M1 | Canonical registry (`drop_glue.rs`): per-type bodies named by the types-owned `drop_glue_symbol_name`, `Linkage::Export` | **The survivor** — sole construction authority for type glue. |
| M2 | Inline recursive emitter, depth-bounded, per site | Deleted (§8). |
| M3 | A second per-instantiation ADT glue and Vec element-release builder under a backend-local mangle | Deleted (§8). It was a second identity home for the same concept; M1's Vec element adapter replaces it. |
| M4 | Capture drop-glue envelope (`emit_capture_dec_glue`, `CaptureRelease`) | Retained as the owner of capture **layout**. Each owning slot's release is an M1 call. |
| M5 | Closure-box embedded `DROP_GLUE_PTR` dispatch (`emit_closure_dec_into`) | Retained — the §1 exception. M1's closure shape delegates to it. |

A second glue identity is the same defect class as a depth-bounded one: it
reopens the question the single types-owned identity closed.

## 2. Actors and lifetime events

| Actor / event | Value before | Owner after | Required action |
|---|---|---|---|
| Plan drop: a binder's death point, a branch or arm entry | owned typed word | none | call `drop<T>` once |
| Closure, curry or poll-state capture teardown | owned capture slot | none | environment glue calls `drop<T>` for each owning capture |
| Constructor-pattern match | the match owns the scrutinee | each bound field owns a duplicate | duplicate the bound fields, then call `drop<S>` on the scrutinee at arm entry ([uniform counting](uniform-counting.md) §4) |
| Var-pattern match | the match owns the scrutinee | the binder | the binder takes the value; no duplicate and no release |
| Vec teardown | Vec owns each live element | none | the Vec body iterates the runtime length and calls element `drop<E>` |
| ADT teardown | box owns the fields selected by its runtime tag | none | the ADT body branches on tag and calls each field's glue |

## 3. Identity, construction, and recursion

### 3.1 Canonical identity

- **The key is `ConcreteType`**, including the fully-qualified ADT and all
  concrete arguments.
- **The symbol authority is exactly `cranelisp_types::drop_glue_symbol_name`**
  over the module and the concrete type. It is injective over the concrete type
  and module-qualified: two module objects that both need `String` glue export
  distinct symbols, and repeated requests inside one module share one
  declaration. The backend does not mirror its grammar.
- **Span, call site, spelling, traversal depth, requesting function and process
  address are not identity inputs.**
- **The registry is the sole construction authority.** It maps each key to
  `Declared | Defining | Defined` plus its `FuncId`. Ordinary lowering and every
  compiler-synthesised environment in the same module compilation share it; no
  per-compiler cache exists.

### 3.2 Finite construction for recursive types

Construction is declaration-first:

1. Validate that the requested type is concrete.
2. Record its declaration as `Defining` before walking its fields.
3. Emit the body. A recursive field requests the same key and receives the
   declared `FuncId`; mutually recursive types close the same way.
4. Mark the body `Defined`.

The compiler therefore walks a finite graph of type nodes, while the generated
functions recurse over the runtime value graph. A `Defining` re-entry emits a
call, never another body.

- **Loud failures.** A duplicate definition, non-concrete key, missing type
  definition or unresolved field substitution is a located compilation error.
  None selects a shallow release.
- **Termination.** A nullary constructor makes no recursive call; a recursive
  data constructor calls glue only for the child present at runtime.
- **No cycle collection.** Language values cannot form an ownership cycle
  without an explicit cycle-forming feature.

### 3.3 JIT, object, cache and link behaviour

- **One transaction.** Glue is `Linkage::Export` code in the same Cranelift
  module and compilation as its callers. JIT finalisation and object emission
  contain the same module-qualified body.
- **Result roots are requested up front.** `compile_to_module` requests glue for
  each compiled body's result root through `ConcreteType::result_root()`, the
  one-hop `IO a -> a` projection. That set is a superset of consumer demand.
  Backend code must not restate the `IO` shape.
- **The registry is fenced after bodies.** `finish()` runs after body
  compilation, where release seams request their glue, and before finalisation.
  An entry not `Defined` there is an error.
- **Projection.** `CompilationArtifacts.drop_glues` maps each concrete type to
  its symbol and, in JIT mode only, its finalised address. The address is an
  observation, valid only while int retains the matching `Code::Jit`.
- **Cache hit and link.** Neither the map nor any address is persisted. On a
  cache hit, int derives the same symbol and looks it up in the linker retained
  by `Code::Linker`. A linked program relocates against the same exported
  symbol. Fresh JIT, cache hit and standalone link therefore call one emitted
  body under their established retention owners
  ([result owner](../int/result-owner.md)).
- **Registry lifetime.** One registry per compilation; concurrent compilations
  have disjoint registries. There is no global glue state.

Forbidden alternatives: a GOT slot for glue (it is neither language-callable nor
redefinable), arbitrary public JIT-symbol lookup, a persisted address or
artefact map, a second compile entry, JIT-only helpers, a type-erased generic
releaser, or a heap-header or C-ABI change.

### 3.4 Settled seam decisions

- **D1 — the registry holds no module borrow.** It is state only: module path,
  release intrinsic identities and entries. Every method takes the Cranelift
  module and symbol tables as arguments, and each function compiler holds a
  disjoint `glue` field. A registry that held `&mut M` could never be reached
  from body compilation, because the compiler already holds that borrow.
  Interior mutability or a per-compiler cache was rejected: the former hides
  the ordering `finish()` checks, and the latter breaks sole authority.
  Defining glue mid-body in a fresh Cranelift context is safe; the capture
  envelope established that pattern.
- **D2 — release seams take a `ConcreteType`.** A non-concrete type at a
  release site is a located `CodegenError`, never a shallow dec. The one live
  exception is the type-keyed arm in `emit_release`, the one plan-drop release
seam. Its disposition belongs to
  [the non-concrete release contract](non-concrete-release-contract.md) §4 and
  §7.4, and is open under FIXME 0903.
- **D5 — emission order is input-dependent; behaviour must not be.** The first
  request for a type defines its body wherever that happens, so glue functions
  appear in varying order. Identity is the type, so this is harmless. Any
  observable order dependence is a defect.
- **D8 — the closure shape delegates.** M1's closure arm calls
  `emit_closure_dec_into` rather than duplicating its free path.

## 4. One release emitter, many releasing seams

`emit_typed_rc_dec` is the glue-call emitter. It converts the value's type to a
`ConcreteType`, requests that type's glue and emits one call. It has no
fallback arm and no caller-supplied `needs_guard`. The nullary-tag guard is a
property of the type and lives once inside the glue body (`guard_nullary`), so
no site can disagree with its type about how a value is released.

- **Environments.** Explicit lambdas, auto-curry and poll or launch
  continuations share one environment-body builder. Each capture descriptor
  carries its concrete type. An owning capture calls canonical glue; a closure
  box uses its embedded pointer. User-written and compiler-synthesised closures
  differ only in who supplies the capture list.
- **Vec.** Vec glue owns runtime iteration and delegates element discharge to
  canonical glue through M1's adapter over the established `vec_drop` callback
  ABI. `vec_drop` is an unconditional teardown, so the Vec shape goes through
  the rc-gated release; calling it directly would free a shared Vec.
- **ADT.** ADT glue branches on the runtime constructor and walks exactly that
  constructor's concrete substituted fields.
- **Every shape discharges fields only in the `old_rc == 1` branch.**

| Seam | Mechanism |
|---|---|
| Plan drops (death points, branch and arm entries, moves-off post-drops) | one `drop<T>` per binder through `emit_release`, plus D2's open non-concrete arm |
| Match scrutinee release at arm entry | one `drop<S>` |
| Read-only builtin operand release | one `drop<T>` after the read |
| ADT field walk | inside M1's generated body |
| Vec element release | M1's element adapter |
| Capture slot release | one `drop<T>` per owning slot, or the closure-box dispatch |
| Closure box release | `emit_closure_dec_into` (M5) |
| IO node release | M1's IO shape ([non-concrete release contract](non-concrete-release-contract.md) §5.4) |

### 4.1 The constructor-template admission — superseded record

**Superseded** by [the non-concrete release contract](non-concrete-release-contract.md)
§4 face 1 and §4.1, which own the live disposition. This record remains because
source rustdoc cites it.

- **What S118 ruled.** A constructor `Def` is compiled once per declaration, so
  a generic constructor template has a residual-typed field parameter. The
  guarded consuming increment on that parameter and the guarded scope-exit
  decrement were kept as a pair under invariant **I-CT**: every value the branch
  released had earlier been incremented and published into the box the frame
  returns, so the decrement never observes the last reference. The admission
  was to be keyed on the frame, not the type.
- **Why it fell.** Keying on the frame caused 16 hard refusals, because accessor
  and trait-instance frames reach the same arm. I-CT also proves only that the
  count balances: on a raw scalar at or above `NULLARY_TAG_THRESHOLD`, both
  halves are wild atomic writes. The replacement invariant I-CT′ is discharged
  by representation, and the source arm stays type-keyed until that contract's
  structural close (§3.4 D2).

## 5. Match-owned scrutinee protocol

Retired at S123 W2. The match owns its scrutinee; its arm-entry duplicates and
drop are the ownership plan's ([uniform counting](uniform-counting.md) §4).
Two rules from this section stay true and are owned there:

- **Category before ownership.** A release is owed only for a heap category.
- **No spelling is ownership authority.** An inline and a `let`-bound
  scrutinee plan identically.

## 6. TCO replacement/transfer predicate

Retired at S123 W2. A tail self-call releases nothing at the jump: every
reference is consumed before it ([uniform counting](uniform-counting.md) §2.3).

## 7. Seam records retained for their evidence

The migration's slice plan is Git history. These records remain because tests
and neighbouring designs cite them.

### 7.2 SList concatenation — attributed outside backend

The SList construction corruption (FIXME 0835) was attributed to the
primitives/intrinsics pair, not to type glue: `sconcat` deep-incremented its
right operand and balanced it with `consume_slist`, which stops at the first
shared node. The committed repros are `tests/slist_sconcat_ownership_0835.rs`,
and the pair's contract is
`design/runtime/s118-structural-embedding-ownership.md`.

**The discriminating recipe.** Count `allocs - deallocs` under
`CRANELISP_RC_STATS=1` against the number of applications:

- a residual growing with the right operand's length per call is the
  marshal/consume asymmetry;
- a residual tracking type nesting depth, or vanishing under glue migration,
  would be transitive discharge.

### 7.3 Match release is counted, not detected

An exact-balance instrument cannot see a double release of a value that was
going to be freed anyway. `--run` read balanced while `--link` aborted. Unit
cells therefore assert **exactly one** release call per arm on the scrutinee,
and the `--link` leg carries the release-exactly-once face
(`tests/match_owned_temporary_scrutinee_0810.rs`).

### 7.4 Capture and auto-curry teardown

Explicit and compiler-synthesised captures reach the same seam, so a fix to the
explicit `fn` path alone was never sufficient. Acceptance is the ownership-flow
generator balancing over every owning type under both analysis toggles, with no
exclusion for curried partial application (`tests/gen_ownership_flows.rs`), and
`tests/capture_drop_glue_strands_nested_heap_0760.rs`.

### 7.5 The non-concrete release arm

Making release type-directed surfaced the one class that cannot supply a
concrete type (§4.1). The arm remains type-keyed. A frame-keyed narrowing was
measured and reverted. FIXME 0891 is deferred on FIXME 0903, and the contract's
reject list forbids re-landing the frame key alone
([non-concrete release contract](non-concrete-release-contract.md) §8).

## 8. The atomic deletion condition (S118 arch ruling 10)

A canonical registry coexisting with the legacy inline emitter was an approved
transitional state. Its closure condition was that consumers migrate **and** the
legacy mechanisms delete in the same wave. It closed in S118. The deleted set
remains the standing reject list: a re-introduction of any of these is a
`/review` REJECT, and `tests/drop_glue_legacy_emitter_fence.rs` greps
production sources for the named seams.

**Deleted, in fence order:**

1. **The depth bound and its carrier** — `MAX_DROP_GLUE_DEPTH` and the
   `FnCompiler::drop_glue_depth` counter.
2. **The inline recursive emitter** — `emit_rc_dec_with_inline_drop_glue`,
   `emit_inline_drop_glue`, `emit_mixed_adt_heap_guard`,
   `emit_drop_glue_field_decs`, `emit_field_decs`, and the inline-only
   `build_adt_type_substitution`. The per-site `TypedRelease` /
   `typed_release_kind` classification is subsumed by the registry's shape
   classification, which keeps the Vec-before-ADT order rule.
3. **The second glue identity home (M3)** — `build_adt_drop_glue_fn`,
   `build_elem_dec_fn`, `adt_drop_glue_name` and `adt_instantiation_mangle`.

**Explicitly NOT deleted:** `emit_closure_dec_into` (M5); `emit_capture_dec_glue`
(M4, the capture-layout owner); `closure_drop_glue_name` and
`curry_drop_glue_name`, which name capture envelopes rather than type glue;
`substitute_type_inline` and `collect_var_ids_from_type`, which have other
consumers.

The fence asserts on symbol names, never line numbers.

## 9. Evidence

- **Solution tests.** `tests/transitive_drop_glue_s116.rs` covers depth and
  recursion, `tests/adt_drop_glue_underkey.rs` covers identity,
  `tests/mixed_arm_match_forward_0726.rs` and
  `tests/match_owned_temporary_scrutinee_0810.rs` cover match lifetimes,
  `tests/ms_p8_conj_leak.rs` and `tests/tco_tail_arg_alias_uaf.rs` cover TCO,
  and §7.4 names the capture tests. The legacy fence is §8.
- **Armed detectors.** Arming is scoped to child processes and uses an explicit
  environment allow-list, never a suite-global or `set_var` arming
  (`design/intrinsics/diagnostic-modes.md` §7.1).
- **Unit tier.** §10.

## 10. Unit-test design: submodule × complexity/edge/negative matrix

Cells sit beside the production owner (**Tests mirror module composition**).
Where a rule is pure, such as shape classification, the cell exercises the pure
function without a live `FnCompiler`. Cells assert
emitted call identity and control-flow order, not only text presence. Test
modules cite rows by position: the third row is the glue-call emitter, the
fourth the constructor template, the fifth the match seam and the sixth the
retired TCO predicate.

| Submodule | Complexity / positive | Edge | Negative |
|---|---|---|---|
| `drop_glue` identity | primitive-owning types; FQ ADT; two generic instantiations | repeated request is idempotent; one bare type name in two modules differs | non-concrete key rejected; collision witness; span/caller cannot alter identity |
| `drop_glue` registry/body builder | scalar leaf; ADT→String; ADT→Vec→ADT; depths 1/2/4/5/>5 | self-recursive nullary and data arms; mutual recursion; a repeated field type emits one body; permuted request order yields the same bodies and keys | no depth constant; no shallow fallback; duplicate definition and missing typedef fail loudly; `finish()` rejects a `Defining` entry |
| `rc_emission` glue-call emitter (`rc_emission/glue_call_emitter_tests.rs`, `drop_glue/vec_arm_rc_gate_tests.rs`) | owned heap pointer ⇒ exactly one call to the canonical symbol; the final-reference body releases fields then frees | mixed ADT nullary tag guarded inside the body, not at the site; closure field; empty Vec | no field call on `old_rc > 1`; no `needs_guard` parameter; a non-concrete type at a release site is a located error |
| Constructor-template admission — **superseded** by [the non-concrete release contract](non-concrete-release-contract.md) §4.1 | residual template parameters carry no RC operation (I-CT′); a concrete-field template takes the ordinary path | multi-field template: residual fields none, concrete fields ordinary | no guarded increment or decrement survives on a residual parameter |
| `match_codegen` | match counting is the ownership plan's; its cells are the plan's ([uniform counting](uniform-counting.md) §8) | — | — |
| TCO predicate — **retired** with §6 | — | — | — |
| `lib` compile orchestration | JIT and object request the same symbol set; the registry `finish()`es after bodies | recursive declaration finalises once; two callers share one body; result-root request is a superset | unresolved `Defining` at finalise is an error; no request after `finish()` |
| Capture and environment glue | explicit closure over Vec/ADT; auto-curry; nested closure; poll-state capture | zero captures; repeated same-typed captures | every owning capture has a glue call; no second skeleton per mirror |

The fourth row states the target. Its module cells were deleted at the S123
cutover; the contract's §4.1 discharge is by representation.

## 11. Quality attributes and constraints

- **Simplicity.** One type-keyed registry replaces the inline emitter, the
  second identity home and per-site guard negotiation. Complexity scales with
  distinct concrete owning types, not nesting depth or seam count.
- **Observability.** Construction failures name the concrete type and the
  missing definition or substitution. `/clif` shows a call to a named,
  type-derived symbol at every release site.
- **Concurrency.** Registries are per compilation, with no global state and no
  backend lock. Glue uses the RC atomicity policy of the release it replaces.
- **Performance.** One call per released outer owner and runtime traversal of
  exactly the owned graph, with no depth-proportional code. Glue inlining or
  specialisation waits for differential heap-balance evidence (**Complexity has
  a budget**).

**Reject criteria** (binding for `/review`):

- a depth constant, or any shallow fallback;
- a borrowed-builder clone of recursive emission;
- a seam-specific deep releaser (match, TCO, capture or construction);
- a second named-glue identity home;
- a JIT-only helper, a global registry, a type-erased releaser or a third
  header word;
- persisted process-local glue addresses, or a cache-schema change for glue;
- a fix covering explicit `fn` captures only;
- a per-spelling release rule at the match seam;
- a `needs_guard` parameter on a release seam;
- a detector armed outside a child-process allow-list construction.

Non-concrete releases add the reject list in
[the non-concrete release contract](non-concrete-release-contract.md) §8.
