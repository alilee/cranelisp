# Transitive drop glue and owned-value displacement

> **Owner**: `design`, narrow-deployed to `cranelisp-backend`.
> **Status**: current design, verified against source 2026-09-25. The S118
> consumer migration it once planned has landed.
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
| Scope cleanup, post-call cleanup | owned typed word | none | call `drop<T>` once |
| Closure, curry or poll-state capture teardown | owned capture slot | none | environment glue calls `drop<T>` for each owning capture |
| Constructor-pattern match on an owned temporary | wrapper owns its fields | arm bindings borrow fields unless protected or transferred | after the arm's last use, call wrapper `drop<T>` once; protect each escaping field first |
| Var-pattern match on an owned temporary | binding aliases the whole value | binding/body or none | transfer the one owner when forwarded; otherwise call `drop<T>` **exactly once** after the arm |
| TCO loop-slot replacement | old parameter slot owns `T` | next slot value or none | the §6 predicate decides; if replaced, call `drop<T>` before overwrite |
| Vec teardown | Vec owns each live element | none | the Vec body iterates the runtime length and calls element `drop<E>` |
| ADT teardown | box owns the fields selected by its runtime tag | none | the ADT body branches on tag and calls each field's glue |

The match rule separates *field survival* from *wrapper release*. Extraction
borrows by default. If an arm result or tail argument carries an extracted heap
field beyond the match, the backend protects it before wrapper teardown; only
then may the wrapper glue discharge its field reference. Inline and let-bound
scrutinees use the same plan. This prevents both the leak and the premature
free without trading one for the other.

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
  exception is the type-keyed arm in scope cleanup. Its disposition belongs to
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
| Scope-exit cleanup (`emit_heap_binding_decs`) | one `drop<T>` per binding, plus D2's open non-concrete arm |
| Let-scope tail flush | same shared body |
| Superseded parameter flush | same, gated by the §6 predicate |
| Match wrapper release | per-arm `drop<S>` (§5) |
| Moded-argument post-call release | one `drop<T>` |
| ADT field walk | inside M1's generated body |
| Vec element release | M1's element adapter |
| Capture slot release | one `drop<T>` per owning slot, or the closure-box dispatch |
| Closure box release | `emit_closure_dec_into` (M5) |
| IO node release | M1's IO shape ([non-concrete release contract](non-concrete-release-contract.md) §5.4) |

### 4.1 The constructor-template admission — superseded record

**Superseded** by [the non-concrete release contract](non-concrete-release-contract.md)
§4 face 1 and §4.1, which own the live disposition. This record remains because
source rustdoc and `ctor_template_admission_tests` cite it.

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

`compile_match` records the ownership answer once, before any arm, from the
provenance classification ([non-concrete release contract](non-concrete-release-contract.md)
§6.1). Each arm then resolves its own plan:

- `Borrowed` — the enclosing scope or callee owns the scrutinee; no wrapper
  release, and pattern bindings borrow.
- `OwnedForwarded` — this arm transfers the whole scrutinee (`[r r]`); this
  path emits no release and carries the one owner out.
- `OwnedConsumed` — this frame owns a temporary and this arm consumes it; the
  arm protects any extracted field that outlives the wrapper, then calls
  `drop<S>` once at the arm's lifetime end.

Rules that keep the plan sound:

- **Release is per arm.** A forwarding sibling never suppresses another arm's
  release. The whole-match `any arm forwards` predicate survives only as a
  provenance trace, never as a release gate.
- **One owner for both pattern kinds.** A var-pattern binder borrows a value
  the match frame owns for the arm's duration, exactly like constructor field
  bindings. It is never registered for scope cleanup. Registering it as well
  would release the same value twice; making the owner depend on pattern kind
  would restore the per-spelling rule this plan removes.
- **The COW exception travels per arm and keeps its polarity.** When the COW
  producer retained the returned pointer, this arm's release is its balancing
  decrement and fires even on a forwarding arm.
- **Category before ownership.** A release is owed only when the scrutinee is a
  heap category as well as owned.
- **No spelling is ownership authority.** An inline versus let-bound scrutinee
  changes nothing.

## 6. TCO replacement/transfer predicate

Both tail-jump flushes consult one pure predicate per old slot,
`tco_slot_disposition`, returning `TransferOldOwner | Replace | BorrowedInvalid`.

| New argument / state | Verdict | Old-slot action |
|---|---|---|
| Bare local `Var` resolving to that exact slot, including a legal cross-slot move | transfer | no release; move bookkeeping prevents a second owner |
| Control-flow expression (`(recur (if c lo hi))`) | replace | the branch tail's protective increment balances a uniform flush |
| Analysis-on in-place COW rooted at the slot | transfer | no release |
| Bare argument naming a borrowed inner shadow | `BorrowedInvalid` | a located compiler error; never a guessed release or a silent skip |
| Fresh construction, call, literal, copied COW result, unrelated variable or unknown provenance | replace | call `drop<T>` before overwrite |

- **The control-flow row must stay `Replace`.** Its bindings differ per
  branch, so a single static skip would keep the dead branch's binding alive.
  The protect-then-flush strategy is the use-after-free cure
  ([ownership codegen](ownership-codegen.md) §13.3).
- **The in-place COW row is analysis-on only and positional-blind.** With
  ownership analysis off, the COW always copies and the release is always owed.
  The predicate takes the toggle as an input rather than reading it twice.
- **The borrowed-shadow row (the fourth) means a shadowing borrow**, not merely
  a borrowed slot. A borrowed parameter carried forward as its own tail argument
  owes nothing.
- **Classification and release stay separate.** The predicate decides owner
  continuity; canonical glue performs the discharge. Unknown provenance is
  conservative replacement. This is **Narrowing carries its check**.

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
cells therefore assert **exactly one** release call per consuming arm on the
scrutinee, and the `--link` leg carries the release-exactly-once face
(`tests/match_owned_temporary_scrutinee_0810.rs`,
`compiler/match_codegen/scrutinee_ownership_tests.rs`).

### 7.4 Capture and auto-curry teardown

Explicit and compiler-synthesised captures reach the same seam, so a fix to the
explicit `fn` path alone was never sufficient. Acceptance is the ownership-flow
generator balancing over every owning type under both analysis toggles, with no
exclusion for curried partial application (`tests/gen_ownership_flows.rs`), and
`tests/capture_drop_glue_strands_nested_heap_0760.rs`.

### 7.5 The non-concrete scope-exit arm

Making scope cleanup type-directed surfaced the one class that cannot supply a
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
`match_forwards_scrutinee`, retained for a provenance trace only (§5);
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
Where a rule is pure — shape classification, the §5 plan and the §6 predicate —
the cell exercises the pure function without a live `FnCompiler`. Cells assert
emitted call identity and control-flow order, not only text presence. Test
modules cite rows by position: the third row is the glue-call emitter, the
fourth the constructor template, the fifth the match seam and the sixth the
TCO predicate.

| Submodule | Complexity / positive | Edge | Negative |
|---|---|---|---|
| `drop_glue` identity | primitive-owning types; FQ ADT; two generic instantiations | repeated request is idempotent; one bare type name in two modules differs | non-concrete key rejected; collision witness; span/caller cannot alter identity |
| `drop_glue` registry/body builder | scalar leaf; ADT→String; ADT→Vec→ADT; depths 1/2/4/5/>5 | self-recursive nullary and data arms; mutual recursion; a repeated field type emits one body; permuted request order yields the same bodies and keys | no depth constant; no shallow fallback; duplicate definition and missing typedef fail loudly; `finish()` rejects a `Defining` entry |
| `rc_emission` glue-call emitter (`rc_emission/glue_call_emitter_tests.rs`, `drop_glue/vec_arm_rc_gate_tests.rs`) | owned heap pointer ⇒ exactly one call to the canonical symbol; the final-reference body releases fields then frees | mixed ADT nullary tag guarded inside the body, not at the site; closure field; empty Vec | no field call on `old_rc > 1`; no `needs_guard` parameter; a non-concrete type at a release site is a located error |
| Constructor-template admission (`fn_compiler/ctor_template_admission_tests.rs`) — **superseded** by [the non-concrete release contract](non-concrete-release-contract.md) §4.1 | residual template parameters carry no RC operation (I-CT′); a concrete-field template takes the ordinary path | multi-field template: residual fields none, concrete fields ordinary | no guarded increment or decrement survives on a residual parameter |
| `match_codegen` (`match_codegen/arm_lifetime_plan_tests.rs`, `scrutinee_ownership_tests.rs`) | inline and let-bound owned temporary; constructor and var patterns; plan recorded once | field forwarded into a tail call; whole-wrapper forward; borrowed callee scrutinee; mixed constructor/var match, constructor path | no whole-match suppression; no release before protect; no borrowed-scrutinee release; exactly one release per consuming arm; var binder never registered for cleanup |
| `fn_compiler` TCO predicate (`fn_compiler/tco_slot_predicate_tests.rs`, `tco_shadowing_borrow_tests.rs`) | unrelated fresh replacement releases; bare-Vec and ADT replacement share a path | same-slot and cross-slot move; control-flow tail; analysis-on in-place COW; analysis-off copied COW | shadowing borrow is `BorrowedInvalid`; fresh or unknown cannot suppress release; no TCO-private glue; the control-flow row never becomes a skip |
| `lib` compile orchestration | JIT and object request the same symbol set; the registry `finish()`es after bodies | recursive declaration finalises once; two callers share one body; result-root request is a superset | unresolved `Defining` at finalise is an error; no request after `finish()` |
| Capture and environment glue | explicit closure over Vec/ADT; auto-curry; nested closure; poll-state capture | zero captures; repeated same-typed captures | borrowed capture not released; every owning capture has a glue call; no second skeleton per mirror |

The fourth row states the target. The landed cells in
`ctor_template_admission_tests.rs` still pin the S118 balance of the live
type-keyed arm; they change when that arm's disposition lands (§3.4 D2).

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
