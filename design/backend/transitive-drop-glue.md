# Transitive drop glue and owned-value displacement

**Status:** DESIGN — Sprint 116 Phase 3. **Subordinate to:** `backend.md`.
**Architecture inputs:** `design/arch/safety-invariants.md` R15 and
`design/arch/bounded-contexts.md` §4b invariant 16. This document resolves the
backend design obligations in FIXMEs 0760 and 0796 and supplies the common
mechanism required by the 0810/0835 and 0688 implementation waves. The defect
FIXMEs remain open until implementation and source verification.

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

The universal heap header remains two words. Glue identity comes from the static
concrete type; no type id or function pointer is added to ordinary allocations.
Closure boxes retain their existing embedded capture-glue pointer because the
capture tuple is closure-instance shape rather than a language type carried in
the header.

## 2. Actors and lifetime events

| Actor / event | Value before event | Owner after event | Required action |
|---|---|---|---|
| lexical/scope cleanup, post-call cleanup | owned typed word | none | call `drop<T>` once |
| closure/curry/poll-state capture teardown | owned capture slot | none | generated environment glue calls `drop<T>` for every owning capture |
| constructor-pattern match on owned temporary | wrapper owns its fields | arm bindings borrow fields unless explicitly protected/transferred | after the arm's last use, call wrapper `drop<T>` once; protect each escaping field before that call |
| var-pattern match on owned temporary | binding aliases the whole value | binding/body or none | transfer the one owner when forwarded; otherwise call `drop<T>` once after the arm |
| TCO loop-slot replacement | old parameter slot owns `T` | next slot value or none | one replacement/transfer predicate decides; if replaced, call `drop<T>` before overwrite |
| Vec element teardown | Vec owns each live element | none | Vec body iterates runtime length and calls element `drop<E>` |
| ADT teardown | box owns fields selected by runtime tag | none | ADT body branches on tag and calls each field's glue |

The match rule deliberately separates *field survival* from *wrapper release*.
Extraction is borrowing by default. If an arm result or tail argument carries an
extracted heap field beyond the match, backend emits the existing protective
increment/transfer before wrapper teardown; only then may wrapper glue discharge
its field reference. Inline and let-bound scrutinees use this identical lifetime
plan. This cures both 0810 polarities without choosing leak over premature free.

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
schema does not change: no serialized carrier or heap layout changes. A cache
format/compiler fingerprint already invalidates objects across this codegen
change. Forbidden alternatives are: a GOT slot (glue is not language-callable
or redefinable), arbitrary public JIT-symbol lookup, a serialized address or
artifact map, a cache-schema bump for this carrier, a second compile entry,
private compile-after-cache-miss glue, a JIT-only helper, a generic type-erased
releaser, or a heap/C-ABI change. These choices apply **Single
pipeline, mode parameters**, **Testability is structural**, and **Parallel
development is a first-class constraint**.

## 4. One release emitter, many releasing seams

`emit_typed_rc_dec` becomes a thin glue-call emitter: classify non-owning/value
representations as no-op, apply the existing mixed/nullary guard where the
concrete ADT representation requires it, and call the canonical glue for an
owned heap pointer. It does not recursively inspect ADT fields itself.

Environment glue (explicit lambdas, auto-curry, poll state and future capture
sets) is generated from one environment-body builder. Each capture descriptor
contains its concrete type and ownership disposition; owning captures call the
canonical type glue. This folds 0796 by construction: user-written and
compiler-synthesised closures differ only in who supplies the capture list.
Three copied drop-glue skeletons or a special explicit-`fn` repair are rejected.

Vec glue owns runtime iteration but delegates element discharge to the same
canonical glue identity. Closure-typed fields call the closure box's embedded
environment glue after their outer RC reaches zero. ADT glue branches on the
runtime constructor and walks exactly that constructor's concrete substituted
fields. Every path performs field discharge only in the `old_rc == 1` branch.

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

## 7. Unit-test design: submodule × scenario matrix

Tests mirror module composition (**Tests mirror module composition**); `/dev`
places them beside the production owner rather than in one omnibus fixture.

| Submodule | Complexity / positive cells | Edge cells | Negative cells |
|---|---|---|---|
| `resolution` / glue identity | primitive-owning types; FQ ADT; two generic instantiations | repeated request is idempotent; same bare type name in two modules differs | non-concrete key rejected; collision witness; span/caller cannot alter identity |
| glue registry/body builder | scalar leaf; ADT→String; ADT→Vec→ADT; depths 1/2/4/5/>5 | self-recursive list nullary/data arms; mutually recursive declarations; repeated field type emits one body | no `MAX_DROP_GLUE_DEPTH`; no shallow fallback; duplicate definition and missing typedef fail loudly |
| `rc_emission` | final ref calls fields then dealloc; non-final ref touches no fields | mixed ADT nullary tag; closure field; empty Vec | no field call on `old_rc > 1`; no deep owner routed to bare dec |
| capture/environment glue | explicit closure over Vec/ADT; auto-curry equivalent; nested closure | zero captures; repeated same typed captures; poll-state capture | borrowed/non-owning capture not dropped; every owning capture descriptor has a glue call |
| `match_codegen` | inline and let-bound owned temporary; constructor and var patterns | heap field forwarded into tail call; whole-wrapper forward; borrowed callee scrutinee | no whole-match `any` suppression; no release-before-protect; no borrowed scrutinee release; exact one release per consuming arm |
| `fn_compiler` / TCO | unrelated fresh replacement releases; bare-Vec and ADT replacement use same path | same-slot and cross-slot move; control-flow forward; analysis-on in-place COW; toggle-off copied COW | borrowed alias cannot license transfer; fresh/unknown cannot suppress release; no TCO-private glue |
| `lib` compile orchestration | JIT and object request the same symbol set | recursive declaration finalizes once; two callers share one body | unresolved `Defining`/undeclared glue at finalize is a compilation error |

Unit tests assert emitted call identity and control-flow ordering, not only text
presence. E2e acceptance remains `/qa`/`/testing`'s S116 matrix: exact balance,
value preservation, both ownership toggles, run/link representatives, recursive
termination, and removal of 0796's generative exclusion.

## 8. Quality attributes and constraints

- **Simplicity / maintainability:** one type-keyed body registry replaces inline
  recursive emission and the capture/curry mirrors. Complexity is proportional
  to distinct concrete owning types, not syntactic nesting depth.
- **Observability:** construction failures name concrete type, requesting
  function and missing definition/substitution. No silent fallback exists.
- **Concurrency-safety:** registries are compilation-local; generated glue uses
  the same RC atomicity policy as the owning release it replaces.
- **Performance:** one call per released outer owner and runtime traversal of
  exactly the owned graph. No depth-proportional code expansion. Optimization or
  glue inlining is out of scope until differential heap-balance evidence exists.
- **Testability:** identity and registry state are pure/unit-testable; each
  lifetime seam has positive, edge and negative unit cells.

**No-interim constraints:** no raised depth constant; no shallow fallback; no
borrowed-builder clone of recursive emission; no 0835-, 0810-, capture-, or
TCO-specific deep releaser; no JIT-only helper; no third heap-header word; no
global glue registry; no generic type-erased release; no cache sidecar carrying
process-local glue addresses; and no implementation that fixes only explicit
`fn` captures while leaving compiler-synthesised environments behind.

## Next skills

- `/arch` — author the exact `drop_glue_symbol_name` implementation contract and
  verify the approved `DropGlueArtifact` / `CompilationArtifacts.drop_glues`
  public-baseline delta during the implementation wave.
- `/qa` — reconcile this per-arm match plan and the replacement predicate with
  the S116 matrix; add any missing negative integration cells.
- `/dev` (backend) — implement serially: registry/named glue first, then 0835,
  match, capture/curry, and TCO migration; add the unit matrix with each slice.
- `/review` (backend) — reject any surviving inline depth fallback or private
  releasing mechanism after each implementation slice.
