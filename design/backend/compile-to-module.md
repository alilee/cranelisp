# The compilation entry — `compile_to_module`

> **Owner**: `design`, narrow-deployed to `cranelisp-backend`.
> **Status**: current design, verified against source 2026-09-25.
> **Authority**: `design/arch/bounded-contexts.md` §3 owns the boundary and its
> invariants; the rustdoc in `crates/cranelisp-backend/src/lib.rs` owns the exact
> signatures. This document explains how the one entry is organised and why.
> Section numbers are cited by source and tests, so unused numbers are skipped
> rather than renumbered.

## 1. What the entry is

`compile_to_module` is the only place the backend emits Cranelift IR. It
compiles a caller-chosen set of executable targets from one module into a
caller-supplied Cranelift `Module`, publishes each compiled address into the
target's GOT slot, and returns the introspection byproducts.

- **One path for every mode.** Fresh JIT batches, REPL evaluation, cache
  objects and `--link` objects all call it. The emitted CLIF is identical in
  each case ([JIT/object convergence](jit-object-convergence.md)).
- **Mode is the `Module` instance.** A `JITModule` and an `ObjectModule` differ
  only in how they finalise and resolve the per-module GOT symbol (§5, §9.1).
  There is no mode parameter, environment trait or wrapper entry.
- **It decides nothing it could be told.** Targets, bodies, identities and
  ownership summaries arrive resolved on the symbol tables ([backend master](backend.md) §2).

The public codegen surface around it is small: `load_object` (§10),
`produce_disasm` (§11), `build_isa` and the `Jit` construct boundary. Their
exact shape is the crate-root rustdoc.

## 2. The entry contract

### 2.1 Inputs

| Input | Meaning |
|---|---|
| Module path | The one module whose targets are compiled. |
| Targets | Exact `CallableTarget` values, each an executable arm owned by that module. |
| Symbol tables | The shared concurrent map. It is the single source for bodies, schemes, GOT slots, constructor metadata and callee identity. |
| Cranelift module | The emission target, exclusively borrowed for the call. |
| CLIF capture flag | Whether to render CLIF text into the returned artefacts (§8). |

The entry is generic over the symbol table's code and linker stores and never
names or constructs either (§2.5).

### 2.2 What the caller does not supply

The backend derives each of these internally, so no caller can supply a
disagreeing copy:

- intrinsic function identities — declared on the module (§6);
- bodies, parameter types and ownership summaries — read from each target's
  concrete realization (§4);
- arities — from each target's own parameters or, for a callee, its keyed entry;
- GOT slot assignments — from the symbol table;
- GOT base addresses — never a compile-time value (§5);
- function labels and linkage — derived per target (§7).

### 2.3 Caller obligations

- **JIT callers construct the module through `Jit::new(symbol_tables)`.** That
  one constructor registers every symbol the emitted code imports: intrinsics,
  each module's `__cranelisp_got_{M}` base and platform effects. Host-promised
  externs are added through `Jit::define_symbol`.
- **Object callers need no pre-registration.** Imports remain relocations.
- **Targets must come from the owning table's `codegen_targets()`
  projection** (BC §3 invariant 4). A target outside it is an error (§16).

### 2.4 No internal fork

The body never inspects which `Module` it holds. Every mode difference is a
method on the `Module` implementation or its `CodeFinalizer` capability (§9.1).

### 2.5 Caller finalisation and lifecycle ownership

- **Object mode.** The backend does not produce bytes. The caller calls
  `finish().emit()` on the object module after the entry returns and writes the
  result. There is no separate object-compile entry; that keeps mode out of the
  entry point.
- **JIT mode.** The backend finalises internally (§9.1.1) and writes GOT slots,
  but it never owns the `Arc<Jit>`. The caller composes `Code::Jit` from the
  `Jit` it owns and publishes it; the cache-hit path composes `Code::Linker` the
  same way. `Code` carries lifecycle only; the GOT is the single home of
  callable addresses (BC §3 invariant 3).

### 2.6 Constructor codegen

A constructor is an ordinary callable `Def` whose `DefKind::Constructor`
carries its type, tag and field count. Typecheck synthesises its body as a
single `ConstrADT` node. The backend reads the constructor metadata by one keyed
fetch (`CtorMeta`); pattern matching reads the same tag.

#### 2.6.1 One construct operation, several call shapes

`emit_adt_construct(tag, field values)` is the single construct emitter:

- **no fields** — the value is the bare tag (`iconst`); nothing is allocated,
  preserving the `NULLARY_TAG_THRESHOLD` contract;
- **fields** — allocate an ADT payload, store the tag and store each field.
  Only the allocation varies: a saturated inline site may place a proven
  non-escaping aggregate in a stack slot ([ownership codegen](ownership-codegen.md) §4).

Every construction reaches it:

| Shape | Lowering |
|---|---|
| Saturated application `(Some 3)` | Inline at the call site, with no call frame. This is the constructor analogue of inline primitives. |
| Nullary reference `None` | Folds to the tag at the variable site. |
| The constructor's own body | `compile_constr_adt` compiles the synthesised `ConstrADT` node into the constructor function. |
| Wrapper body that needs no call | A borrowed-builder form performs the same construction inside a generated wrapper (§2.6.2). |

A data-constructor *reference* is not special-cased at the variable site. It
falls through to the generic function-as-value path (§12).

#### 2.6.2 Constructor as a value

`(map Some xs)` builds a zero-capture closure through the ordinary
function-as-value path. Its wrapper body chooses by what is known:

1. the constructor function is in this compilation unit — a direct call;
2. otherwise the keyed constructor metadata is present — construct inline in the
   wrapper. This covers primitive constructors such as `Some`, whose GOT slot
   does not hold a callable constructor body, and constructors from other
   modules.

The wrapper therefore never calls a constructor through the GOT.

#### 2.6.3 Value-flattened constructors

A single-constructor type flattened to a bare word constructs by moving its
field, with no allocation. The inline site, the synthesised body and the
wrapper consult the same `value_construct` decision. If they disagreed, a heap
pointer would be matched as a bare word ([ownership codegen](ownership-codegen.md) §7).

#### 2.6.4 Reference-counting contract

`emit_adt_construct` is **RC-neutral**: it stores the field values it is given.
Callers produce those values under the uniform consuming convention
(`compile_consuming_arg_list`): a non-last-use heap variable is incremented and a
last use or temporary is transferred. Adding an increment inside the construct
operation would double-count at the inline site.

#### 2.6.5 Upstream production

The backend consumes constructor `Def`s and their slots; it produces neither.
Typecheck registers and slots constructors and int batches their targets, as it
does for any callable. Constructor-as-value runs end to end in `--run` and
`--link` (`tests/ctor_as_value.rs`).

#### 2.6.6 Evidence

- Crate unit: `compiler/control_flow/fn_as_value/value_use_tests.rs` compiles a
  constructor and a consumer that binds it as a value. It is the guard that the
  generic function-as-value path replaced the deleted bespoke constructor
  wrapper.
- Solution: `tests/ctor_as_value.rs` covers a user constructor to a
  higher-order function, a primitive constructor bound with `let`, and the
  composed IO form, each in both execution modes.

## 3. Phase order

One invocation runs these phases in order:

1. Declare intrinsics on the module (§6).
2. Collect targets and their concrete bodies (§4).
3. Declare every target function (§7).
4. Request drop glue for each body's result root
   ([transitive drop glue](transitive-drop-glue.md) §3.3).
5. Compile bodies. Release seams request further glue as they need it.
6. Fence the glue registry: every requested glue body is defined.
7. Emit the per-module GOT data symbol (§5.4).
8. Finalise (§9.1.1).
9. Project glue addresses into the artefacts (§8).
10. Publish each compiled address into its GOT slot (§9.1.3).

A failure in phases 1–8 publishes nothing (§9.1.4).

## 4. Target collection

The backend compiles exactly the targets it is handed:

- **No expansion.** An overload arm, a monomorphic instance or a
  default-method instance is already a separate executable arm with its own
  concrete body. The backend never splits a multi-signature definition.
- **No template filtering.** A constrained or generic template is not a codegen
  target; typecheck's `codegen_targets()` projection omits it (BC §3 invariant 4).
  The backend does not scan the table to exclude templates.
- **One body source.** Each target must be a `Life::Concrete` arm realised as a
  body. Its typecheck-built codegen view supplies the concrete body and ownership
  summary. The backend has no rebuild from untyped syntax; a missing view is a
  producer gap and an error (§16).
- **The selected arm owns the parameter types.** Generated overload and macro
  labels are not table bindings, so types come from the arm's scheme, never a
  later lookup by label.

## 5. GOT references

### 5.1 The reference site

Every GOT-indirect call or load emits the same three steps: import the target
module's `__cranelisp_got_{M}` as a `Linkage::Import` data symbol, take its
address with `global_value`, and load `base + slot × 8`. The slot comes from the
callee's keyed entry. The data-symbol name is the types-owned
`got_data_symbol_name`; the backend forwards to it and must not re-derive it.

### 5.2 Two resolvers, one reference

- **JIT.** `Jit::new` resolves each `__cranelisp_got_{M}` to that module's live
  table base, the redefinition swap target.
- **Object.** The symbol stays a relocation. The in-process cache linker or the
  system linker resolves it against the data symbol the defining module's own
  object exports (§5.4).

[Per-module GOT](per-module-got.md) owns the two-GOT model.

### 5.3 Why the reference is uniform

A per-mode reference would be two emission paths that can drift (Principle 7;
Principle 11). Uniformity also makes GOT emission testable with any `Module`,
without mode scaffolding (Principle 5).

### 5.4 The per-module GOT data definition

`CodeFinalizer::define_module_got_data` defines the module's own GOT slab:

- **JIT: no-op.** The live table is defined outside the module by `Jit::new`.
- **Object: an exported, writable, 8-byte-aligned data symbol.** It holds
  explicit zero bytes plus one function-address relocation per compiled target
  at `slot × 8`.
  - The slab is sized to the larger of the fixed runtime `GOT_TABLE_SIZE` and
    the module's highest live, target or retired slot plus one. The `(trace …)`
    GOT swap copies a fixed `GOT_TABLE_SIZE` words in every mode, so a smaller
    object slab would be read past its end.
  - It is writable because the trace swap writes into it.
  - It uses explicit zero bytes rather than zero-fill, because the macOS linker
    faults applying relocations to a zero-fill section.
  - A relocation slot beyond the declared count is an error, never a
    truncation.

## 6. Intrinsic declaration

The entry declares every intrinsic in the catalogue as an imported function on
the supplied module, one catalogue for both modes. `runtime/dealloc` is
mandatory: drop-glue emission and every compiled body depend on it, and its
absence is a codegen error. The resolved identities seed the function map
before any target is declared.

## 7. Function labels and linkage

Each target is declared under its executable label with `Linkage::Local`,
uniformly across modules.

- **Why local suffices.** Every call is GOT-indirect, including calls within a
  module (redefinition correctness), so no function symbol is referenced across
  objects. Exporting function symbols would only pollute the linked symbol
  table.
- **No entry-module special case.** The linked program's `main` alias is int's
  (BC §3 invariant 7).
- **Labels stay private to the backend.** Integration crosses back with
  semantic `CallableTarget` values, never label spellings (§10).
- **Glue is the exception.** Drop glue is exported under the types-owned
  per-module name because cache-hit and linked execution locate it by symbol
  ([transitive drop glue](transitive-drop-glue.md) §3.3).

## 8. Returned artefacts

`CompilationArtifacts` is returned by value on every successful call. It is
non-exhaustive, so additions do not break callers.

| Field | Content |
|---|---|
| CLIF text | Each compiled function's CLIF, joined. It is empty unless the caller asked for capture. |
| Code size | The sum across the compiled set. |
| Compile duration | The whole call. |
| Drop glues | Each canonical glue body emitted, keyed by concrete type, with its symbol and, in JIT mode, its finalised address. |

- **Capture is caller-selected.** Int requests CLIF only while introspection is
  live, so batch runs skip rendering. The `CRANELISP_CODEGEN_DUMP` stderr dump
  has its own trigger and renders matching functions regardless.
- **Disassembly is not an artefact.** It is re-derived on demand (§11).
- **The backend never writes introspection.** Placement belongs to the caller
  (`design/arch/d1-introspection-repl-only.md`).
- Per-function byproducts pass through a crate-private carrier before
  aggregation; no per-function artefact type is public.

## 9. Finalisation and publication

### 9.1 The `CodeFinalizer` capability

`cranelift_module::Module` exposes neither finalisation nor finalised-pointer
reads. `CodeFinalizer` adds them as a capability of the implementation, so mode
differences stay on the `Module` rather than becoming a parameter. Any new
`Module` target must implement it.

#### 9.1.1 Finalise

The entry finalises once, after every body and the GOT data are defined. JIT
finalisation patches relocations and makes pages executable. Object
finalisation is a no-op; bytes are produced by the caller's later `finish()`.

#### 9.1.2 Read addresses

After finalisation, JIT mode returns each function's address. Object mode
returns none. The capability is module-wide, so the first absent address ends
the publication loop.

#### 9.1.3 Publish into the GOT

For each compiled target with a slot, the entry stores the finalised address
into that module's table (`store_slot`). This is the one production write of a
freshly compiled address. It then emits a `JitWrite` event to the GOT observer,
if one is registered ([backend master](backend.md) §5).

#### 9.1.4 Failure before publication

Any error before the publication loop returns without writing a slot. The
caller-owned module may retain declarations or definitions, but it is
unpublished and the caller discards it. The backend therefore needs no rollback,
retention or transaction step. The publication loop itself has no failure path.

#### 9.1.5 Relationship to the cache

The entry is cache-ignorant. A cache hit does not call it: int maps the cached
object and publishes the linker's addresses ([module caching](module-caching.md) §8).
The object compiled for the cache comes from this same entry, so a restored
module runs the same code a fresh compile would.

#### 9.1.6 Object-mode behaviour

`ObjectModule` has no runtime address. Finalisation is a no-op, no address is
read, no slot is written, and glue artefacts carry no address. The caller emits
the bytes (§2.5). The same entry body runs; the capability's absent address is
what skips publication.

## 10. Cache-hit loading

The live cache-hit path is `cache::load_cached_object`. It maps a cached object
into a caller-prepared `Linker` and returns one address per semantic
`CallableTarget`; [module caching](module-caching.md) §8 states its rules.

The crate-root free function `load_object` builds its own linker, loads object
bytes and returns a `LinkerArtefact` keyed by binding name. It registers no
externals and has no production caller. Keeping, wiring or removing it is an
inter-crate public-API decision for `arch` and the user.

## 11. On-demand disassembly

`produce_disasm` disassembles one callable on request, for the REPL `/disasm`
command. It reads the live address from the callable's GOT slot, so it serves
fresh and cache-restored code alike. The caller passes back the code size it
received in the artefacts, so the backend does not persist a size. A slot-less
or unpublished callable is `SymbolNotCompilable`. Disassembly costs far more
than CLIF capture, which is why it is not an artefact.

## 12. Function values

A function used as a value becomes a closure over a generated wrapper body. The
wrapper's call follows the first applicable rule:

1. **target in this compilation** — a direct call;
2. **constructor** — construct inline (§2.6.2);
3. **inline Vec primitive** — emit the operation inline, since it has no slot;
4. **otherwise** — a GOT-indirect call through the uniform reference (§5.1).
   A target with no GOT carrier is a located error, never a name search.

When the target's ownership summary is not conservative, the wrapper adapts the
call to the uniform consuming convention. Every code pointer reachable from a
closure therefore obeys that convention
([ownership codegen](ownership-codegen.md) §3.5).

## 13. Evidence

- Entry contract, object mode, target collection and GOT emission:
  `crates/cranelisp-backend/src/module_assembly_tests.rs`.
- Slab stability and bounds: `crates/cranelisp-backend/src/got_slab_tests.rs`.
- Per-member failure attribution: [failed-member attribution](s117-failed-member-attribution.md) §5.
- Constructors: §2.6.6.

## 14. Open points

- `load_object` has no production caller (§10).
- The cache packet API has no live consumer ([module caching](module-caching.md) §7).

## 15. Failure attribution

When one member of a batch fails, the error names that member's module and
executable label. The attribution is attached at the body loop, where the
identity is in hand, and the original cause and location pass through
unchanged ([failed-member attribution](s117-failed-member-attribution.md)).

## 16. Error contract

Every refusal is a located `CodegenError` or `CompilationError`. None
silently skips a target.

### 16.1 Missing module table

The module path has no symbol table.

### 16.2 Foreign or unsupported target

The target belongs to another module or is not an executable arm of this one.

### 16.3 Empty compilation

The collected target set is empty.

### 16.4 No concrete body

The target is not a concrete body realization, or its body is absent. The
backend has no fallback synthesis: a codegen-reached arm without a body is a
typecheck producer gap. A silent skip would publish no address for a callable
others may call, and a panic would stop the process on a recoverable wiring
error.

## 17. Related designs

- `design/arch/bounded-contexts.md` §3 — boundary and invariants.
- `design/arch/concrete-boundary-type.md` — the concrete typed body.
- `design/arch/backend-keyed-consumer.md` — resolved identity carriers.
- [Per-module GOT](per-module-got.md), [module caching](module-caching.md),
  [executable generation](executable-generation.md),
  [transitive drop glue](transitive-drop-glue.md).
