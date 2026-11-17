# The compilation entry — `compile_to_module`

> **Owner**: `design`, narrow-deployed to `cranelisp-backend`.
> **Status**: current design, verified against source 2026-09-25; §12 at
> `4b58ab93`, 2026-11-17, with §12.1 designed and not yet landed.
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
- **fields** — allocate an ADT payload on the RC heap, store the tag and store
  each field. No site places a construction elsewhere: stack placement retired
  at S124 ([ownership codegen](ownership-codegen.md) §4).

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
4. **host-promised primitive** — lower the call exactly as direct application
   of that primitive does (§12.1), since it has no slot by construction;
5. **otherwise** — a GOT-indirect call through the uniform reference (§5.1).
   A target with no GOT carrier is a located error, never a name search.

Every wrapper parameter arrives owned and the wrapper's call consumes it, so
every code pointer reachable from a closure obeys the uniform consuming
convention ([RC discipline](ring2-rc.md) §3.1). No callee borrows, so there is
nothing to adapt. The wrapper body's counts, including the auto-curry
wrapper's captured arguments, are the forwarding template of
[uniform counting](uniform-counting.md) §3.3.

### 12.1 Host-promised primitives as values (ACT-1063, S124)

Spec §3.2.1 makes every function a first-class value, and the host-promised
primitives are functions: the IO combinators `bind`, `race`, `select` and
`sleep`; the Trace field accessors; `sconcat`; and `discover-tests`. Each is a
`RustPrimitive` entry whose life is `HostPromised`, which carries no GOT slot
by construction ([BC §7](../arch/bounded-contexts.md#7-cross-crate-types--cratescranelisp-types),
"callability is structural"). Direct application lowers each without a slot. The wrapper had no such rule, so a value use fell through to the GOT rule
and was refused.

- **Who owes it: this crate alone.** Read at `4b58ab93`: a value-position
  `bind` reaches the GOT rule with its carrier intact. The `Var`'s
  `VarRef::Global` storage key fetched the entry, since the callable gate and
  the arity read both answered from it, and the `Var`'s type is a
  `ConcreteType` by representation. The refusal asks for a GOT slot that the
  entry's life rules out. No producer owes a carrier, and typecheck's
  `ResolvedCall` is not needed: the storage key already names the entry
  (Principle 24).
- **Rule.** A wrapper whose target is a host-promised primitive lowers its one
  saturated call through the same lowering direct application uses. An IO
  combinator mints its IO node inline. A Trace accessor imports its intrinsic
  by ABI name, and every other host-promised entry imports its entry key by
  name. Both apply to the fn-as-value wrapper and to the auto-curry wrapper's
  builtin arm.
- **Partial application.** Of the family, `bind`, `race` and `sconcat` take
  two operands, so only they have a partial face; `sconcat`'s partial works
  today because its shim symbol exists. The curry builtin arm's last resort
  imports any unlisted builtin by its bare name. A bare import resolves
  against whatever the host process exports, not against an entry. A partial
  `bind` therefore does not fail at finalisation: it links, and aborts at run
  time on a misaligned pointer (observed by `qa`). That it links to the C
  library's socket `bind`, whose integer result is read as an IO node, is a
  source reading. `race` resolves to nothing, so JIT finalisation panics the
  compile worker. Rule 4
  removes both faces for this family. The curry builtin arm also loses the
  bare-name fallback. Its rules are inline Vec primitive, host-promised
  (rule 4), extern shim, then GOT slot (rule 5). A name that none of them
  claims is a located internal error, not a symbol lookup. That makes a
  collision with a host-process symbol unconstructable for every name, not
  just avoided for this family.
- **One lowering per primitive** (Principle 07). The combinator
  classification (`IoCombinator`), the IO node layouts, the disposer
  derivation and the Trace accessor ABI mapping each keep one home. Both the
  direct call and the wrapper reach them; the wrapper holds no copy. The
  combinator classifier is asked of the wrapper target's resolved storage
  symbol, under the same rule as the `BuiltinFn` carrier's name: identity
  comes from resolution, never from the written spelling. A local `bind` is a
  scope-stack value and never reaches this rule. A user `bind` resolves to its
  own entry.
- **The wrapper's builder.** The lowering emits into the wrapper's function,
  not the enclosing body. `dev` chooses between two realisations: an inner
  body compiler over the wrapper's builder, as lambda bodies have, which
  compiles no expression and consults no plan; or lowering cores parameterised
  by the builder. A copy of a lowering written for the wrapper is not
  admissible. That is how the curry arm's private list of extern primitives,
  `is_extern_primitive_in_wrapper`, drifted from `is_extern_primitive`.
- **Disposer type.** An IO combinator's result disposer is derived from its
  first operand's concrete type. Direct application reads that operand's
  expression type. The fn-as-value wrapper reads the first parameter of the
  value site's concrete `Fn` type. The curry wrapper reads its first applied
  argument's type. All three are `ConcreteType`s already, so no derivation
  meets a type variable.
- **Counts unchanged.** Host-promised primitives consume every argument (BC §3
  invariant 2). An IO combinator's node takes its owned operands, and a race
  takes both through its branch Vec. The forwarding template therefore stays
  the wrapper body's only RC emission
  ([uniform counting](uniform-counting.md) §3.3).
- **Totality, structural.** Rule 4 is selected by matching the fetched entry's
  life exhaustively. A new slot-less life or host-promised lowering then fails
  to compile until the wrapper decides its rule, instead of reaching rule 5.
  After this, rule 5's refusal is reachable only when a slot-carrying entry
  has lost its slot. That is an internal invariant failure, and its text is
  worded as one rather than naming a carrier
  ([REPL §5.5](../../repl/spec/05-error-presentation.md)).
- **Extent, observed by `qa`** ([evidence delta](../../tests/plan/s124-evidence-delta.md)
  §3.9, REPRO-1063 and REPRO-1063-p). As values, `bind`, `race`, `select`,
  `sleep`, `nanos`, `name`, `sconcat` and `discover-tests` are refused at
  rule 5. The other three Trace accessors are refused by source reading only.
  A partial `(bind io)` compiles, links and aborts on a misaligned pointer in
  `--run`, the REPL and the linked executable. A partial `(race a)` panics the
  compile worker. `quote-sexp` carries a slot, so it is outside this family
  and works as a value.
- **Not covered.** The direct call's unrecognised-builtin arm
  (`compile_platform_or_direct_extern_call`) keeps its by-name extern
  fallback, and no program is known to reach it. A host promise that int
  fails to keep still panics at finalisation instead of returning a located
  error. Neither has been observed. The trigger for designing either is a
  program that reaches it.
- **Falsifier.** The design is falsified if any REPRO-1063 or REPRO-1063-p
  leg fails once rule 4 lands. It is also falsified if a value use or partial
  application emits an IO node whose tag, fields or disposer differ from the
  direct application's (T-1063-b, M-1063).

## 13. Evidence

- Entry contract, object mode, target collection and GOT emission:
  `crates/cranelisp-backend/src/module_assembly_tests.rs`.
- Slab stability and bounds: `crates/cranelisp-backend/src/got_slab_tests.rs`.
- Per-member failure attribution: §15.
- Constructors: §2.6.6.

## 14. Open points

- `load_object` has no production caller (§10).
- The cache packet API has no live consumer ([module caching](module-caching.md) §7).

## 15. Failure attribution

When one member of a batch fails, the error names that member's module and
executable label. The attribution is attached at the body loop, where the
identity is in hand, and the original cause and location pass through
unchanged; the helper must not format and re-parse either. A later-member
failure may leave declarations inside the caller-owned, unpublished module,
but it cannot publish a function pointer to the live GOT, so the backend gains
no rollback, retention or transaction responsibility.

- **Rejected sources of the identity**, each a second resolver for a fact the
  loop already has: the failing body's callee or punctuation, a "last name"
  side channel, a scan of the requested names or symbol tables, message
  parsing in the backend or the binary, and a new error variant or shared
  carrier to hold it.
- **Out of scope:** a non-body batch error (target collection, declaration)
  keeps the generic conversion and is not attributed by the body helper.
- **Unit scenarios** (`module_assembly_tests.rs`, through production
  `compile_to_module`): a later member failing after an earlier success is
  attributed to the later member with its original source location, never to
  the cause's callee; reversing the names moves the attribution with the
  failing member; a single-name failure attributes the same way; a non-body
  error stays unattributed; the success control is unchanged; and in JIT mode
  the live GOT values are unchanged after the failure.

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
