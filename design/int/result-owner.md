# Program-result ownership and typed-context exit

**Status:** DESIGN — Sprint 116 Phase 3. **Subordinate to:** `int.md`.
**Scope:** the Binary/int surface (`src/` + `crates/cranelisp-exe-bundle/`) only.
**Architecture inputs:** `design/arch/safety-invariants.md` R15,
`design/arch/bounded-contexts.md` §4b invariant 16 and §6,
`design/arch/interfaces.md` §“Type-drop glue identity and address boundary”, and
Sprint 116 architecture ruling 9. This resolves the design obligation in FIXME
0745; the FIXME remains open until implementation and verification.

## 1. Binding outcome: observe, then release

Every successful execution result crosses from generated typed code into exactly
one **program-result owner**. That owner carries the pair `(value: i64, ty: Type)`
from the program driver through the result's final observation, then releases the
value exactly once through backend's named glue for its concrete owning type.

The semantic protocol is:

1. The driver returns a word and its caller preserves the static result type. If
   the source return type is `IO a`, the driver consumes the IO protocol tree and
   transfers the `Pure` payload; the owned result type is the inner `a`, not
   `IO a`.
2. Int classifies the result once. A scalar/value-layout result needs no release.
   An owning result is narrowed once with `ConcreteType::from_type`; failure is a
   typed-context invariant error, never permission to shallow-dec or leak.
3. The owner observes the live value: REPL formats it, while run/link converts it
   to the process exit code (`Int` narrows to `i32`; every other type yields 0).
4. Only after that observation completes, the owner invokes the canonical
   `extern "C" fn(i64)` glue selected by `(emitting module, ConcreteType)`.
5. The owner then relinquishes the word and may exit or return. No downstream
   carrier contains an owned copy.

This ordering is unconditional for owning values. Display failure, conversion
success, and non-`Int` exit conversion do not waive release. Runtime-error and
dispatch-fault outcomes carry no successful result owner and therefore invoke no
result glue. A glue failure is an internal safety failure and is not recovered by
calling glue again.

The protocol applies to plain heap results and to arbitrarily nested payloads.
Int never traverses the value. Backend's per-concrete glue owns transitive
discharge, so `String`, `Vec String`, an ADT containing a Vec of ADTs, closures,
and recursive finite values all use the same one-call int protocol.

This is the int manifestation of **Single pipeline, mode parameters** and **No
interim implementations of later-ring capabilities**: there is no JIT-only
releaser, IO-only payload branch, display-owned dec, shallow fallback, or private
copy of backend's glue behavior.

## 2. Representation and ownership states

The implementation should model the successful result as an int-private owner,
not continue passing a copyable `(i64, Type)` tuple through unrelated helpers.
The conceptual state machine is:

```text
DriverOutcome
  ├─ error/trap ───────────────────────────────> no result owner
  └─ clean + static Type
       -> OwnedProgramResult { value, concrete/value disposition, release target }
       -> observed (display or exit conversion)
       -> released/no-op
       -> consumed
```

`OwnedProgramResult` is an int-private representation; its exact Rust spelling is
for `/dev`, but these properties are binding:

- construction consumes the clean `ProgramOutcome` value and the carried source
  `Type`;
- `IO a` is unwrapped exactly once at construction, after the driver has
  transferred the `Pure` payload;
- the owning arm contains the resolved glue target and its code-lifetime guard;
  the scalar/value arm contains no callable target;
- observation borrows the value; finalization consumes the owner;
- there is one finalization chokepoint. Normal callers cannot copy the owned word
  or independently invoke the target;
- a defensive `Drop` backstop may release an armed owner during Rust unwinding,
  but it must share the same disarm-on-success state and call target. It is not a
  second normal release path.

This follows **Model invariants by representation** and **Published pointers have
retention owners**. A raw function address without its `Arc<Jit>`/`Arc<Linker>`
guard is not a valid release target.

## 3. One protocol, three target-resolution adapters

Target resolution varies only because the compiled code is housed differently.
The semantic owner and observe-then-release ordering do not vary.

### 3.1 Fresh JIT (`--run` and REPL)

Backend proactively emits exported glue for every concrete owning return type in
the same `compile_to_module` transaction as the result-producing code, including
the inner `a` of `IO a`. Int consumes
`CompilationArtifacts.drop_glues: HashMap<ConcreteType, DropGlueArtifact>`:

1. Narrow the carried result type to the exact `ConcreteType` key.
2. Perform one direct `drop_glues.get(&key)`. Absence, symbol/key disagreement,
   or `jit_address: None` on a fresh-JIT result is a hard compilation/integration
   error before observation ownership can be lost. There is no symbol scan or
   compile-after-the-fact fallback.
3. Pair `jit_address` with a clone of the existing `Code::Jit(Arc<Jit>)` owner
   retained by the result-producing entry. The pair, not the address alone, is
   stored on the result owner.
4. Display/convert while that guard is live; call the address; drop the guard
   only after the call returns.

`--run` and REPL consume the same target construction. Their only difference is
the observation callback: exit conversion versus `result_value_doc` rendering.

### 3.2 Cache-hit execution

A cache hit obtains no process-local address from serialized metadata. The object
already contains the exported glue body. Int:

1. derives the same canonical symbol using
   `drop_glue_symbol_name(&module, &concrete_type)`;
2. resolves it once with the cache loader's existing `Linker::get_symbol` keyed
   lookup after `load_object`;
3. pairs the pointer with the same `Arc<Linker>` that retains the mmap'd object
   code (`Code::Linker`); and
4. runs the identical observe-then-release owner.

Missing symbols are cache-load failures, not cache misses repaired by generating
private glue. No address or drop-glue map is serialized, so this design adds no
cache-schema bump.

### 3.3 Linked startup

The generated startup stub knows `main`'s concrete result type at object emission.
It declares an import/relocation to
`drop_glue_symbol_name(entry_module, inner_result_type)` using the same canonical
naming function. The defining module object supplies the exported body and the
system linker resolves the relocation.

The clean block's required order is:

1. retain the driver's `exit_code_i64` as the owned result word;
2. compute the process `i32` exit code while the word is live;
3. for an owning result, call the relocated `extern "C" fn(i64)` glue once;
4. call `exit(computed_code)`.

The error block does not call result glue because `ProgramOutcome` contains no
successful result on `error_kind != 0`. The startup object owns no Rust
`Arc`—ordinary executable text lifetime keeps both caller and relocated glue live
until `exit`. The exe-bundle must continue force-linking the intrinsic/runtime
dependencies used by the generated glue, but it does not define a wrapper
releaser and does not interpret the result type.

## 4. Integration seams and data flow

### 4.1 Compilation-artifact routing

The fresh-JIT artifact projection must reach the same int compilation record that
currently installs `Code::Jit`; it must not be discarded after introspection data
is routed. The release target is associated with `(module, ConcreteType)`, not
with a source expression or the most recently compiled function. Repeated
compilation may replace the association only together with its code-lifetime
owner; an old pointer never pairs with a new JIT.

Cache restore constructs the equivalent association from the loaded object's
symbol and its `Arc<Linker>`. Both adapters feed the same int-private release
target type. This applies **Resolve once** and **Single source of truth**: fresh
JIT reads the approved artifact; cache/link derive the approved symbol; no int
helper reconstructs backend's type encoding.

### 4.2 REPL value lifetime

`ExprOutcome::Value` / `EvalResult::Val` currently separates execution from later
formatting. The owned result must therefore remain armed across that boundary or
the formatting operation must be moved inside an owner-consuming helper. Either
shape is acceptable only if the type, target, and lifetime guard travel together
and `format_eval_result` cannot silently copy the owned word.

Formatting reads the value first. The release occurs after the complete
`StyledDoc`/String has been built, before control returns to the prompt. Bare
symbol/definition displays and display-only values that did not come from a
clean executed result do not fabricate ownership. The defensive `ty.is_io()`
formatting branch must not become a second IO/result owner; execution unwraps IO
at the driver boundary, and any future direct caller must enter the same owner
constructor.

### 4.3 Run lifetime

`CompilerSession::trampoline` returns an owned result, not a free-standing tuple.
`main` computes the exit code through its observation API, finalizes the result,
then shuts down/flushes and exits. Session shutdown must not precede release:
shutdown may remove the final `Code::Jit`/`Code::Linker` retention root. The
binding order is observe → release → session/code shutdown → trace flush → exit.

### 4.4 `Pure` and non-IO results

`cranelisp_run_program` owns known IO protocol nodes. For `Pure payload`,
`drive_io` returns the payload and `consume_io_tree` frees the outer IO box
without freeing that opaque field; ownership transfers to the int result owner.
The result owner therefore selects glue for `a`, never glue for `IO a` and never
an intrinsics `consume_*` function.

Non-IO expression execution enters the same clean-result constructor with its
own result type. This prevents an IO-only 0745 patch and makes REPL evaluation
and entry-main execution obey one typed-context rule.

## 5. Exact-once and error-path rules

| Event | Result ownership disposition |
|---|---|
| clean scalar/value result | observe; release is a typed no-op; consume owner |
| clean owning result | observe completely; invoke target once; disarm |
| display/exit conversion returns an error | finalize through the same target before propagating, or unwind through the armed backstop |
| driver runtime trap / dispatch fault | no successful result owner; no result glue call |
| missing/non-concrete type at typed exit | hard located/invariant error while the owner remains armed; never shallow release or silent leak |
| missing artifact/symbol/address | hard compilation/cache/link error; no ambient scan and no late compilation |
| glue call traps | propagate/abort as safety failure; never retry |
| session shutdown / REPL redefinition | cannot invalidate a target held by an armed owner's lifetime guard |

The release call owns its input. After it begins, the caller must not inspect,
format, convert, or release the word again.

## 6. Unit-test design: submodule × scenario matrix

Tests mirror module composition (**Tests mirror module composition**). `/dev`
places unit tests beside the owner and uses test doubles for observation and glue
invocation; exe-bundle/link correctness remains e2e where relocation is the fact.

| Submodule | Complexity / positive cells | Edge cells | Negative cells |
|---|---|---|---|
| `pipeline` result-owner construction | Int no-op; String release; `IO String` selects String; nested ADT/Vec key | non-IO expression; `Pure` inner typing; value 0 as a valid word | non-concrete `Type`; owning type with no keyed target; never select `IO a` glue |
| `worker` fresh-artifact routing | keyed String and nested type artifacts pair with `Code::Jit` | two types in one batch; repeat key; recompilation pairs new address/new guard | absent key; `jit_address: None`; symbol mismatch; raw address cannot outlive guard |
| cache-hit loader | canonical symbol resolves and pairs with `Arc<Linker>` | warm cache; two module-qualified copies of same type | missing symbol fails; no scan; no serialized/process-local address fallback |
| `eval` / `repl::format` | scalar, String, nested payload display before one release | formatter returns error/unwinds; warning envelope; result value 0 | no release before final display read; no double release after formatting; display-only Def/bare-symbol path does not release |
| `main` run arm / lifecycle | `IO Int` converts then releases; `IO String` converts 0 then releases | nested payload; both JIT and cache-hit retention; shutdown after release | shutdown-before-release rejected; trap/fault invokes no result glue; glue never retried |
| `exe` startup CLIF | scalar omits call; owning `IO a` conversion precedes relocated glue then exit | Int owning wrapper versus scalar Int; nested concrete type; module qualification | error block has no release; no call after exit; missing relocation is link failure; no JIT/private helper |
| exe-bundle contract | generated glue's intrinsic dependencies remain linked | no-platform program; release before process exit | no exe-bundle generic releaser or result-type switch; missing dependency fails linked e2e |

Ordering tests use a recorded event sequence such as
`observe-start → observe-read → observe-done → glue(value) → guard-drop`; counter
tests assert glue is called exactly once. Type tests assert the exact
`ConcreteType` key and module-qualified `LinkerSymbol`, not merely that some
function pointer was called.

The QA/e2e complement is `tests/plan/s116-test-plan.md`: run, REPL, and link;
scalar, heap, nested heap, and `Pure`; exact allocation parity; both ownership
analysis toggles; and the permanent 0745 cell.

## 7. Quality attributes

- **Simplicity / maintainability:** one owner state machine and one release-target
  representation; three small resolution adapters reflect real code-housing
  differences. Int contains no value-layout traversal.
- **Observability:** target-resolution errors name module, concrete type, expected
  symbol, and mode. Debug assertions/event-order unit tests make early release,
  lost ownership, and retention loss attributable at the seam.
- **Concurrency-safety:** result owners are turn-local and contain immutable
  target/guard pairs. No global address map is introduced; recompilation cannot
  mutate an armed owner.
- **Performance:** one keyed lookup at owner construction and one glue call at
  final release. Scalar/value results remain call-free. No global registry, type
  scan, or depth-proportional int work.
- **Testability:** observation and release are separable callbacks behind an
  int-private owner, so ordering, exact-once behavior, and error cleanup are
  unit-testable without constructing the full compiler (**Testability is
  structural**).

This sprint does not change int's compiler-internal concurrency architecture or
observability sinks. It changes result lifetime, cache/JIT artifact routing, REPL
display ownership, and linked-startup ordering only.

## Next skills

- `/arch` — confirm this design consumes ruling 9 without a further public API
  or ABI change and reconcile backend's subordinate doc from its pre-ruling
  `Linkage::Local` wording to the approved exported contract.
- `/qa` — verify the owner/error/retention negatives against the S116 typed-exit
  matrix and keep 0745's mode/toggle cells name-traceable.
- `/dev` (int/exe-bundle) — implement the private owner and the fresh-JIT,
  cache-hit, REPL/run, and linked-startup adapters with the unit matrix.
- `/review` (int/exe-bundle) — reject raw unguarded addresses, display-before/
  after ordering inversions, IO-only/JIT-only release, and any private deep
  releaser.
