# Backend — context design

> **Owner**: `design`, narrow-deployed to `cranelisp-backend`.
>
> **What this document is**: the backend's interior — how the crate is shaped,
> what it must not do, what is measured and what is merely asserted, and the
> index to the subordinate designs. It is the entry point for backend design
> work.
>
> **What it is not**: it does not restate the boundary or the public surface.
> `design/arch/bounded-contexts.md` §3 owns the bounded context, what crosses it
> and the invariants the crate upholds; the per-item `///` rustdoc in
> `crates/cranelisp-backend/src/` owns the exact Rust obligations and
> `public-api.txt` is their evidence. Where any statement here disagrees with
> those, they win. Code conventions, the submodule seam map and the debug hooks
> are `dev`'s, in `crates/cranelisp-backend/CLAUDE.md`.

## 1. What the crate is

Typed AST in, executable code out. The backend translates symbol-table entries
into Cranelift IR and produces artefacts: in-memory code for direct execution,
object files for linking, and the cache pair for re-use across sessions.

Three properties shape everything else:

- **One emission path.** `compile_to_module` is the only place CLIF is emitted.
  Mode is a property of the `Module` the caller supplies, never a parameter, and
  the emitted CLIF is identical either way (`jit-object-convergence.md` §1).
- **No cadence, no locks.** Compilations run concurrently over disjoint inputs.
  See [Concurrency](#4-concurrency) for the crate-local locking rule.
- **It decides nothing it could be told.** Name resolution, type identity,
  ownership modes and concreteness all arrive as resolved values. The reading
  discipline is defined below.

Out of scope: inference (typecheck), expansion (frontend), scheduling (int),
runtime helpers (intrinsics/primitives — the backend declares them as imports).

## 2. The reading discipline — a pure keyed consumer

This is the crate's defining property and the single largest simplification in
its history. Every semantic identity the backend consumes — call target,
constructor, effect, extern, arity, ownership summary, type identity for
layout, tags, drop glue and schema — arrives from typecheck as a resolved,
fully-qualified value. The backend performs **one direct keyed fetch** on it and
discriminates on the fetched entry's kind. The projections are on
`CompileContext` (`compiler/context.rs`).

**There is no resolver.** No precedence walk, no import-chain re-follow, no
global scan. The former resolver family and its arbitrary-order fallback scan
were deleted; `resolution.rs` retains only fixed name-*composition* schemes.
The standing gate is structural: zero resolver entry points under `compiler/`.

**A miss is loud.** A carrier miss, an entry miss or a slot-less template at a
value read is a hard, located codegen error — never a fallback, never a
re-resolution. The `Option`-and-fallback convention was replaced by exhaustive
matches on the closed carrier sums, which makes "unresolved" unconstructable at
this boundary rather than merely rejected.

**Why it is structural, not stylistic.** A second resolver has to agree with
typecheck's, and repeatedly did not — the recurring "two resolvers, one name"
class, including run-to-run wrong-tag nondeterminism. Identity that the backend
re-derives is identity that can disagree. The same rule governs smaller
judgments: self-call identity is ONE shared predicate (`is_self_call`) consumed
by the TCO back-edge decision, the stack-allocation gate and the spark
classifier, so those three can never diverge; before it existed each judged
identity by bare written-name equality and a shadowed call looped forever.

**Where a judgment is genuinely the backend's, it stays here.** The scope-stack
slot behind a local binder is backend-owned — the carrier ships binder
*identity*, not a slot. A binder absent from the scope stack is a producer
contract breach and fails hard with the binder named, not a soft codegen error.

**Two soft arms remain, and both are narrower than they read.**
`constructor_metas` (`compiler/context.rs`) yields an empty result when its
table lookup misses and drops a constructor whose canonical and bare probes both
miss; `concrete_field_types` (`compiler/match_codegen.rs`) returns an empty
vector on a key miss that was hard-validated moments earlier. Neither is a
breach of this section. The first is a type→constructor *enumeration*, not a
reference-kind carrier read, and its governing contract is
`design/arch/dotted-ctor-canonical-keys.md` §10.5, which places a
`debug_assert!` on keying drift and accepts the release-build skip; a miss there
could degrade trace descriptors or field-type substitution, but legitimate
inputs do not construct the missing-entry state. The former direct drop-glue
consequence is superseded: glue reads constructor fields through its own
hard-failing path (`transitive-drop-glue.md`). The second sits behind that earlier hard check in
the same arm, so it is a dead defensive arm rather than a fallback.

**Proposed disposition, awaiting the user (ACT-0964 item 1).** Harden both
arms rather than keep the release-build skip. Pass the already-fetched
constructor entry into `concrete_field_types`, so its miss cannot be
constructed, and make `constructor_metas` return a located `CodegenError` on a
both-probes miss in every profile, with one unit test per arm. The skip saves
nothing on legitimate inputs, and a hard miss is this section's rule
everywhere else. Accepting the skip instead keeps a leak-grade degradation
whose only detector is a debug assertion that release builds do not run, and
`dotted-ctor-canonical-keys.md` §10.5 (`arch`) would then remain the
governing text. Either answer is recorded here.

## 3. Internal shape

The kept-current module and seam map is `crates/cranelisp-backend/CLAUDE.md`;
this document does not carry a second inventory, because the ones it used to
carry decayed through three reorganisations before anyone noticed.

**The maintainability problem is real and has moved, not closed.** The S75-era
audit's mini-monoliths were split by protocol boundary, and the helper
duplication families (the arity-cloned extern-call ladder, the cloned COW
skeletons, the twin symbol-table walkers) were collapsed into single
parameterised helpers. But `compiler/fn_compiler.rs` is now by a wide margin the
largest file in the crate — larger than any of the files that split — and
`compiler/apply.rs` is second. The oversized *functions* were fixed; the
oversized *file* was not.

Alongside it sits an unrouted flag from the same era: `FnCompiler`'s **field
count**. Moving methods between files never addressed it, and it is the kind of
structural question that belongs to `arch` rather than to a file split. No
filing carries it. It is recorded here so that the next reader of this crate
does not rediscover it as if it were new.

**Most of the weight is ownership arithmetic.** The deciders that
[uniform counting](uniform-counting.md) §5 retires live mainly in these two
files, so that change is also this condition's largest reduction.

**Drop-glue builders stay separate (ACT-0964 item 2).** ADT glue
(`DropGlueRegistry`), the two capture-envelope glues (one shared envelope,
`emit_capture_dec_glue`) and Vec release (`emit_vec_rc_dec_with_drop` over
`runtime/vec_drop`) keep their own builders. What must agree among them is
already single-sourced: glue identity, the nullary guard, field discharge only
on the last reference, and release by type through `emit_typed_rc_dec`. What
differs is real: capture glue builds in its own context before the enclosing
builder can reach the registry, and Vec release is a runtime teardown behind
an rc gate. A shared skeleton would carry a mode for each.

**Cost of the condition.** Review cost in these files is dominated by
re-establishing the invariants of the surrounding thousands of lines, not by
understanding the change. That is the whole of Principle 6's complexity budget
argument, and it is what makes feature work here slow.

## 4. Concurrency

The backend reads shared state and writes through narrow, interior-mutable
seams. It takes **no lock of its own**.

- Symbol tables are read through a concurrent map; reads are shard-scoped and no
  exclusive borrow is ever required.
- The Cranelift module is exclusively borrowed for the duration of one
  `compile_to_module` call and never shared across threads.
- Slot *layout* is pinned before codegen; workers fill slot *contents* in any
  order, in parallel, with no inter-worker coordination.
- Publishing a compiled symbol's lifecycle owner goes through the types-owned
  publication capability, briefly and per entry.

The reclaim safety invariant — no derived function pointer is reachable once a
JIT's retention root hits zero — is **upheld externally**, by int's atomic
GOT-swap discipline and by the named retention owner every published pointer has
(Principle 22; `design/arch/bounded-contexts.md` §3 invariant 5, with the
session-lifetime pool in `design/int/session-transaction.md` §6–§7). A closure's
embedded `code_ptr` and `drop_glue_ptr` follow the
[intrinsics closure-layout contract](../arch/bounded-contexts.md) and are raw addresses
into their creating compilation's pages; it is the owner's retention, not GOT
routing, that keeps them valid. The backend relies on that; it does not enforce
it, and the asymmetry is deliberate.

There is nothing to flag here, and that is an outcome rather than an omission:
the crate introduces no shared mutable state for a review to worry about.

## 5. Observability

The target is that when a miscompile fires, the signal needed to find it is
already visible — CLIF, RC traffic, last-use decisions, GOT-slot population.

- **CLIF** — a stderr dump filtered by module or module-and-symbol during
  compilation, plus on-demand capture for the REPL. The capture flag is a
  parameter the caller sets only when introspection is live, so batch runs skip
  the rendering rather than producing it and dropping it unread. The stderr dump
  is independent of that flag. Cache-hit paths do not re-codegen, so CLIF for
  them comes from the introspection store, not the dump.
- **Disassembly is never stored.** It is re-derived on demand, because it costs
  far more than CLIF capture and is asked for rarely.
- **RC** — tracing of inc/dec events and a live-allocation check that catches
  double frees; per-site tallies behind their own gate.
- **GOT-slot population has a first-class observer.** The backend owns only the
  observer *contract* and emits on its two write sites; with nothing registered
  the emit path is a single relaxed null check. The buffer, activation,
  formatter and redefinition tags are int's. This was chosen over extending the
  introspection artefact, paralleling the IO observer.

**Per-member failure attribution.** When one member of a compile batch fails,
the error carries that member's own module and name, attached at the body loop
where the identity is still in hand. It is not reconstructed afterwards from the
cause string, a callee, or iteration state — that would be a second resolver for
a fact the loop already had. The original cause and source location pass through
unchanged; the helper must not format and re-parse either. A later-member
failure may leave declarations inside the caller-owned, unpublished Cranelift
module, but **it cannot publish a function pointer to the live GOT** — so the
backend gains no rollback, retention or transaction responsibility from this.

**Every codegen gate is byte-identical when off.** That phrase in a gate's
rustdoc is a contract, not a comment: it is what lets a gate ship dark and what
makes a golden-CLIF diff meaningful. The corollary is the acceptance rule for
any pure extraction or refactor — **a non-empty golden diff means the extraction
was not behaviour-preserving; the refactor is wrong, not the golden.**

## 6. Cache and linking

`module-caching.md` and `compile-to-module.md` carry the mechanism; the
interior facts worth stating once here:

- **Writes.** The backend owns the persisted format and writes two of its
  files: `write_meta` writes a module's sidecar and `write_manifest` writes the
  index, each through a temporary file and rename. The object is the ordinary
  emission entry against an object module, finalised **by the caller**; int
  emits its bytes and writes the `.o` itself. There is no separate
  object-compile entry, which keeps mode out of the entry point. Int decides
  when to write and where the cache directory is
  ([module caching](module-caching.md) §7).
- **Reads.** The cache-hit path is not a parallel codepath. It lives inside the
  ordinary recursive module registration. Symbol resolution returns a typed
  result, never an option: **a resolution failure is a cache-load error, never a
  silently skipped slot.** That shape exists because the option-and-skip pattern
  silently pushed NULL slots and shipped.
- **Schema versioning.** The persisted sidecar carries a schema version; a
  mismatch invalidates the cache as if dependencies had changed, rather than
  surfacing a deserialisation error. Read the current value from the constant —
  a literal in prose goes stale, and did.
- **One object, two readers.** The same `.o` is consumed by the in-process
  linker on a JIT cache-hit and by the system linker under `--link`. The backend
  emits identical CLIF for both; only the resolver at finalize differs. The
  `--link` entry-point alias is int's job, not the backend's.
- **The in-process linker exists** because a JIT-mode cache hit cannot use the
  system linker: it must map an object and resolve relocations against
  in-memory addresses.

## 7. Runtime failure

**A runtime panic reports its message and ends the process, in every mode,
the REPL included; nothing propagates or recovers** (user ruling, 2026-11-15;
the normative text is `spec`'s, `spec/12-runtime.md` §12.7). The architecture
is [process-ending panics](../arch/s123-panics-and-environment.md) §1: one
terminal funnel in intrinsics, no slot, no sentinel and no ferry. The backend's
part is its §1.3 emitted half: a raise is never followed by reachable code.

**Status: the emitted half is built (S123 W1).** Every raise ends its block
with a trap, and no raising frame returns a sentinel. Closing
[ACT-1040](../../sprints/actions/ACT-1040-panic-sentinel-reaches-heap-consumer-intake.md)
(the SIGSEGV on a sentinel) and
[ACT-1042](../../sprints/actions/ACT-1042-callee-panic-with-scalar-result-resumes-caller-intake.md)
(the resumed caller) is `qa`'s decision, on their end-to-end cells.

- **Shape.** Place the message bytes, call `runtime/panic(msg_ptr, msg_len)`,
  and end the block with a trap. There is no sentinel and no return.
  - The trap never executes, because `runtime/panic` never returns (below).
    If that contract were broken, the process would stop at the trap instead
    of resuming a caller with a fabricated value. That is the safer failure.
  - No other site emits a trap. An unguarded `sdiv` stays excluded, because a
    hardware fault would bypass the message.
- **One emission helper.** `raise::emit_raise` emits the message, the call and
  the trap together (Principle 07, Single source of truth). Its four
  consumers are the match-failure block, the division guard, the shared Vec
  index guard and the trap stub. A site's message is either one of the
  spec's §12.7.2.1 messages, placed in an anonymous data object, or the trap
  stub's baked session-owned bytes.
  - **Grade: measured, with a known bypass.** Nothing structural stops a new
    site from emitting the call itself: the helper takes a raw `FuncId`, and
    any code holding `runtime/panic`'s id can make its own `FuncRef`. The
    census `raise::tests::raise_helper_is_the_only_panic_call_emitter` scans
    production sources for a `FuncRef` made for `runtime/panic` outside the
    helper. Its detection proof fires on both spellings the crate uses and
    stays silent for another intrinsic.
  - **Residual.** The census matches identifier spelling, not function
    identity. It counts a `declare_func_in_func` call only when that call's
    first argument contains `panic`. An emitter that first binds the id to an
    unrelated name (`let id = …panic_func_id…; declare_func_in_func(id, …)`)
    is not counted, and the planted-emitter proof does not cover that case
    (W1 review advisory B1). Until it is closed, the architecture's
    falsifier still applies: a `runtime/panic` call followed by reachable
    code. Each consumer's structure cell reads its CLIF for that.
  - Making the bypass unwritable needs a type that only the helper can
    consume, such as an opaque handle in place of the raw `FuncId`. That
    changes the boundary the id crosses, so it is `arch`'s question (open
    handoff). `qa` owns the grade.
- **What the backend relies on, in intrinsics' terms.** `runtime/panic` never
  returns, on any thread, and its catalog entry declares no result (ACT-1033's
  derived pair). The import is declared from that entry. The exit path, the
  message's rendering, a spark worker's panic and the order among concurrent
  panics (open question S123-Q7) are `design`(intrinsics)'s and `spec`'s.
- **A missing `runtime/panic` declaration** is a located codegen error.
- **Sites.** Non-exhaustive match (`"match failed"`), division by zero
  (`"division by zero"`), and Vec bounds. The messages are
  the spec's §12.7.2.1 table and are observable. The redefinition
  [trap stub](ownership-codegen.md#81-the-trap-stub) raises through the same
  call with its own provenance message, so under the ruling a call to a
  cascade-broken symbol also ends the REPL (open question, below). A new
  trapping operation, such as a remainder primitive, adopts the same shape.
- **One Vec index guard.** Load the length and raise the panic shape when the
  index is negative or not below it. The `vec-get` and `vec-set` emission cores
  each open with this one guard, before any element load, RC operation,
  uniqueness probe or runtime-helper call.
  - Status: built for both operations; `qa` closed ACT-1037 on 2026-10-01
    ([s122-closure.md §9](s122-closure.md#9-act-1037--vec-set-index-guard)
    states the `--link` limit).
  - The `vec-set` core is the only lowering of `vec-set`. The static last-use
    site, the static non-last-use (copy-only) site and the value-position and
    auto-curry wrappers all reach the element write or `vec-set-copy` through
    it, so the guard dominates both copy-on-write arms by construction.
  - A static uniqueness proof elides the rc probe, never the guard. It
    elides the probe only when the source has no separate owner; otherwise
    the probe runs.
  - Both operations report the spec's single message,
    `"vec-get: index out of bounds"`. A `vec-set`-specific message is a `spec`
    question.
  - `vec-set-copy` is never called out of range. It cannot raise the panic
    itself: its result is a Vec that the emitted code consumes before
    returning. So the check lives only in emission.
  - "Before any RC operation" holds inside the core, not across the whole
    static site. Counts raised before the core are never undone, which is
    moot once the process ends at the raise. The structure test checks only
    the core.
- **`i64::MIN / -1` wraps to `i64::MIN`**, like `+`, `-` and `*` (user ruling,
  2026-11-15; spec §12.7.3). Only a zero divisor raises. `emit_checked_div` keeps the
  hardware-faulting pair away from `sdiv`: a divisor of `-1` is replaced by
  `1`, and the result is selected as the wrapping negation of the dividend.
  Every other divisor keeps `sdiv`'s truncation. The out-of-line `div-i64`
  primitive (`a.wrapping_div(b)` after its zero test) behaves the same, so a
  value-use call and an inline call agree.
- **`+`, `-` and `*` wrap unguarded** (spec §12.7.3). Only an operation that would
  fault in hardware earns a guard; checked arithmetic would be stricter than the
  language requires.
- **What the ruling removed from this crate.**
  - The sentinel return after every raise, and with it every question of what a
    caller does with a panicking callee's result. The propagation options
    in [s122-closure.md §10](s122-closure.md#10-act-1040--panic-propagation-proposal)
    are withdrawn.
  - The leak caveats on the raise paths, including the trap stub's.
  - Module cells that ran a panicking JIT body and then read the error slot. A
    raise now ends the process, so the executing cells run the body in a child
    process (`test_child`) and observe its exit and its single message. The
    structure cells read the CLIF: the guard dominates the core, and the raise
    is followed by the trap.
  - No backend site lowers `catch-runtime-error`, so its removal has no
    emission counterpart here.
- **Messages (ACT-1041, ACT-1036).** The backend supplies only the message
  bytes at each site. The doubled `runtime panic:` prefix and the codegen
  category in `--run` come from the binary's two slot readers (ACT-1041), and
  the `0..0` location of the `main`-return refusal is raised in `src/exe.rs`
  (ACT-1036); neither is a backend site. The backend's own `0..0` codegen
  spans are FIXME 0915, which carries.
- **Open, for the user through `spec`.** Whether a call to a cascade-broken
  symbol is a runtime panic under the ruling, and so ends the REPL. The
  alternative is a refusal the session raises before the call, which is
  `design`(int)'s. The backend stub works under either answer.

## 8. Subordinate designs

| Subject | Document | Standing |
|---|---|---|
| Uniform reference counting | `uniform-counting.md` | **Adopted target, not built (S123).** Reading U′: every binder owns, last-use move and in-place update at count 1 are the only retained rules, one ownership plan per body. Supersedes the counting rules in the RC discipline, ownership codegen, drop-glue TCO, binder tail-transfer and binding-indirection documents when it lands. |
| S122 delivery record | `s122-closure.md` | Retained evidence for the S122 corrections, which landed at the S122 close (2026-10-02): result-root consumer, shared Vec guard, typed closure fixture, macro alias, IO-combinator freshness and the ACT-1037 `vec-set` index guard (§9, with its `--link` evidence limit). Its §10 panic-propagation options are withdrawn by the 2026-11-15 ruling (§7). |
| Compilation entry shape | `compile-to-module.md` | The one entry's contract and phase order, constructor codegen, GOT emission, finalisation and publication, and its error contract. |
| JIT/object convergence | `jit-object-convergence.md` | The convergence invariant, what may differ at the fixup boundary, and the falsifier that has no executing guard. |
| Per-module GOT | `per-module-got.md` | The two-GOT model as emitted, and why it is shaped that way. |
| Module caching | `module-caching.md` | Cache keys, serialisation, invalidation, the load path. |
| Executable generation | `executable-generation.md` | `--link` mode. |
| RC discipline | `ring2-rc.md` | As built, until `uniform-counting.md` lands. The conservative lowering: the uniform consuming convention, extern and platform consumption, the IO extern's balance, scope cleanup and the binders that never transfer by last use, the opt-in spark-capture borrow and its open default-on condition. |
| Ownership codegen | `ownership-codegen.md` | As built; its counting sections (borrow elision, the uniqueness proof, the wrapper and COW contracts) are superseded by `uniform-counting.md` when it lands. The mechanisms that consume the ownership analysis — borrow elision, stack placement, confined non-atomic RC, uniqueness and reuse, value flattening, redefinition machinery — with their built/open state. |
| Transitive drop glue | `transitive-drop-glue.md` | One named drop function per concrete owning type; declaration-first construction; per-arm match release; the TCO slot predicate; no depth cutoff, no shallow fallback. |
| Non-concrete release | `non-concrete-release-contract.md` | Category before operation, no fabricated concreteness, the IO node's release, the one entry-convention derivation for every call and wrapper, and the open structural close (lifecycle disposition, refusal frame, census). |
| Binder identity | `binding-scope.md` | A binder is its slot, never its name. Delivered. |
| Binding-indirection consume | `binding-indirection-consume.md` | The consume-position × operand-provenance contract, as built; retired wholesale when `uniform-counting.md` lands. |
| S115 carrier and RC record | `s115-carrier-and-rc-sweep.md` | Retained S115 carrier-attribution and RC-leak evidence, the auto-curry emission totality table and the R4 mangle-family census. |
| Failed-member attribution | `s117-failed-member-attribution.md` | The attribution seam and its negative design list. |
| IO trampoline / scheduling | `io-trampoline.md`, `io-scheduling.md` | The IO node and effect machinery. |
| Lenient evaluation | `lenient-eval.md` | Spark admission (M-static default), the create-gate budget and depth decline, the IVar runtime contract, emission and the error ferry. Open depth/contention work is in `design/arch/backlog/performance.md`. |
| IO trace contract | `archive/io-trampoline-trace.md` | The IO event taxonomy and its off-path performance bound — a live contract despite its location. |

## 9. Cross-references

- `design/arch/bounded-contexts.md` §3 — the bounded context, boundary and
  invariants (authoritative over anything here)
- `design/arch/backend-keyed-consumer.md` — the keyed-consumer end state
  summarised in this document, and the `VarRef`/`ApplyRef` carrier sums
  consumed here
- `design/arch/concrete-boundary-type.md` — why the type the backend classifies
  has no variable case
- `design/arch/principles.md` — the principles cited above
- `crates/cranelisp-backend/CLAUDE.md` — seam map, debug hooks, code conventions
- `crates/cranelisp-backend/src/` — the implementation, and the rustdoc that is
  the facade
