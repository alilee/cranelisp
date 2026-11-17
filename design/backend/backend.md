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
> are `dev`'s, in `crates/cranelisp-backend/AGENTS.md`.

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
by the TCO back-edge decision and the spark classifier (and, until its S124
retirement, the stack-allocation gate), so they can never diverge; before it existed each judged
identity by bare written-name equality and a shadowed call looped forever.

**Where a judgment is genuinely the backend's, it stays here.** The scope-stack
slot behind a local binder is backend-owned — the carrier ships binder
*identity*, not a slot. A binder absent from the scope stack is a producer
contract breach and fails hard with the binder named, not a soft codegen error.

**Keyed type and constructor reads fail in every profile** (user ruling,
2026-11-15, closing ACT-0964 item 1). `constructor_metas` and
`ctor_field_types` (`compiler/context.rs`) return a keying-drift codegen error
when the module table, a constructor's canonical and bare probes, or the
pattern constructor's entry misses. Neither degrades to an empty result, and
neither relies on a debug assertion. Grade: measured, by one unit cell per arm
with a resolving control (`compiler/context/keyed_read_hardening_tests.rs`).
This supersedes the release-build skip that
`design/arch/dotted-ctor-canonical-keys.md` §10.5 accepted.

- **Residual, asserted with a falsifier.** `ctor_field_types` returns a
  parametric constructor's declared field types unsubstituted when the
  scrutinee carries no type arguments. The match lowering always supplies the
  scrutinee's concrete type, so the arm is believed unreachable from
  production. Falsifier: a field type containing a type variable reaching
  heap classification from a match arm. S124 makes it a `ParamArity` keying
  error ([release contract](non-concrete-release-contract.md) §7.4 step 1).

## 3. Internal shape

The kept-current module and seam map is `crates/cranelisp-backend/AGENTS.md`;
this document does not carry a second inventory, because the ones it used to
carry decayed through three reorganisations before anyone noticed.

**The maintainability problem is the ownership stratum.** The helper
duplication families of the S75-era audit (the arity-cloned extern-call ladder,
the cloned COW skeletons, the twin symbol-table walkers) are single
parameterised helpers. `compiler/fn_compiler.rs` and `compiler/apply.rs`
remain the crate's largest files, and `FnCompiler` carries many fields of
ownership state. The S122 audit (`audits/cranelisp-backend-s122.md` F4)
judged that file size is not the issue; the many separate answers to "who owns
this reference" were. [Uniform counting](uniform-counting.md) §5 deleted those
deciders at the S123 W2 cutover, and §0 of
[ownership codegen](ownership-codegen.md) schedules the remaining placement
mechanisms out. Whether `FnCompiler`'s remaining field count warrants `arch`'s
attention is to be re-measured after the S124 retirements, not before.

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

**Per-member failure attribution.** A failing batch member's error names that
member, attached at the body loop where the identity is in hand, and cannot
publish to the live GOT ([compile-to-module](compile-to-module.md) §15).

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
is [process-ending panics](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) (§4b invariant 13): one
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
  the trap together (Principle 07, Single source of truth). Its consumers
  are the match-failure block, the division guard and the shared Vec index
  guard, each placing one of the spec's §12.7.2.1 messages in an anonymous
  data object. The redefinition trap stub, a former fourth consumer, retired
  at S123 W4 ([ownership codegen](ownership-codegen.md) §8.1).
  - **Grade as built: measured, with a known bypass.** The helper takes a raw
    `FuncId`, and any code holding `runtime/panic`'s id can make its own
    `FuncRef`: the public `CompileContext::panic_func_id`, or the
    intrinsic declaration loop's by-name map
    (`jit::IntrinsicFuncIds::by_name`), which seeds every compile's
    `func_ids`. The census `raise::tests::raise_helper_is_the_only_panic_call_emitter`
    matches spelling, not identity, so an alias evades it (W1 review advisory
    B1). Until the hardening below lands, the architecture's falsifier
    applies: a `runtime/panic` call followed by reachable code.
- **Hardening (S124, P-15; safety register R13).** After row D2 makes the
  `compiler` module crate-private:
  - **One handle.** `raise` defines a panic handle whose only field, the
    `FuncId`, is private to `raise`. Only `raise` constructs one, and only
    `emit_raise` reads its id. `CompileContext`, the intrinsic declaration
    result and every consumer (the match-failure block, the division guard in
    `primitives_inline`, the Vec index guard, the value-position wrappers)
    hold and pass the handle, never a `FuncId`. `raise::declared` returns
    the handle.
  - **No second path to the id.** The intrinsic declaration loop hands the
    declared `runtime/panic` to `raise`, which wraps it. That entry is not
    inserted into the by-name map, so no compile's `func_ids` contains it and
    no by-name lookup yields it. The panic symbol's name appears in this
    crate's production source only in `raise`.
  - **Grade after: structural** for reuse of the declared id: code outside
    `raise` holds no value from which to build the call. **Measured,
    lexically, for one residual:** Cranelift's `declare_function` returns the
    same id for a symbol declared again by name, so a by-name re-declaration
    anywhere in the crate would bypass the handle. That cannot be made
    unwritable inside this crate. The existing census is rewritten to that
    residual: it counts production mentions of the panic symbol's name outside
    `raise`, and its detection proof plants one by-name declaration and stays
    silent without it. The spelling census of `FuncRef` construction is
    retired, since the handle makes it moot. The grade is safety register
    R13's.
  - **The census's blind spot** is a declaration whose name is computed and
    never spelled, such as a second loop over the intrinsics catalog. The
    intrinsic declaration loop stays the crate's one catalog-driven
    declaration site; `review` rejects a second (R13).
  - No public item is added; D2 removes the field from the public surface
    first.
- **What the backend relies on, in intrinsics' terms.** `runtime/panic` never
  returns, on any thread, and its catalog entry declares no result (ACT-1033's
  derived pair). The import is declared from that entry. The exit path, the
  message's rendering, a spark worker's panic and the order among concurrent
  panics (open question S123-Q7) are `design`(intrinsics)'s and `spec`'s.
- **A missing `runtime/panic` declaration** is a located codegen error.
- **Sites.** Non-exhaustive match (`"match failed"`), division by zero
  (`"division by zero"`), and Vec bounds. The messages are
  the spec's §12.7.2.1 table and are observable. A call to a symbol a
  redefinition would leave broken is refused at compile time
  (`spec/12-runtime.md` §12.7.1), so no backend site raises for it. A new
  trapping operation, such as a remainder primitive, adopts the same shape.
- **One Vec index guard.** Load the length and raise the panic shape when the
  index is negative or not below it. The `vec-get` and `vec-set` emission cores
  each open with this one guard, before any element load, RC operation,
  uniqueness probe or runtime-helper call.
  - Status: built for both operations; `qa` closed ACT-1037 on 2026-10-01
    ([closure record](../../tests/plan/s122-evidence-delta.md#act-1037-vec-set-bounds-check-closed)
    states the `--link` limit).
  - The `vec-set` core is the only lowering of `vec-set`. The static site
    and the value-position and auto-curry wrappers all reach the element write
    or `vec-set-copy` through it, so the guard dominates both copy-on-write
    arms by construction.
  - The rc probe always runs after the guard. No static proof elides it
    ([uniform-counting.md](uniform-counting.md) §2.2).
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
    caller does with a panicking callee's result. The S122 propagation
    options are withdrawn (Git history).
  - The leak caveats on the raise paths.
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

## 8. Subordinate designs

| Subject | Document | Standing |
|---|---|---|
| Uniform reference counting | `uniform-counting.md` | **Built (S123 W2); W2 evidence adequate.** Reading U′: every binder owns, last-use move and in-place update at count 1 are the only retained rules, one ownership plan per body. The backend's one counting design. |
| S122 delivery record | `s122-closure.md` | Retired: anchors only, each pointing at its rule's current home; the record is in Git history. |
| Compilation entry shape | `compile-to-module.md` | The one entry's contract and phase order, constructor codegen, GOT emission, finalisation and publication, and its error contract. |
| JIT/object convergence | `jit-object-convergence.md` | The convergence invariant, what may differ at the fixup boundary, and the falsifier that has no executing guard. |
| Per-module GOT | `per-module-got.md` | The two-GOT model as emitted, and why it is shaped that way. |
| Module caching | `module-caching.md` | Cache keys, serialisation, invalidation, the load path. |
| Executable generation | `executable-generation.md` | `--link` mode. |
| RC discipline | `ring2-rc.md` | The calling convention as emitted, extern consumption, the IO extern's balance and the RC emission primitives. |
| Ownership codegen | `ownership-codegen.md` | The mechanisms that read ownership facts without deciding a count, and each one's disposition under Principle 27 (§0): confined atomicity retired at S123 W4; stack placement, value flattening, the spark density axis and the borrowed-sibling carrier retire in S124, each with its change-set designed. Also the reuse counters, the redefinition slots and the supporting contracts. |
| Transitive drop glue | `transitive-drop-glue.md` | One named drop function per concrete owning type; declaration-first construction; no depth cutoff, no shallow fallback. |
| Non-concrete release | `non-concrete-release-contract.md` | Category before operation, no fabricated concreteness, the IO node's release, and the S124 structural close: the three-arm census, the constructor field channel, concrete binder types (§7.3–§7.4, order §7.7). The lifecycle disposition and refusal frame stay open. |
| Binder identity | `binding-scope.md` | A binder is its slot, never its name. Delivered. |
| Binding-indirection consume | `binding-indirection-consume.md` | Retired (S123 W2); a stub kept for cited section numbers until those citations move. |
| S115 carrier and RC record | `s115-carrier-and-rc-sweep.md` | Retained S115 carrier-attribution and RC-leak evidence, the auto-curry emission totality table and the R4 mangle-family census. |
| Failed-member attribution | `s117-failed-member-attribution.md` | Retired: anchors only; the contract is `compile-to-module.md` §15. |
| IO trampoline / scheduling | `io-trampoline.md`, `io-scheduling.md` | The IO node and effect machinery. |
| Lenient evaluation | `lenient-eval.md` | Spark admission (M-static default), the create-gate budget and depth decline, the IVar runtime contract, emission and the error ferry; the S124 trace-extent decline (§2.3). Open depth/contention work is in `design/arch/backlog/performance.md`. |
| Trace codegen | `trace-codegen.md` | The backend's interior decisions for `(trace …)`: the traced set fixed by slot claims (ACT-1039), and the backend's half of strict evaluation and allocation-free wrappers (ACT-1038). |
| IO trace contract | `archive/io-trampoline-trace.md` | The IO event taxonomy and its off-path performance bound — a live contract despite its location. |

## 9. S124 open work and its order

Every S124 backend item, its design and what it waits on. A row leaves when
its change lands. Public rows are the S124 and S123 packets' as indexed in
[interfaces](../arch/interfaces.md#approved-changes-not-yet-in-source-s124).

| # | Change-set | Design | Waits on |
|---|---|---|---|
| B1 | Stack-placement retirement with row D5, closing ACT-1049 | [ownership codegen](ownership-codegen.md) §4 | — (first backend change-set); its intrinsics half lands with it |
| B2 | Category census, three arms | [release contract](non-concrete-release-contract.md) §7.3 | B1 |
| B3 | Close step 1: constructor field channel, row D1 | release contract §7.4 | B2, and the census reading zero residual and absent field reads (release contract §7.3). Expected: after typecheck's accessor monomorphisation, which removes the measured accessor traffic |
| B4 | Close step 2: concrete binder types, the three arms deleted | release contract §7.4 | the zero read: B3, typecheck's producer corrections including ACT-1034, and ACT-1050's producer |
| B5 | Value-flattening retirement, row D4 | [ownership codegen](ownership-codegen.md) §7 | B4 |
| B6 | Row D2, then the panic handle (P-15) | §7 above | — ; the handle follows D2 |
| B7 | Rows R10-1, -2, -3, -5, -7 as one contraction (R10-6 is superseded by R10-9, B11) | [BC §3](../arch/bounded-contexts.md#3-backend-cratescranelisp-backend) | B6's D2 |
| B8 | Borrowed-sibling carrier, rows D6 and D9 | [ownership codegen](ownership-codegen.md) §9 | the types change of D6, in the same change-set |
| B9 | Spark density retirement | [ownership codegen](ownership-codegen.md) §13.4 | — |
| B10 | Trace: claim-based traced set (ACT-1039); `in_trace_body` deleted (ACT-1038) | [trace codegen](trace-codegen.md) | the claim-based set: — . The deletion: intrinsics' row D8 change with this crate's descriptor-test adaptation ([trace codegen](trace-codegen.md) §2) |
| B11 | Heap layouts read from intrinsics, rows R10-9 and R10-10 | §9.1 below | intrinsics' additions ([heap layout owners](../intrinsics/heap-layout.md) §5) |
| B12 | A host-promised primitive as a value or partially applied (value uses refused; a partial `bind` aborts; a partial `race` panics the worker), closing ACT-1063 | [compile-to-module](compile-to-module.md) §12.1 | REPRO-1063 and REPRO-1063-p committed RED ([evidence delta](../../tests/plan/s124-evidence-delta.md) §3.9) |

- B6 to B10 and B12 have no dependency on the close; `sprint` places them. Each
  emission-affecting one carries its own scoped re-baseline, so keep them out
  of the B1–B5 change-sets.
- `CACHE_SCHEMA_VERSION` is bumped by B5 and B8, and by two change-sets that
  land on other surfaces but must edit this crate's constant: row D3's and
  ACT-1052's ([crate guidance](../../crates/cranelisp-backend/AGENTS.md), cache
  discipline; [int §7.6.3](../int/int.md#763-slot-layout-identity-act-1052)).
- ACT-1052's change-set also corrects the rustdoc of
  `CachedModuleRef::dependency_hashes` (`cache/manifest.rs`), which says the
  values are source hashes. After that change they are opaque validity keys
  whose form is int's. This is a factual correction with no API change, made
  by `dev`(backend) in int's change-set.
- The approved baseline-format row K11-a lands last, alone, after every other
  row.
- ACT-1018 has no backend item. Its remaining residual is one block per
  `print` on the standard-library prelude path; it is re-measured after
  ACT-1050.

### 9.1 Rows R10-9 and R10-10 — the backend half

The backend half of [S124 packet](../../sprints/s124-api-packet.md) rows R10-9
and R10-10, both approved by the user on 2026-11-17; R10-9 supersedes S123 row
R10-6. The
owner, the added items and the rule "one defining module per layout" are
[heap layout owners](../intrinsics/heap-layout.md) §1–§2. Source read at
`4b58ab93`, 2026-11-16.

**Deleted from `heap.rs`, all public.** The `heap` module stays, with
`HeapCategory` and `NULLARY_THRESHOLD_I64`.

- `HeapAdt`: the struct, fields `header` and `tag`, `TAG_OFFSET`,
  `FIELDS_START`, `field_offset`, `payload_size`, and its two constant locks.
- `HeapClosure`: the struct, fields `header`, `code_ptr` and `drop_glue_ptr`,
  `CODE_PTR_OFFSET`, `DROP_GLUE_PTR_OFFSET`, `CAPTURES_START`,
  `capture_offset`, `payload_size`, and its three constant locks.
- `HeapVec`: the struct, fields `header`, `len`, `cap` and `data_ptr`,
  `LEN_OFFSET`, `CAP_OFFSET`, `DATA_PTR_OFFSET`, `payload_size`, and its four
  constant locks.

**Readers instead.**

- ADT and closure readers name `cranelisp_intrinsics::alloc::{HeapAdt,
  HeapClosure}`, and the Vec payload size reader names
  `vec_runtime::PAYLOAD_SIZE`, under R10-9's own consumer list. The item names
  and integer types match, so each change is an import.
- **The Vec offset readers are row R10-10's edge**, approved by the user on
  2026-11-17: backend → `vec_runtime::{LEN_OFFSET, CAP_OFFSET,
  DATA_PTR_OFFSET}`, three existing `pub const … : usize` items with no reader
  outside intrinsics at `4b58ab93`. The row adds no item and changes no
  signature, so the backend baseline moves +0 for it. The constants are
  `usize` where the deleted `HeapVec` constants were `i32`: `heap.rs` converts
  each once, in a constant context, naming the intrinsics constant, and
  `compiler/vec_codegen.rs` reads the converted values. The rustdoc naming
  these readers is intrinsics', in the same change-set; the root's edge to two
  of the constants is int's ([int §16.0](../int/int.md)).
- Constants composed from these layouts keep their compositions and pins and
  read the intrinsics items, for example `compiler/apply.rs`'s
  `PURE_GLUE_ABS_OFFSET` (release contract §5.5).
- `compiler/control_flow/dependent_spark.rs`'s `IVAR_RC_OFFSET`, a literal
  `8` for the header's count, is deleted for `HeapHeader::RC_OFFSET`.

**Outside this crate, in the same callee-first migration.** The binary's
readers move to the intrinsics items: `src/display.rs` (`HeapAdt`, `HeapVec`)
and `src/session_v4/test_runner/run.rs` and its tests (`HeapAdt`).
`src/session_v4/test_runner.rs` writes the ADT, closure and Vec layouts as
literals, the closure capture at `32` among them; the row approves its edge to
`alloc::HeapClosure`, and replacing those literals is int's
([int §16.0](../int/int.md)).

**Expected baseline effect.** Backend `public-api.txt` −49 lines in the
current format (`HeapAdt` 15, `HeapClosure` 17, `HeapVec` 17), or −28 in
K11-a's format, all R10-9's; R10-10 adds +0. No schema, ABI or layout value changes, so emission is
byte-identical and the golden corpus is unaffected.

- **R10-6 does not land.** `HeapClosure` is deleted, not narrowed, so B7
  carries no `HeapClosure` change and its 17 lines are within this row's −49.
- **Residual.** A literal offset against an ADT, closure or Vec base evades a
  census of named constants; `IVAR_RC_OFFSET` is one such instance here. The
  falsifier is intrinsics' ([heap layout owners](../intrinsics/heap-layout.md)
  §4).

## 10. Cross-references

- `design/arch/bounded-contexts.md` §3 — the bounded context, boundary and
  invariants (authoritative over anything here)
- `design/arch/backend-keyed-consumer.md` — the keyed-consumer end state
  summarised in this document, and the `VarRef`/`ApplyRef` carrier sums
  consumed here
- `design/arch/concrete-boundary-type.md` — why the type the backend classifies
  has no variable case
- `design/arch/principles.md` — the principles cited above
- `crates/cranelisp-backend/AGENTS.md` — seam map, debug hooks, code conventions
- `crates/cranelisp-backend/src/` — the implementation, and the rustdoc that is
  the facade
