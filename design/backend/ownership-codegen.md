# Ownership codegen

**Owner:** `design`, narrow-deployed to `cranelisp-backend`. **Subordinate to:**
[backend.md](backend.md).

**Status:** the current design of the backend mechanisms that consume the
ownership analysis — what is built, the contracts it rests on, and the parts
that are designed but not built. Verified against source on 2026-09-21;
§3.4, §13.3, §13.5, §13.7 and §15 row 2 re-verified on 2026-09-30. Section
numbers are cited from source and tests and are kept stable; the increment
ladders, as-built narratives and falsified analyses that used to fill this
document are in Git history.

**Governing authority:** [the ownership spine](../arch/ownership-inference.md)
(arch). Where this design and the spine disagree, the spine governs. The
producer of every fact consumed here is
[typecheck's ownership inference](../typecheck/ownership-inference.md).

> **Standing invariant.** The conservative lowering — every parameter `Owned`,
> every RC operation atomic, every allocation on the RC heap — is permanently
> reachable under the master analysis-off toggle (§2), and every mechanism below
> is gated by a present fact whose absence selects the conservative path. The
> conservative path is the spine's all-`Owned` oracle
> ([spine contract](../arch/ownership-inference.md#62-the-differential-oracle-r7)), not a frozen historical
> baseline: where the conservative lowering itself was wrong (§13.7) it was
> corrected in both polarities.

---

## §0. Scope and state

| Mechanism | Section | State |
|---|---|---|
| Master analysis-off toggle and cache key | §2 | Built |
| Borrow elision | §3 | Built: caller skip-inc and temporary post-call dec, `Borrowed` callee params, `Fresh` return-protect elision, in-frame projection elision at the consumer seam, the adaptation helper, the Decision-24 wrapper. **Not built:** producer-side escaping-projection elision (§3.3) |
| Stack placement for `NoEscape` | §4 | Built for scalar-payload ADT constructor calls. Closures and Vec literals decline; the region arena is deferred (§4.4) |
| Non-atomic RC for `Confined` | §5 | Built for materialization incs through the node carrier; through-binding sites stay atomic |
| Uniqueness and reuse | §6 | Built: static-proof elision of the Vec COW rc==1 check, and the reuse hit/miss counters. **Not built:** general drop-guided reuse tokens (§6.1) |
| One-word value flattening | §7 | Built |
| Redefinition machinery (backend half) | §8 | Built |
| Dual-symbol extern convention | §9 | **Carrier only**: `Realization::ExternShim { borrowed_sibling }` exists and is cache-validated, but no sibling is registered and no emission gate selects one |
| Vec-query trio in value position | §12.7 | Built |
| Supporting contracts (golden oracle, counters, wrapper and COW contracts, spark density, unit scenarios, producer pins) | §13 | Current; the ACT-1021 and ACT-1024 COW corrections (§13.3, §13.7) are in the working tree, uncommitted; K4 is complete and `qa` judged it adequate; user acceptance is pending |
| RC/alloc seam assertion density | §15 | Rows 5–6 built; row 2 retired; rows 1, 3 and 4 open |

---

## §1. Seams

The mechanisms land on existing seams; there is no new pipeline stage, graph or
store. The main ones, by module (the seam map is `crates/cranelisp-backend/CLAUDE.md`):

- **`cranelisp-backend/src/heap.rs`** — the RC emission helpers, the atomicity decision
  (`use_nonatomic_arm`), `emit_stack_alloc`, `compute_last_uses`,
  `HeapCategory::classify`. Only `cranelisp-backend/src/heap.rs` imports layout constants, so
  atomicity and slot-initialisation changes stay local to it.
- **`compiler/apply.rs`** — moded argument lowering
  (`compile_consuming_arg_list_moded`), direct and GOT-indirect calls, the
  stack-eligible constructor path.
- **`compiler/fn_compiler.rs`** — `Borrowed` parameter registration, the return
  protect, the stack-eligibility gates, the tail-call scope flush.
- **`compiler/vec_codegen.rs`** — the inline COW cores and their polarity
  contract, `vec-get` projection elision, the element adapters.
- **`compiler/control_flow/fn_as_value.rs`** — value-position and auto-curry
  wrappers, `emit_d24_adaptation`.
- **`compiler/control_flow/sparkability.rs`** — the spark density axis.
- **`cache/`** — the ownership toggle as a manifest key.

Typecheck supplies mode summaries on monomorphic definitions and advisory site
facts on `MonoExpr` nodes; the backend reads them and derives no ownership,
escape, confinement or uniqueness of its own.

---

## §2. The master analysis-off toggle

### 2.1 One switch

`CRANELISP_NO_OWNERSHIP=1` forces the conservative point everywhere. Enforcement
is producer-primary: typecheck's ownership pass does not run, so no summaries,
site facts or value-use marks exist, and every consumer takes its absent-fact
arm. The backend reads the same polarity (`ownership_analysis_off`) where it
must, including the cache manifest. The toggle is the permanent differential
oracle switch; the default is analysis-on.

### 2.2 Absent facts select the existing code

Producer-side gating does not by itself prove the conservative lowering is
unchanged, so the backend is shaped to make it so:

1. **The else-arm is the existing helper.** Each mechanism is a guard of the form
   `if let Some(fact) = … { new emission } else { the existing helper call }`.
   The conservative arm is never a copied or reflowed variant.
2. **No unconditional new instructions.** A mechanism emits nothing on the
   fact-absent path. The redefinition machinery (§8) is the one exception class,
   and it runs only on the redefinition path.
3. **Derived artifacts are fact-conditional.** Adapter work in wrappers exists
   only for non-conservative summaries; with the toggle off none exist.
4. **The differential evidence is `qa`'s**: toggle-off CLIF against the golden
   corpus (§13.1), and analysis-on versus analysis-off observable output.

### 2.3 The toggle is a cache invalidation key

A cache written analysis-on persists moded summaries and machine code compiled
against moded conventions; loading it analysis-off would pair conservative
callers with borrowing callees. The toggle's polarity is therefore one of the
manifest's global invalidation dimensions alongside the compiler fingerprint,
target and format: flipping it invalidates the whole cache. Mixed-ABI caches are
unrepresentable, at the price of a rebuild on flip.

### 2.4 The measurement probes

`CRANELISP_NONATOMIC_RC` (a documented-unsound blanket non-atomic probe) and
`CRANELISP_CAPTURE_BORROW` (the opt-in spark capture-by-borrow) remain
independent, off-by-default measurement toggles. §5 shares the former's emission
arms under sound per-site gating; the latter still exists beside the inferred
`Borrowed` classification. Neither participates in the canonical run or the
golden corpus.

---

## §3. Borrow-elision emission

### 3.1 Caller side

At a statically resolved call, `compile_consuming_arg_list_moded` reads the
callee's entry convention — derived once from the keyed callable's realization
([non-concrete-release-contract.md](non-concrete-release-contract.md) §7.6) —
and emits per position through the pure `moded_arg_rc`. Only a compiled `Body`
with a non-conservative summary can yield a borrowed position; every other
realization, and an absent summary, consumes:

| Argument | Callee param `Owned` | Callee param `Borrowed` |
|---|---|---|
| Owned binding (`Var`) | consuming inc (unchanged) | **no inc**; the caller's scope cleanup is the single dec |
| Temporary | no inc; ownership transfers | no inc, and a **post-call dec** of the temporary |

A `Var` naming a function value or bare constructor is a fresh temporary, not an
owned binding. Closure calls, constructors, externs and platform effects stay on
the Decision-24 convention permanently.

### 3.2 Callee side

`bind_defn_params` registers each heap `Borrowed` parameter in `borrowed_vars`.
Everything follows from the existing borrowed discipline: no scope dec, never a
last-use transfer, and passing it onward to an `Owned` position fires the
ordinary consuming inc (adaptation is the default). **Invariant:** a `Borrowed`
parameter never reaches the return path — the analysis widens returned
parameters first — asserted by a `debug_assert!` on the return path in
`fn_compiler.rs`.

### 3.3 Result modes and projections

- **`ResultMode::Fresh`** — `return_is_fresh_by_summary` elides the return
  protect when a present summary says `Fresh`. `Fresh` is a *provably not
  aliased* claim, so the declared fact table must never let a primitive that may
  alias an argument declare it; the COW primitives therefore declare
  `MayAliasOf(0)` ([spine](../arch/ownership-inference.md) §3.7).
- **`MayAliasOf(i)`** — a conditional alias (the COW fast path returns its
  argument's box). Not `Fresh`, so the protect is kept; classified
  non-conservative, so adaptation still fires. No emission arm of its own.
- **`AliasOf(i)`** — an unconditional alias; emission-neutral for the caller.
- **`ProjectionOf(i)`** — the result is a borrowed view into argument `i`'s root.
  It keeps its materialization; the adaptation helper never adds a second inc
  (§3.4).

**In-frame projection elision (built, consumer-driven).** When a direct `vec-get`
projection carrying the `provenance` site fact is passed **directly into a
`Borrowed` parameter**, the element inc and the post-call dec collapse: the
consumer seam sets `elide_vecget_span` and `emit_vec_get_core` skips the inc for
that span. This is the one shape where the borrowed element provably neither
escapes the expression nor outlives the root, which the caller holds across the
call.

**Producer-side escaping-projection elision (not built, gated).** Eliding the
read's inc at the `vec-get` and lending the view past the consumer seam
(returned, stored, or passed to `Owned`) is **parallel-unsound** without more:
under lenient evaluation a sibling strand can COW or free the root while the
escaped view is live (reproduced as same-seed non-determinism). It is admissible
only when the root is proved `Confined` or uniquely owned across the escape —
the §5 and §6.4 facts. Its design, if taken up: `ProjectionOf` propagation across
returns, `Let`-bound projections joining `borrowed_vars`, and a `compute_last_uses`
extension in which each use of a provenance-carrying binding also records a use
of its root, so the root's release orders after every rooted projection.

### 3.4 The adaptation helper

The per-edge delta between Decision 24 and a moded convention is mechanical and
has one emitter, `emit_d24_adaptation` (`fn_as_value.rs`), consumed by the
value-position wrapper bodies and by auto-curry. It emits a post-call release
for each parameter the derived entry convention marks borrowed, and no result
inc — a moded callee always returns an owned reference, so callee
materialization and wrapper adaptation never both increment. It reads the
derived convention, never a declared `Mode`: only a compiled `Body` can borrow,
so an extern shim's wrapper adapts nothing whatever the shim declares. The
derivation, and the separately scheduled typed release of the borrowed
parameter, are
[non-concrete-release-contract.md](non-concrete-release-contract.md) §7.6.

### 3.5 The Decision-24 wrapper

The existing value-position and auto-curry wrapper bodies **are** the Decision-24
adapters: when the target's derived entry convention borrows a parameter —
only a compiled `Body` can — `emit_wrapper_call` injects `emit_d24_adaptation`
around the call; every other target calls through unchanged, and an extern shim
always receives its argument owned. No separate adapter symbol is minted, and
auto-curry composes through the same seam, so adapters never stack.

> **Invariant.** Every code pointer reachable from a closure value targets a
> Decision-24-conformant entry. A moded body is reachable only from statically
> resolved call sites and these wrapper bodies; no other path takes its address.

---

## §4. Stack placement for `NoEscape`

The mechanism is live: `STACK_ALLOC_ESCAPE_FACT_SOUND = true`, with
`CRANELISP_NO_STACK_ALLOC=1` as the fine runtime oracle and
`CRANELISP_NO_OWNERSHIP` as the coarse one.

### 4.1 Eligibility

`emit_stack_alloc` creates a stack slot of `HeapHeader::SIZE + payload`, takes
its address and initialises the header exactly as `alloc_with_rc` would except
for the immortal RC (§4.2), so every downstream store and RC/COW/drop path runs
unchanged against the stack address.

The escape fact lives on the use-site `Apply` of a constructor (the allocation
in the caller's frame), not on the synthetic constructor body.
`FnCompiler::constructor_call_stack_eligible` computes the verdict there,
requiring `escapes == Some(false)` and all five gates, each conservative:

1. **Statically sized** — always true for a constructor call.
2. **All-scalar payload** — every field classifies `NeverHeap`. A stack aggregate
   holding heap fields would owe a frame-exit field release its drop glue never
   runs.
3. **Not reachable by a TCO back-edge** — declined for the whole function when it
   self-calls, because the escape fact is per frame and a loop iteration would
   reuse the slot under a live reference.
4. **Backend-emitted** — extern bodies allocate through `alloc_with_rc` and
   cannot be redirected without an allocator seam (§4.4).
5. **Not relocated into a spark thunk** — §4.3.

Scope: scalar-payload ADT constructor calls only. Closures and Vec literals
decline (a Vec literal allocates through `runtime/vec_new`; closures need a
scalar-capture gate). Declining is always sound. Stack bindings get no scope
dec.

### 4.2 The immortal header

Stack slots keep the standard header with `rc = IMMORTAL_RC` (`1 << 62`). Any
residual RC traffic a `NoEscape` value meets — adaptation incs, callee consuming
decs, guarded ops — is a harmless drift on a frame-local cell; the free path
(`old == 1`) is unreachable, so `dealloc` never sees a stack pointer; and the COW
unique check never succeeds, so a buffer-freeing grow path is unreachable. No
call site changes for stack-ness. When stack placement extends to Vec literals,
vecs with in-frame writes should decline, because they would never mutate in
place.

### 4.3 Spark relocation — gate 5

A joined spark reading a parent-frame slot through a borrowed capture is sound:
the parent frame is live across spark and join, and suspension crossings are
escape edges typecheck already classifies.

A construction the **backend itself relocates** into a spark thunk is different,
and the escape fact cannot see it: lenient evaluation synthesizes thunk bodies
for sparked apply arguments and `let` bindings, and a construction moved there
carries the fact computed for its original frame while its slot lives in a thunk
frame that pops at the join. Gate 5 declines every stack placement while
`FnCompiler::in_spark_thunk` is set. The flag is raised by the one
`compile_spark_thunk` helper for apply-argument and independent-`let` sparks,
set directly on the dependent-`let` thunk's compiler, and propagated into lambda
bodies by `compile_lambda_body`. Constructions genuinely written inside a thunk
are also declined — a conservative over-decline accepted because the win there
is marginal. Under `CRANELISP_NO_LENIENT` no thunk exists and the gate never
fires.

### 4.4 The region arena — deferred

An arena for `NoEscape` allocations of one structural lifetime (a `let` body, a
match arm, a `ParBind` arm) would reach dynamically sized and extern-produced
allocations. It consumes the same escape facts, shares the immortal-header
discipline, and frees a `ParBind`-arm arena in the joining parent after the join.
**Trigger to design it:** an allocator seam that lets extern allocations be
redirected, **and** a fixture whose hot allocation is `NoEscape` and dynamically
sized or extern-produced, so the arena would deliver a measured win stack slots
cannot.

---

## §5. Non-atomic RC for `Confined`

### 5.1 One decision point, two gates

`RcAtomicity { Atomic, NonAtomic }` feeds a single decision,
`heap::use_nonatomic_arm`: the per-site gate or the process-global probe. The
gated helpers have `_atomicity` siblings, and the plain names delegate with
`Atomic`, so non-participating call sites are untouched. Soundness rests on
typecheck's op-wise per-cell join: a cell is `Confined` only if every surviving
RC operation on it runs on the owning strand, so mixed emission cannot race. The
backend performs no strand reasoning.

The live carrier is `node_confined(&MonoExpr)`, read where the producing node is
in hand; its consumer is `protect_return_value`, so a parent-strand return
allocation's materialization inc goes non-atomic. As typecheck's confinement
precision grows, more nodes go non-atomic with no backend change.

**Through-binding sites stay atomic.** The consuming inc of a `Var` argument,
the Vec scope-cleanup dec, the match auto-upgrade and the tail-flush protect pass
`Atomic` literally, because the analysis produces no confined `let` binding
today. A `Symbol`-keyed carrier for them was removed: it was provably always
empty, and with no shadow save/restore it would have leaked an outer confined
verdict onto an inner crossing binding — a data race. **Re-add rule:** only once
the analysis confines a `let` binding, and then either with save/restore on
shadowing or keyed on the Cranelift `Variable`, never on the name.

### 5.2 What stays atomic

Operations emitted inside shared artifacts have no site identity:

| Artifact | Why it stays atomic |
|---|---|
| Vec element inc/dec adapters | one function per element type serves every vec of that shape |
| Rust-side copy loops and `rc_inc`/`consume_shallow` | inside extern bodies; would need dual extern variants |
| ADT and closure inline drop and scope-cleanup decs | open-coded outside the gated helpers |
| COW consumed-source decs and static vec-op decs | their sources are crossing in the measured corpus |

`emit_vec_rc_dec_with_drop` has an atomicity input, but no confined verdict
reaches it.

### 5.3 The free path

The non-atomic dec keeps the `old == 1` → drop glue → `dealloc` sequence and
omits the Acquire fence: single-strand cells need no publication ordering.

---

## §6. Uniqueness and reuse

**Binding constraint (spine §3.5):** reuse tokens and uniqueness bits are
function-local — never parameters, returns or fields. Nothing here changes the
call ABI.

### 6.1 General drop-guided reuse — not built

The designed mechanism, retained for whoever takes it up: at a last-use
consuming dec whose value's layout matches a downstream allocation in the same
function, replace the free path with `token = (rc == 1) ? ptr : 0`; at the
allocation, branch on the token to re-initialise in place or allocate as today.
The token is an SSA value between two in-frame sites; pairing is intra-function,
greedy and conservative (no pair ⇒ today's code). No such pairing exists in
source; the built reuse is the Vec COW path below.

### 6.2 Bulk operations — one check per call

The inline COW cores make the in-place-versus-copy decision **once per call** by
the dynamic `rc == 1` check. A shared vec's first write copies, the copy is
unique by construction, and later writes in the chain go in place: copy once,
then in place, with no loop-level machinery.

### 6.3 Cost of the dynamic check

An uncontended atomic load, compare and branch — single-digit cycles in the
shadow of the call — against, for a grid-shaped vec, one buffer allocation plus
per-element incs and a free per write. The design question is where the check
can be elided, not whether to emit it. **Hazard:** reuse on a non-unique value is
heap corruption; the reuse emission needs value-correct and heap-balanced
evidence under allocator perturbation.

### 6.4 The static-uniqueness proof elides the check

The proof is an elision layer over the dynamic check, never a second mechanism:

- **`unique_static: Option<bool>`** on fresh-producing nodes, read by
  `node_unique_static`. `Some(true)` at a COW site emits the in-place arm with
  the `rc == 1` load and compare replaced by a constant; `Some(false)` or `None`
  emits the dynamic check unchanged.
- **`result_unique`** on callee summaries lets a caller mark its use of a call
  result proven unique, chaining the proof across calls. The backend reads it;
  it derives no uniqueness itself.

There is exactly one emission shape with the check optionally elided, and no
uniqueness-specialised body. **The proof-elided arm has no dynamic backstop**, so
the reuse-corruption evidence must cover a proof-elided reuse, not only a
dynamic one.

### 6.5 Reuse counters

The COW cores emit `runtime/reuse_hit` on the in-place arm and
`runtime/reuse_miss` on the copy arm, gated at codegen time on
`CRANELISP_RC_STATS` (off ⇒ no emitted IR). Reuse permission is dynamic, so the
split is a runtime tally, reported in the `[RC_STATS]` line (§13.2.1).

---

## §7. One-word value flattening

### 7.1 `HeapCategory::Value` and its single source

`HeapCategory::Value` marks a concrete type represented inline: no header, no
refcount, no drop glue, with constructor and field structure kept for
construction and match. Eligibility is one predicate with two soundness-coupled
consumers — typecheck's `Copy` mode classifier and the backend's layout — so it
lives once, in `cranelisp-types`: `value_layout(ty, …) -> Option<ValueLayout>`
with `VALUE_LAYOUT_MAX_WORDS = 1`. `HeapCategory::classify` delegates to it and
derives no predicate of its own. A `Copy` mode over an unflattened
representation would be a missing increment, which is why the predicate must not
be duplicated.

At a `Value`-typed site: construction is a bare move of the single field into
the word; field read and match are bare moves; there is no RC at consuming
positions or scope exit and no `borrowed_vars` entry; and a `Value` field inside
a heap ADT or Vec is skipped by drop glue exactly as a `NeverHeap` field is.

### 7.2 One word, single constructor

Every ABI surface is uniformly i64, so a one-word `Value` crosses every boundary
unchanged. Multi-constructor types (which need a tag word) and types wider than
one word stay heap-represented and RC-shared — sound, just unflattened.
**Trigger for multi-word flattening:** a fixture whose hot type is Copy-eligible
but wider than one word; its shape (element stride, multi-slot returns, boxing
at word-sized edges) is designed then. A flattened value never meets the nullary
tag guard as tag-or-pointer: classification is total post-mono and a `Value`
type classifies `Value` at every site.

### 7.3 Vec of values

The Vec runtime's element inc/dec pointers are nullable, and null already means
"no per-element RC" — how `Vec Int` works. A Vec of one-word values is emitted
with null element functions and behaves like `Vec Int`: its copy does no incs and
its drop walks nothing. No runtime code was added.

### 7.4 Cache and `--link` parity

Layout is a deterministic function of the type definitions (persisted in the
module metadata and chain-followed to one defining module), the size bound (a
constant) and the toggle (a manifest key), so every compile of cache-valid
inputs makes the same flattening decisions. Flattening changed compiled
representation and bumped `CACHE_SCHEMA_VERSION`; any future change to the
predicate or bound must bump it again.

### 7.5 Trace and display descriptors

The descriptor baker reads the same classification and renders a flattened value
from its raw word with its constructor name. No platform-visible type flattens;
platform ABI edges stay boxed.

### 7.6 Compatibility rules

- Matches over `HeapCategory` stay exhaustive; no wildcard collapses `Value`
  into another arm.
- A `Copy` parameter emits no inc, no dec and no `borrowed_vars` entry.
- Stack placement and reuse key on allocation size and site facts, so
  flattening only removes candidates from them.
- No code may assume "heap-typed ⇔ has a header" beyond what `classify` says.

---

## §8. Redefinition machinery — the backend half

The session transaction (reverse index, affected-set closure, cascade
reporting, frozen-slot retention) is int's
([session-transaction.md](../int/session-transaction.md)); this section is the
backend's contribution. Slot holes are never reclaimed.

### 8.1 The trap stub

A symbol broken by a redefinition cascade gets a per-symbol stub:
`iconst msg_ptr; iconst msg_len; call runtime/panic; return 0`. It compiles with
signature `() -> i64` and never reads its arguments, so one body is safe for any
caller arity under the uniform all-i64 convention on SysV x86-64 and AAPCS64
(register arguments are caller scratch, stack arguments are caller-cleaned).
That is what makes patching the broken symbol's **existing** slot sound for
unrecompiled callers. A shared intrinsic cannot do this, because the slot holds
one bare pointer and no side channel says which symbol was hit.

- **The message** is session-owned UTF-8 with no terminator, baked as
  `(ptr, len)`. It must live exactly as long as the returned `Code` handle; a
  broken symbol later recovered with a new ABI leaves its old slot on the stub
  for the session's life.
- **Known leak:** the caller's consuming incs on heap arguments are not released
  when the stub raises — one reference per trap invocation, the same caveat as
  every runtime panic ([backend.md](backend.md#7-runtime-failure)).

### 8.2 Fresh slots and frozen slots

An ABI-changing redefinition allocates a fresh slot through the ordinary
monotone allocator, and recompiled callers embed it through the unchanged GOT
load, so slot versioning needs no emission change. The ABI-preserving path stays
the in-place slot patch. The per-module GOT slab's base is baked into finalized
code, so the slab must never move while slots grow; retaining superseded `Code`
is int's session pool.

### 8.3 The interface to int

1. `compile_to_module` — unchanged, called per affected symbol.
2. `compile_trap_stub(msg_ptr: *const u8, msg_len: usize) -> Result<(*const u8, Code), CompilationError>`
   — builds the stub in a fresh per-symbol JIT (so `runtime/panic` resolves
   through ordinary intrinsic registration) and returns the pointer to store in
   the slot plus its retention handle.
3. The GOT's `store_slot` and slot allocation — existing. Freezing a slot is
   session bookkeeping, not a GOT mechanism.

---

## §9. The dual-symbol extern convention

### 9.1 Pattern

For a hand-audited extern whose declared facts mark a parameter only-read, a
borrowed-convention sibling can sit beside the untouched consuming export,
authored as one shared core with two exports so the bodies cannot drift. The
carrier is `Realization::ExternShim { borrowed_sibling }`, cache-validated at
load. No primitive registers a sibling, and no call site selects one.

### 9.2 Candidates

`vec-len` is not a candidate: it is inline-lowered at every site and now
declared `user_inline`. `str-len` was chosen as the template instance to prove
the pattern end to end, not for a measured win, and was not built. Further
candidates are data-gated on a per-extern adaptation attribution showing a pair
population worth removing.

### 9.3 The emission gate

If built, a call site targets the sibling only when **all** hold: the declared
fact marks the parameter only-read, the argument is borrowed at the site, a
sibling is registered, and analysis is on. Any false leg takes the consuming
export with today's emission. A selected sibling needs its own explicit case in
the entry-convention derivation, and a closure wrapper never selects one: it
always calls the consuming primary entry
([non-concrete-release-contract.md](non-concrete-release-contract.md) §7.6).

### 9.4 `neq-string` is a primitive entry

Declared ownership facts attach only to symbols with a primitive table entry.
`neq-string` — the `!=` twin of `str-eq`, reached through `Eq` dispatch — is
registered as one, so `(!= s1 s2)` gets the same `Borrowed` facts as
`(== s1 s2)`. The scalar `neq-*` siblings stay entry-less: their arguments carry
no RC, so the conservative default costs nothing.

---

## §10. What must not ship

- A reuse token or uniqueness bit on any ABI surface.
- A mode on a closure, constructor, extern or platform ABI edge beyond
  adaptation and declared facts.
- A backend-local escape, strand or uniqueness analysis duplicating typecheck's.
- An emission change on a fact-absent path (§2.2).
- GOT slot-hole reclamation.

---

## §11. Quality attributes

- **Simplicity.** Every mechanism rides an existing seam: the non-atomic arms,
  the wrapper bodies, the null element-function path, the panic machinery and
  the slot allocator. Net-new machinery is stack-slot emission with its
  sentinel, the adaptation helper, the trap stub and one manifest key.
- **Maintainability.** Atomicity and slot initialisation stay in `cranelisp-backend/src/heap.rs`; mode
  consumption concentrates in argument lowering and parameter binding.
- **Observability.** `[RC_STATS]` attributes the mechanisms (§13.2), the CLIF
  dump shows fact-gated deltas, and the toggle gives every observation an A/B
  baseline.
- **Concurrency safety.** The backend adds no strand reasoning and no shared
  state; confinement and escape arrive as typecheck verdicts. The immortal
  sentinel (§4.2) and the else-arm discipline (§2.2) are this crate's structural
  guards.
- **Performance.** Acceptance rides `qa`'s measured bars, never estimates here.

---

## §12. Open questions routed onward

The questions this design routed onward were delivered or are carried by the
sections above: the byte-identity lanes (§13.1), elision and stack-slot fences
(§3, §4), the reuse fence (§6.3), trap-stub behaviour (§8.1) and sibling
attribution (§9.2). One settled defect keeps its number because source cites it.

### 12.7 Vec-query trio in value position

`vec-get`, `vec-set` and `vec-push` are inline primitives: a single extern body
cannot know the element's heap category, so they have no callable body. Used as
a value — passed to a higher-order function, or partially applied — they
previously reached a GOT call through a null slot. The value-position and
auto-curry wrappers now lower them inline through the shared builder-parameterized
cores (`emit_vec_query_into`), selected by the kind-keyed
`is_inline_primitive_at`, with the element type plumbed from the value's concrete
function type. Every wrapper parameter arrives owned, so `vec-get` incs the
element per its category and releases the consumed vec, and `vec-set`/`vec-push`
transfer the element into the vec with the COW `rc == 1` path available. An
absent element type is a located refusal, never a default.

---

## §13. Supporting contracts

### 13.1 The golden-CLIF oracle — backend facts

The corpus, capture contract, configuration pins, exclusions and scoped
re-baseline discipline are `qa`'s, in
`tests/fixtures/clif_baseline/MANIFEST.md`, with the rule at the
[spine contract](../arch/ownership-inference.md#62-the-differential-oracle-r7). The backend guarantees what the
oracle relies on:

- `CRANELISP_CODEGEN_DUMP` writes each function as one framed block on
  **stderr**, keyed `module::symbol`.
- Under `--no-cache` each symbol codegens once, so one frame per symbol. A
  duplicate frame means a cache pass leaked in or a symbol was compiled twice —
  a finding, never deduplicated.
- Frame content is deterministic for fixed source and configuration, and wrapper
  names and slot immediates are load-bearing identity, so nothing is
  canonicalised.
- The oracle sees the JIT pass only. The object pass's function-reference
  declaration order depends on scheduler timing, so its bytes are not
  reproducible; a mechanism gated on module type is invisible to this oracle and
  needs a mode-equivalence lane instead.
- An emission-affecting change lands its attributed scoped re-baseline in the
  same change-set; a non-empty diff from a pure refactor means the refactor is
  wrong ([backend.md](backend.md) §5).

### 13.2 Mechanism attribution

#### 13.2.1 The `[RC_STATS]` line

With `CRANELISP_RC_STATS` set, the process-exit line appends the
per-mechanism family after the original four fields, so positional parsers keep
working:

```
[RC_STATS] rc_inc=N rc_dec=N allocs=N deallocs=N \
           stack_slot=N reuse_hit=N reuse_miss=N rc_nonatomic=N rc_atomic=N \
           str-len_adapt=N alloc_bytes=N
```

- `rc_inc`, `rc_dec`, `allocs`, `deallocs`, `reuse_hit`, `reuse_miss` and
  `alloc_bytes` are **runtime** tallies.
- `stack_slot`, `rc_nonatomic` and `rc_atomic` are **codegen-time** counts,
  honest for `--run` and the REPL (compile and run share a process) and honestly
  zero for a `--link` binary, which did no codegen.

The counter state and the print surface live in `cranelisp-intrinsics::rc`; the
backend is the sole writer, pushing (`tally_stack_slot`, `tally_rc_emit`) from
host code during compilation. The pushes emit no IR.

#### 13.2.2 Finer measurement seams

Each reads a signal codegen already computes and emits no IR when off; none
changes a public API, a `cranelisp-types` item or a C-ABI symbol:

- **N1 — allocation bytes** — `alloc_bytes` in `[RC_STATS]`, read from the
  allocator's existing byte counter. Built.
- **N2 — per-branch allocation attribution** — not built. If needed, the minimal
  form is a two-bucket in-spark versus parent tally keyed off a thread-local
  marker the spark runtime sets; a per-site dump needs a compile-to-run site
  channel and is heavier.
- **N3 — per-site residual atomic RC** (`[RC_SITE_STATS]`) — built in
  `rc_site_stats.rs`: a codegen-time map at `use_nonatomic_arm` keyed by
  enclosing function and span with the confinement class, dumped by a
  backend-side exit hook, so it needs no intrinsics print path.
- **N4 — fine stack oracle** — `CRANELISP_NO_STACK_ALLOC=1`, read once at codegen
  and ANDed with `STACK_ALLOC_ESCAPE_FACT_SOUND`, declines stack placement only
  while every other mechanism stays live. Built.

### 13.3 Wrapper and COW contracts

**Wrapper identity.** Value-position wrappers are span-keyed and include the
enclosing function's discriminator (`__wrap_{name}_{disc}{start}_{end}__`), so
distinct monomorphisations of one enclosing function never share a wrapper
symbol. Any signature ever embedded in a wrapper name must use the same total
fully-qualified grammar as the monomorphisation mangler — a lossy key would
reopen the mangler collision class one level down. A proposed scheme keying
wrappers by dispatch identity and concrete signature was not built.

**Curry drop-glue identity.** A curry wrapper's capture drop glue is keyed
identically to its wrapper (`curry_drop_glue_name(disc, span)`): a closure and
its glue are one object with one identity, so distinct monomorphisations at one
span get distinct glue, and the two arms of one create gate share one.

**Dispatch is kind-driven.** `emit_wrapper_call` selects its arm from the
entry: an inline primitive lowers inline (§12.7); a slotted conservative target
calls through its slot; a slotted non-conservative target calls through its slot
inside the adaptation (§3.5).

**COW source polarity.** The COW cores take an explicit
`SourceOwnership::{Owned, Borrowed}`; the copy branch releases the consumed
source iff `Owned`. Wrapper and curry bodies pass `Owned`. The mutate and grow
branches return the same box, whose ownership the settled §13.7 contract governs.

**The tail-call flushes.** Decs emitted after a tail self-call's jump never
run, so two flushes release before it:

- the heap `let`/match/lambda bindings in scope frames `[1..]`
  (`flush_let_scopes_before_tail_jump`);
- the superseded heap parameters in frame `[0]`
  (`flush_superseded_heap_params_before_tail_jump`).

Which old slot each flush releases is the
[§6 predicate](transitive-drop-glue.md#6-tco-replacementtransfer-predicate).
This section owns the other half: every value handed to the next iteration
must carry exactly one owned reference.

| Argument shape | Treatment |
|---|---|
| Bare top-level `Var` `(recur v)` | a move: the slot's own reference travels, and the flushes skip that slot |
| Control-flow forward `(recur (if c a b))`, `(recur (match … a))` | a branch or arm that yields a bare `Var` increments it at the branch tail (`maybe_protect_tail_arg_alias`) when the rule below says so. Which binding travels is known only at runtime, so the increment is per branch |
| Consumed into a fresh value `(recur (wrap v))` | the consuming increment already gave the fresh value its own reference |

**The branch-forward rule.** A branch-forwarded `Var` never receives its slot's
reference: only a top-level move, and the analysis-on in-place COW row of §6,
do. So the branch increments exactly when the resolved slot holds a frame-owned
heap reference:

- **in a `let`/match/lambda frame:** the slot is not borrowed;
- **in the parameter frame:** the slot is not borrowed, or the frame promoted
  it (FIXME 0720's entry increment).

Consequences:

- **Transfer rows are deliberately not consulted.** In `(recur v (if c v w))`
  the top-level `v` takes the slot's reference, and the branch copy needs its
  own. A "released at the jump" key would skip that increment and leave two
  slots on one reference.
- **A parameter consumed by an in-place COW argument is still incremented
  when a branch also forwards it.** In `(go (if c p q) (vec-push p 1))` the
  COW's `p` is its last use, so without the increment an in-place push would
  share `p`'s box with the branch copy. With it the push sees two references
  and copies, and the consuming COW releases the slot's reference (below).
- **Borrowed, unpromoted parameters are not incremented.** Forwarded through a
  branch at its own position, such a parameter cannot occur: the branch
  supersedes the slot, so the frame promotes it. Forwarded into a different,
  frame-owned slot, it owes a reference nothing supplies (lead L4).
- **The slot is resolved, not spelled.** The rule reads the slot the `Var`
  resolves to ([binding scope](binding-scope.md) §4). Promotion is a
  parameter-frame fact only, and never applies to a shadowing binder.

**One ownership fact, read by every tail seam.** "The slot holds a frame-owned
reference" is computed once per slot. The following all read it:

- both flush filters;
- the branch-forward rule;
- the escape-borrow gate (`tail_jump_releases_binding`), which asks whether a
  borrowed view's root dies at the jump.

"Released at the jump" is that fact combined with the §6 verdict `Replace`.
Converging the three former readings onto the one fact is what makes a
disagreement between the flushes and the increment unconstructable (Principle
[07](../arch/principles/07-single-source-of-truth.md)).

**The consuming in-place COW argument.** §6 row 3 ("in-place COW rooted at the
slot": transfer, no release) is true only when the COW takes the slot's
reference in both of its runtime branches. One fact per self-tail call decides
it, before the arguments compile:

- **The fact.** A top-level tail argument consumes a parameter slot's reference
  when analysis is on, the argument is a COW builtin site, its source is a
  bare `Var` resolving to that frame-owned parameter slot, and the source is at
  its last use, so the site lowers through the in-place core.
- **"Last use" covers the slot's uncounted aliases.** A binder that views the
  same box without holding a reference extends the source's live range: a
  `let` forward, and a variable-pattern arm binder over the bare `Var`
  scrutinee ([RC discipline](ring2-rc.md) §5.5). In
  `(match x [alias (go (vec-push x 1) alias)])` the push is not `x`'s last use,
  so the site is copy-only: the flush releases `x`, and the escape-borrow gate
  gives the forwarded `alias` its reference.
- **A copy-only site is not row 3.** A COW whose source is used later in the
  argument list, as in `(go (vec-push p 1) (if c p q))`, lowers to the copy
  extern, which neither consumes nor forwards `p`'s box. It is §6 row 5, and
  the flush releases the slot.
- **The producer reads the fact.** The fact is issued as the site's consuming
  claim (§13.7), so a consuming site's source is `Owned`: the mutate and grow
  branches forward the box with no retention increment, and the copy branch
  releases the slot's reference. This is the self-tail sibling of the
  return-COW claim (`return_cow_source_in_scope`). Every other COW site keeps
  the §13.7 classification.
- **The flush reads the same fact.** Row 3 exempts exactly the consuming
  site's slot. A consuming site never retains, so no retention enters row 3.
- **Toggle-off never consumes.** The fact is false, so the COW counts its
  source, always copies and the flush releases (FIXME 0695).

With both readers on one fact, every forward is balanced whichever branch
runs:

| Step | Branch taken | Branch not taken |
|---|---|---|
| `(go (if c p q) (vec-push p 1))` (consuming) | the increment gives `p` two references; the COW copies and releases one | the COW mutates in place and carries the slot's reference forward |
| `(go (vec-push p 1) (if c p q))` (copy-only) | the increment gives the forward its own reference; the flush releases the slot | the flush releases `p` |

The previous, name-keyed exemption offered row 3 to any COW site rooted at the
slot and gated it on the retain verdict. The copy-only order then kept the
slot's reference unreleased. Before this rule, the unincremented branch copy
absorbed that reference by accident. With the increment it leaked one
reference per iteration (`Consumed` flow). With `IntoResult` flow the retain
verdict withdrew the exemption, and the forward was freed before this rule.

**Status (2026-09-30): the branch-forward rule, the consuming-COW fact and the
fact's alias correction (below) are implemented in the working tree,
uncommitted, and not accepted.** `test`'s after-fix run (V1 part 1) passed.
The §13.7 change-set has since landed on top of them. `test`'s V2 kept the
tail family and A-T/A-V GREEN, and `review`(backend) found no blocking
finding. K4 is complete and `qa` judged Phase 5's evidence
adequate ([K4 record](../../tests/plan/s122-evidence-delta.md#final-test-visit-k4--record-and-phase-5-adequacy-2026-09-30)).
User acceptance and phase approval are pending.

- QA's D1/D2 and C-PT/C-LT gates confirmed the ACT-1021 mechanism
  ([retained record](../../tests/plan/s122-evidence-delta.md#retained-records-of-the-deleted-filings))
  and the slot-ownership key.
- `dev` implemented the branch-forward rule and the one ownership fact in the
  working tree, uncommitted. D1, C-PT, C-C1, C-C2′ and the committed subject
  flipped GREEN. C-C2 (`Consumed`) regressed to a leak of one reference per
  iteration, which falsified this section's earlier claim that the COW-first
  leak was the exemption's accepted residual.
- The consuming-COW fact above corrects row 3's reading within ACT-1021. The
  §6 verdict table is unchanged. The mechanism agrees with all four C-C2 and
  C-C2′ outcomes, and `test`'s seam view confirmed it at CLIF.
- The §13.7 contract (ACT-1024) builds on this fact. The consuming claim is
  what licenses a `Var`-sourced COW to skip its retention increment, so every
  other `Var`-sourced site retains.
- **Correction (2026-09-30, during implementation).** The consuming fact read
  the name-keyed last-use map, which ignored variable-pattern aliases.
  - **Symptom.** A committed unit went RED. It is now
    `tco_shadowing_borrow_tests::copy_only_tail_push_protects_its_forwarded_match_alias`,
    and it is GREEN with the correction. Its shape is
    `(match x [alias (go (vec-push x 1) alias)])`.
  - **Mechanism.** The site claimed `x`, so there was no retention increment
    and no flush release. The escape-borrow gate saw no dying root, so `alias`
    got no increment either. Both loop slots were left on one reference.
  - **Evidence.** `dev`'s failing CLIF confirms the mechanism. At e2e the
    same shape, with the parameter's flow `Consumed`, is a use-after-free
    under the armed stale-release check at HEAD, before the amendment and
    after it. The unit cell's regression is its absent-escape-fact
    configuration, which the retaining COW had balanced.
  - **Fix.** The alias rule above narrows the fact and leaves its two readers
    unchanged. The alias map it reads is keyed by name and never scoped, so
    it is conservative only in part:
    - a stale entry left by a non-alias rebinding can only delay a last use,
      which turns an in-place site into a copy (safe);
    - a later alias binder with the same name over a different root
      overwrites the entry, which can move the original root's last use
      earlier (unsafe). This is the existing, unmeasured lead
      [ACT-1029](../../sprints/actions/ACT-1029-alias-map-same-name-overwrite-lead.md):
      predicted class `binder-name-underkey`, with a use-after-free face. It
      is not an S122 regression, not part of ACT-1021's approved scope, and
      not confirmed. A scope-correct map waits on a confirmed face.
  - **Measured (`dev`, 2026-09-30).** The unit cell, the last-use map cells
    and both e2e probes (A-T armed; A-V in all six modes, including both link
    modes that used to crash) are GREEN after the fix. The correction adds no
    golden drift beyond QA's six classified frames. The falsifier stays: either
    probe or the unit cell RED again.
  - **Also closed, by prediction and unmeasured, except where a same-name
    alias binder intervenes (ACT-1029):** in any frame, an in-place COW
    followed by a later use of a variable-pattern alias mutates the value
    that alias names. The closure is asserted; it is falsified by that write
    observed through an alias with no same-name alias binder intervening.
    The exception is ACT-1029's: its minimal pair confirms the lead if the
    subject faults under the armed stale-release check, or its `let` twin
    shows the in-place write, while the renamed control balances. It refutes
    the lead if the subject balances armed with the correct value.

**Leads for `qa`.** Each is unmeasured unless its entry says otherwise. None
is part of ACT-1021's approved scope.

- **L2 — a borrowed pattern view forwarded through a branch.** Its root is
  released at the jump. The escape-borrow gate upgrades only a top-level `Var`,
  and the branch rule skips a borrowed slot. The prediction is a
  use-after-free.
- **L3 — promotion read by name at scope exit.** `pop_scope_with_cleanup`
  applies promotion in every frame. A borrowed pattern binder that shadows a
  promoted parameter's name would be released at its scope exit. The slot
  fact closes this, but moving scope exit onto it waits for L3's measurement.
- **L4 — a borrowed, unpromoted parameter forwarded into another slot** (QA).
  The receiving slot is frame-owned, and the branch rule does not increment a
  borrowed slot. The prediction is an over-release when that branch runs.
- **L5 — a nullary-pattern arm.** `compile_nullary_pattern` has no protect
  call, so `[None v]` in a tail-argument `match` forwards a frame-owned binding
  bare. The prediction is a use-after-free.
- **L6 — a heap-free nested scope.** `(if c (let [k 1] p) q)` relies on the
  inner scope's return protect, which fires only when that scope has a heap
  cleanup target. The prediction is a use-after-free.
- **L7 — a consuming COW the flushes do not see.** Before §13.7 landed, a
  tail-argument COW whose site recorded `escapes = Some(false)` forwarded its
  source's box with no retention increment. Two shapes then also release that
  box at the jump:
  - a `let`-bound source, `(let [v …] (go (vec-push v 1)))`, because row 3 is
    not offered in a `let` frame;
  - a COW under a branch, `(go (if c (vec-push p 1) q))`, because row 3 reads
    top-level arguments only.

  §13.7 closes both by prediction. Neither site holds the consuming claim, so
  the source is `Borrowed`, the reuse increments whatever the escape fact, and
  the flush's release balances it. The unit tier pins that neither holds the
  claim and that the `let` face retains under every escape fact; W-LOOP
  measures the flush release they share. Closure itself is asserted, with a
  named falsifier: either shape RED under the armed stale-release check.
- **L8 — a shadowing binder named like the return-COW source. Refuted as
  unreachable (`dev`, 2026-09-30, at CLIF).** The shape is
  `(defn f [v] (vec-push v (let [v (vec-push [] 2)] (vec-len (vec-push v 3)))))`.
  The name-keyed return-COW source did match the inner site, but that site is
  never in place: `compute_last_uses` is name-keyed and records the outer
  direct `Var` argument as `v`'s last use, so the inner site lowers to the
  copy extern, which never reads the source classification. The CLIF is
  identical before and after the site-keyed claim, and the predicted
  double release does not occur. The site-keyed claim (§13.7) still makes the
  misclassification unconstructable in any shape; the issuer's unit pins the
  claimed node's identity, and the L8 cell is a negative leg.
- **L9 — a return-COW body whose element argument reads the source.** The
  shape is `(defn f [v] (vec-push v (vec-len v)))`. The source is not at its
  last use, so the site lowers to the copy extern, which releases nothing,
  while scope exit still skips `v`. The prediction is a leak of one reference
  per call. It is not in ACT-1024's scope. Closing it would add the claim's
  last-use condition to the return-COW issuer.
- **L10 — an alias through a non-`Var` scrutinee or `let` value.** The alias
  rule reads a bare `Var` only. In `(match (if c x y) [a (go (vec-push x 1) a)])`
  the binder `a` may view `x`'s box without extending `x`'s last use. The
  prediction is the same fault as the corrected shape. Widening the rule to
  the provenance trace (`operand_live_binding_root`) would close it at the
  cost of more copy-only sites. The trigger is a measured fault.

The protection flag is set only while compiling an `if`/`match` that is itself a
tail argument, is cleared around the condition or scrutinee, and replaces the
unconditional return protect for a match arm in that context. A leak-balance
check reads green over this class's use-after-free, so its evidence asserts the
computed result under the armed stale-release check.

**Attribution discipline.** Design hypotheses in this area have named a
plausible but wrong seam more than once. Before fixing an RC defect here,
confirm the mechanism against `CRANELISP_RC_STATS` and the CLIF dump on the
reduced repro.

### 13.4 Spark density — the fact supply

The density admission axis is designed in [lenient-eval.md](lenient-eval.md)
§2.7 and ships disabled by default (`SPARK_DENSITY_MAX_DEFAULT = 0`). This
design's obligation is the fact supply: `spark_density` scores a candidate
subtree through the same `node_escapes` and `node_confined` readers §4 and §5
use, counting heap-result sites not covered by `NoEscape` and RC sites neither
confined nor borrow-elided. A subtree carrying no ownership fact returns `None`,
so the axis is inert and admission unchanged whenever analysis did not run.

### 13.5 Unit scenario spaces

`dev` derives unit scenarios per submodule and scenario class, and `qa` audits
coverage against these spaces. Each space's negative class — absent facts emit
the unchanged instruction sequence — is the unit-tier half of the golden
oracle.

| Seam | Scenario space |
|---|---|
| RC helpers (`cranelisp-backend/src/heap.rs`, `rc_emission.rs`) | helper × `confined` {`Some(true)`, `Some(false)`, `None`, toggle-off} → non-atomic arm or unchanged atomic arm; the unsound probe still overrides |
| Moded arguments (`apply.rs`) | {owned binding, temporary} × callee param {`Owned`, `Borrowed`, no summary} × toggle; the adaptation row; arity above eight; a recursive callee |
| Return protect (`fn_compiler.rs`) | result mode {`Fresh`, `MayAliasOf`, `AliasOf`, `ProjectionOf`, absent} × body shape |
| Tail-argument forwarding (`fn_compiler.rs`, §13.3) | slot {`let` owned, `let` borrowed, parameter owned, parameter borrowed and unpromoted, parameter promoted} × form {`if` branch, wildcard arm, variable-pattern arm, constructor-pattern arm} × also {moved by a top-level `Var`, consumed by an in-place COW argument} → exactly one increment on the forwarding branch, or none; the ownership fact is pure over slot facts and reads a shadowing binder's slot, not its name |
| Consuming COW argument (`fn_compiler.rs`, `vec_codegen.rs`, `heap.rs`, §13.3) | COW site {in-place (source at last use), copy-only (source used later, or a later use of its variable-pattern or `let` alias; an alias used only inside the site's own operands does not count)} × source slot {parameter owned, parameter promoted, `let`} × position {top-level argument, under a branch} × toggle → the fact holds only for an in-place top-level site on an owned parameter with analysis on; where it holds, the source is `Owned` and the flush skips exactly that slot, otherwise the flush releases the slot and the §13.7 classification is unchanged |
| Wrappers (`fn_as_value.rs`) | dispatch kind {user function, extern, inline primitive, constructor, trait method, operator} × use {HOF argument, partial application, returned, stored, bound} × instantiation count {1, 2 same op, 2 different ops, n} × summary × mode {REPL, `--run`} |
| COW cores (`vec_codegen.rs`, §13.7) | branch {mutate, copy, grow} × source {fresh temporary, `Var` holding the consuming claim (return-COW, self-tail), other `Var`, shadowing binder named like the return-COW source, `Var` in a nested operand of a claimed site} × call site {static, wrapper, curry} × escape {`Some(true)`, `Some(false)`, `None`} → only the first two sources are `Owned`; every other `Var` is `Borrowed` and increments on mutate and grow; the result owns exactly one reference on every branch; emission is identical across the escape axis. The shadowing binder in the return-COW shape is never at its last use, so it copies (L8, §13.3): that cell is a negative leg, and the claim's node key is pinned at its issuer |
| Match scrutinee plan (`match_codegen.rs`, §13.7, [transitive drop glue](transitive-drop-glue.md) §5) | scrutinee {fresh temporary, call result, COW site on {mutate, copy branch, copy-only path} × source {`Owned`, `Borrowed`}, binding} × arm {forwarding variable, consuming variable, constructor, wildcard} × consumer {returned, `let`-bound, tail argument} × toggle → the plan reads ownership and arm shape only; a forwarding arm emits no release, and the enclosing return adds no protect; a consuming arm releases once; a COW scrutinee plans identically to a call result |
| Vec literal element move-in | element {fresh temporary, COW-aliased result} × escape |
| Stack placement | the five gates × `escapes` × site kind → stack slot or unchanged heap; sentinel behaviour |
| Spark density (`sparkability.rs`) | facts {present, absent} × body {allocation-dense, compute-dense, mixed} × threshold boundary → admitted, declined, inert |
| Trap stub and GOT | exhaustion, freeze, in-place patch |

### 13.6 Producer pins

- **Facts are final.** Typecheck writes site facts in one annotation walk after
  its fixpoint converges, so an absent fact always means "concluded
  conservative, or did not run", never "not yet written". The backend needs no
  staleness handling.
- **Provenance is `Symbol`-keyed with a shadowing guard.** Where a body rebinds a
  name that is or roots a live provenance root, typecheck emits
  `provenance: None`, and the backend takes the ordinary materialization path; it
  performs no disambiguation of its own.

### 13.7 COW mutate and grow branches — the settled contract

A COW operation has a copy branch (`rc > 1`, a new box) and mutate/grow branches
(`rc == 1`, the same box). On the mutate and grow branches the result and the
source are one box, so the result owns a reference only if the site supplies
one. The settled contract (the R14 ruling,
[safety-invariants.md](../arch/safety-invariants.md) §4) has two inseparable
halves:

1. **Toggle-off counts every COW source.** `cow_source_ownership` classifies
   every source `Owned` when analysis is off, so the runtime `rc == 1` branch
   fires only on a genuinely unique source and the copy branch is correct by
   construction. The conservative loop allocates per iteration; that is what
   conservative means. (**R14 count-truth:** the in-place branch is sound iff
   every live independently owned reference is counted.)
2. **Analysis-on: the source has two states, and a `Borrowed` source always
   retains on reuse.**
   - **`Owned`** — the site owns the reference it consumes. The mutate and
     grow branches transfer it, and the copy branch releases it. The source is
     either a fresh producing temporary, or a `Var` whose site holds the
     **consuming claim**.
   - **The consuming claim** — this exact site takes its source slot's
     reference. Only code that also suppresses that slot's release issues it,
     and there are two issuers:
     - the function-body return-COW site, whose slot scope exit skips;
     - the consuming self-tail argument (§13.3), whose slot the flush skips.
   - **`Borrowed`** — every other `Var` source. The slot keeps its reference
     and releases it later, at scope exit or at a tail flush. The mutate and
     grow branches increment the returned box, and the copy branch releases
     nothing.

**The escape fact is not an input.** `escapes = Some(false)` truthfully says
the result stays in the frame. It does not say that the slot's release is
suppressed. Every in-frame consumer of a COW result releases it as an owned
temporary, for example:

- an inline-op temporary drop;
- a `let` binding's scope exit;
- a moded call argument;
- a match wrapper release;
- a tail-argument move.

Reading `Some(false)` as licence to skip the increment therefore released one
box twice (ACT-1024;
[QA intake](../../tests/plan/s122-evidence-delta.md#act-1023-and-act-1024--intake-2026-09-30)).
With the claim as the gate, that state cannot arise. The two halves carry
different grades
([R14](../arch/safety-invariants.md)):

- **`Borrowed` carries no retain flag — structural.** It is a unit variant, and
  both COW cores retain it (Principle
  [20](../arch/principles/20-model-invariants-by-representation.md)).
- **A `Var` source reaches `Owned` analysis-on only through the claim, and only
  code that suppresses the slot's release issues it — asserted, with a named
  falsifier.** The grade rests on a census of the two issuers, not on
  representation (Principle
  [25](../arch/principles/25-narrowing-carries-its-check.md)). The claim set is
  crate-visible, so a third writer would compile.
  - Falsifier: a write to the claim set outside the return-COW issuer and the
    self-tail call's extend-and-restore.
  - Promotion: making the set private behind its two issuers makes this
    structural. It is not scheduled.

**The claim is keyed by site, not by name.** It attaches to the exact COW node
whose slot release its issuer suppresses. A nested COW inside that site's
operands does not inherit it. A shadowing binder that spells the source's name
is `Borrowed` (Principle [24](../arch/principles/24-resolve-once.md);
[binding scope](binding-scope.md) §4). The return-COW source used to be
compared by name, so a shadowing inner site matched it. In lead L8's shape
(§13.3) that site never lowers in place, so no fault was reachable there; the
node key removes the name comparison altogether.

**Every COW result owns exactly one reference, on every branch and path.**

- An `Owned` source transfers on mutate and grow. The copy branch returns a
  fresh box and releases the source.
- A `Borrowed` source retains on mutate and grow. The copy branch returns a
  fresh box.
- A source that is not at its last use lowers to the copy extern, which returns
  a fresh box.

So a COW site is an ordinary owned temporary to every consumer, which is how
provenance already classifies it (`OwnedTemporary`). No consumer needs to know
which branch ran, and none may carry a COW-specific release rule. This is
**structural**: no retain-less `Borrowed` state exists from which a
branch-dependent result could arise.

Consequences:

- **In-place reuse survives wherever the count returns to 1 before the next
  check.**
  - A loop whose source slot is released at the jump pays one increment and
    one release per iteration, and still mutates in place. Examples are a
    `let`-bound source and a parameter whose COW sits under a `let` or a
    branch.
  - The consuming self-tail argument (`build`, the l_c3 loops) pays nothing.
- **A chain of in-frame COWs on dead `let` sources copies from the second
  site.** In `(let [a (vec-push v 1) b (vec-push a 2)] …)`, `v`'s slot still
  counts until scope exit.
  - Every such chain used to release one box more than once, so no correct
    program loses reuse.
  - Recovering the reuse would need the slot release suppressed at last use.
    That is drop-guided reuse (§6.1), which is not designed.
  - Trigger: a measured workload in which such a chain dominates.
- **The typecheck escape fact stays published and read** by stack placement
  (§4) and spark density (§13.4). A wrong `Some(false)`, such as the old
  match-variable pattern case, can no longer cause a COW use-after-free.
- **The match seam has no COW rule.** A match over a COW scrutinee plans like
  a match over any owned temporary
  ([transitive drop glue](transitive-drop-glue.md) §5). A forwarding
  variable-pattern arm is `OwnedForwarded`, and a consuming arm is
  `OwnedConsumed`.
  - **What retires.** The match exception forced `OwnedConsumed` on a
    forwarding arm whenever the site retained, as the retention's "balancing"
    release. The producer's recorded retain decisions and their reconciliation
    existed only to feed it, and they retire with it.
  - **Why it was wrong.** The arm released the result it forwarded, and that
    release was balanced only if the frame later added a reference back.
    - **Where a return protect followed** (ACT-1027's e2e shapes, D2-C and
      D2-R in [QA's V1 record](../../tests/plan/s122-evidence-delta.md#act-1024--v1-record-and-the-w-m-ruling-2026-09-30)),
      the mutate and grow branches survived. On the copy branch and the
      copy-only path the result is the only reference, so the arm freed it
      before the protect ran.
    - **Where none followed** (the U-R3a unit, `(match (vec-set v 0 5) [r r])`
      returned over an owned parameter), the arm release alone was the fault.
      On the mutate branch the retention and the arm release cancel, and `v`'s
      scope exit then frees the returned box; on the copy branch the arm frees
      the fresh box. Measured at CLIF before the fix: one increment and two
      releases, with no protect.
  - **Why it cannot stay.** Reading "is `Borrowed`", as this contract first
    specified, would widen that fault to every unclaimed `Var` site.
- **A forwarding join's leak is exposed, not caused.** A `let` or `match` that
  yields its own binder transfers that binder's reference. The probeless
  provenance walk (`value_provenance`) reads such a join as `NotOwnedHere`, so
  its consumer leaks one block
  ([ACT-1026](../../sprints/actions/ACT-1026-binder-forwarding-join-consumed-in-frame-leak-intake.md)).
  - **Two consumer faces.** An in-frame inline op does not release the join.
    An enclosing join, followed by the return protect, adds a reference.
  - **What changes.** The retention supplies the reference that the missing
    increment used to withhold. On the mutate branch those shapes move from a
    cancelling balance to the one-block leak they already show on the copy
    branch. No shape becomes a use-after-free.
  - **Where it is fixed.** The join's transfer is correct. The provenance walk
    is the side to change, at a separate seam, and it is outside this contract.

The halves cannot land separately:

- the gate alone leaves the oracle comparing correct-on against wrong-off;
- the polarity alone leaves the analysis-on failures.

Two alternatives were rejected on evidence, and one on design:

- An unconditional increment on the borrowed mutate branch was once
  **falsified**: it leaked for a literal source and scaled allocation with the
  iteration count in a recur loop. Both sources are now `Owned`: a literal is a
  fresh temporary, and a recur loop's top-level COW on its parameter holds the
  consuming claim. So the increment now falls only where a slot release
  balances it.
- A per-consumer alias increment at every consume shape was rejected as a
  mirror family.
- The binding-indirection consume contract is a different, structurally
  discriminated rule
  ([binding-indirection-consume.md](binding-indirection-consume.md)).

Three ways to keep a COW rule at the match seam were rejected:

- **"Is `Borrowed`" as its predicate** (this contract's first text). It was
  measured unsound on the copy paths (ACT-1027).
- **Freezing it on the old escape-gated verdict.**
  - It leaves ACT-1027 open at escaping sites.
  - It keeps the escape fact as a COW input.
  - The producer's record would disagree with that verdict at every
    `Some(false)` site.
- **Retaining on the copy branch too, so the arm's release balances.** The
  result's count would then depend on its consumer, which is the mirror family.

**Status (2026-09-30): implemented in the working tree for ACT-1024,
uncommitted, and not accepted.** The user approved the fix, the match
exception's retirement with it (which fixes ACT-1027), and carrying ACT-1026
and ACT-1028.

- **Shape.** One change-set on top of the ACT-1021 amendment (§13.3), whose
  claim it reuses: the two-state source, one claim set read by one reader
  with the return-COW and self-tail issuers, and the match plan without a COW
  input. The retain decisions, their reconciliation and the escape-fact
  threading to the COW producer are deleted.
- **A claimed site is not asserted to lower in place.** The return-COW claim
  has no last-use condition, so a claimed site legitimately reaches the copy
  extern (L9). The self-tail issuer derives in-place from the same last-use
  predicate the lowering reads. An assertion that a claimed site takes the
  in-place core was therefore false for one issuer and redundant for the
  other, and it was removed (§15 row 2).
- **Evidence.**
  - `dev`: the producer, escape-axis and U-R3a/U-R3b cells went RED first and
    are GREEN; the claimed-site and U-R3c legs stayed GREEN. With analysis
    off, eight affected shapes emit byte-identical CLIF before and after.
  - `test`'s V2, on the affected e2e binaries with the stale-release check
    armed: W1 and its tail family, W-P, W-L, W-LOOP (reuse equal to its step
    count), and both ACT-1027 faces (D2-C at marginal 0, D2-R) are GREEN. The
    only REDs are the carried D1-M and D1-L. The goldens equal checkpoint A,
    and the public API reads +0/−0.
  - `review`(backend) found no blocking finding.
  - K4 is complete and `qa` judged Phase 5's evidence
    adequate ([K4 record](../../tests/plan/s122-evidence-delta.md#final-test-visit-k4--record-and-phase-5-adequacy-2026-09-30)).
    User acceptance and phase approval are pending.
- **Carried, measured unchanged.**
  - ACT-1026's leak: D1-M and D1-L stay RED at one block, and W-M reads
    exactly one.
  - ACT-1028's leak is unchanged.
  - L9 stays a leak lead.
- **Grades** (the canonical row is [R14](../arch/safety-invariants.md)).
  - The one-reference result, and no retain-less `Borrowed`, are structural.
  - A `Var` source reaching `Owned` only through a claim whose issuer
    suppresses the release is asserted, with the named falsifier above.
  - Balance is measured on the V2 cells above only; W1's pre-fix RED proves
    the check detects. It stays asserted beyond them, with named falsifiers:
    any ACT-1024 shape RED under the armed stale-release check, or either
    ACT-1027 face stopping it. Whole-compiler COW soundness is not inferred.

---

## §15. RC/alloc seam assertion density

**The rule.** An assertion at an RC or allocation seam is one of two kinds, and
the byte-identical-off obligation resolves differently for each:

- **(A) Codegen-invariant assertions** — `debug_assert!` in the emitter guarding
  the compiler's own decision. They emit nothing into generated code, compile
  out in release, and are always on in debug builds. This is the default.
- **(B) Emitted runtime checks** — a check baked into generated code changes the
  CLIF, so it must be gated by an env var read once, default off, extending the
  existing `CRANELISP_RC_DEC_CHECK` / `CRANELISP_RC_STATS` pattern. Never an
  always-on emitted check.

Emission-adjacency decides the kind, not debug versus release; a category-A
assertion may never emit CLIF.

| # | Seam | Kind | Assertion | State |
|---|---|---|---|---|
| 1 | `emit_rc_inc` / `emit_rc_dec` | A | the operand is heap-categorized, never a bare nullary tag | open |
| 2 | COW consumed-source seam | — | No emitter assertion is owed. `Owned` carries its drop materials by representation, and the borrowed increment is structural. The `Var`-source `Owned` path is graded by census, asserted with its named falsifier; its promotion is representational, not an assertion (§13.7). A claimed site is not required to take the in-place core: the return-COW claim legitimately reaches the copy extern (L9, §13.3) | retired (2026-09-30) |
| 3 | drop-glue builders | A | the glue identity for a value equals the keyed identity of its concrete type | open |
| 4 | `compile_vec_lit` element move-in | A | a heap element moved into the container is a producing temporary, not a borrow | open |
| 5 | `vec-get` element inc elision | A | elision fires only with the site fact present (§3.3) | built |
| 6 | inline dec seams (COW copy-branch source, drop-glue element decs, Vec-literal and match teardown) | B | `CRANELISP_RC_DEC_CHECK` covers every backend-emitted dec | built |

Production stays unasserted by design (the R8 carve-out in
[safety-invariants.md](../arch/safety-invariants.md)).
