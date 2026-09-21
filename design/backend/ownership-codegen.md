# Ownership codegen

**Owner:** `design`, narrow-deployed to `cranelisp-backend`. **Subordinate to:**
[backend.md](backend.md).

**Status:** the current design of the backend mechanisms that consume the
ownership analysis — what is built, the contracts it rests on, and the parts
that are designed but not built. Verified against source on 2026-09-21. Section
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
| Supporting contracts (golden oracle, counters, wrapper and COW contracts, spark density, unit scenarios, producer pins) | §13 | Current |
| RC/alloc seam assertion density | §15 | Rows 5–6 built; rows 1–4 open |

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

At a statically resolved call whose callee carries a summary,
`compile_consuming_arg_list_moded` reads the callee's modes through the keyed
`CompileContext::callee_summary_at` (conservative on absence) and emits per position
through the pure `moded_arg_rc(category, mode, owned_binding)`:

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
value-position wrapper bodies and by auto-curry. It currently emits a guarded
post-call dec for every `Borrowed` parameter and no result inc — a moded callee
always returns an owned reference, so callee materialization and wrapper
adaptation never both increment. Its parameter loop is wrong for consuming
extern shims; the realization-directed replacement is designed at
[non-concrete-release-contract.md](non-concrete-release-contract.md) §7.6.

### 3.5 The Decision-24 wrapper

The existing value-position and auto-curry wrapper bodies **are** the Decision-24
adapters: when the target's summary is non-conservative, `emit_wrapper_call`
injects `emit_d24_adaptation` around the moded call; a conservative or absent
summary calls through unchanged. No separate adapter symbol is minted, and
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
  every runtime panic ([ring1-codegen.md](ring1-codegen.md)).

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
export with today's emission. A closure wrapper always calls the consuming entry
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

**The tail-call scope flush.** Before a tail self-call jumps, the heap `let`
bindings in scope frames `[1..]` are released
(`flush_let_scopes_before_tail_jump`), because decs emitted after the jump never
run. A tail argument transfers a live binding in exactly one of three ways, and
the flush must net each binding to exactly one owner:

| Argument shape | Treatment |
|---|---|
| Bare top-level `Var` `(recur v)` | a move: excluded from the flush |
| Control-flow alias `(recur (if c a b))`, `(recur (match … a))` | flushed; each branch that yields a will-be-flushed binding incs it at the branch tail (`maybe_protect_tail_arg_alias`), per branch, because which binding moves is known only at runtime |
| Consumed into a fresh value `(recur (wrap v))` | flushed; the consuming inc already gave the fresh value its own reference |

The protection flag is set only while compiling an `if`/`match` that is itself a
tail argument, is cleared around the condition or scrutinee, and replaces the
unconditional return protect for a match arm in that context. A leak-balance
check reads green over this class's use-after-free, so its evidence asserts the
computed result.

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
| Wrappers (`fn_as_value.rs`) | dispatch kind {user function, extern, inline primitive, constructor, trait method, operator} × use {HOF argument, partial application, returned, stored, bound} × instantiation count {1, 2 same op, 2 different ops, n} × summary × mode {REPL, `--run`} |
| COW cores (`vec_codegen.rs`) | branch {mutate, copy, grow} × polarity {`Owned`, `Borrowed`} × call site {static, wrapper, curry} × escape {`Some(true)`, `Some(false)`, `None`} → exact balance and value semantics |
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
(`rc == 1`, the same box). When the result of a mutate on a borrowed source
escapes — returned through a match binding, stored in a Vec literal, projected
out — the source's scope dec would free the box under the live result. The
settled contract (the R14 ruling, [safety-invariants.md](../arch/safety-invariants.md)
§4) has two inseparable halves:

1. **Toggle-off counts every COW source.** `cow_source_ownership` classifies
   every source `Owned` when analysis is off, so the runtime `rc == 1` branch
   fires only on a genuinely unique source and the copy branch is correct by
   construction. The conservative loop allocates per iteration; that is what
   conservative means. (**R14 count-truth:** the in-place branch is sound iff
   every live independently owned reference is counted.)
2. **Analysis-on incs by escape.** `Borrowed` comes only from the settled origin
   lattice, and the COW core incs the returned pointer iff
   `node_escapes(cow_apply) != Some(false)` — escape or absence incs, the
   use-after-free-safe direction; an in-frame recur transfer (`Some(false)`)
   keeps in-place reuse. Escape is read from the node, never re-derived at the
   producer.

The halves cannot land separately: the gate alone leaves the oracle comparing
correct-on against wrong-off, and the polarity alone leaves the analysis-on
failures. An unconditional producer inc on the borrowed mutate branch was
**falsified** — it leaks for a literal source and scales allocation with
iteration count in a recur loop — and a per-consumer alias inc at every consume
shape was rejected as a mirror family. The separate binding-indirection consume
contract is a different, structurally discriminated rule
([binding-indirection-consume.md](binding-indirection-consume.md)).

**Where the backend gate cannot help.** If typecheck records a wrong
`escapes = Some(false)` (the match-variable pattern case), the gate correctly
declines to inc and cannot distinguish it from a correct recur loop; the cure is
the recorded fact, in typecheck.

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
| 2 | COW consumed-source seam | A | `Owned` carries its drop materials; the borrowed mutate/grow inc follows the §13.7 escape gate | open |
| 3 | drop-glue builders | A | the glue identity for a value equals the keyed identity of its concrete type | open |
| 4 | `compile_vec_lit` element move-in | A | a heap element moved into the container is a producing temporary, not a borrow | open |
| 5 | `vec-get` element inc elision | A | elision fires only with the site fact present (§3.3) | built |
| 6 | inline dec seams (COW copy-branch source, drop-glue element decs, Vec-literal and match teardown) | B | `CRANELISP_RC_DEC_CHECK` covers every backend-emitted dec | built |

Production stays unasserted by design (the R8 carve-out in
[safety-invariants.md](../arch/safety-invariants.md)).
