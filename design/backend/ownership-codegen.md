# Ownership codegen

**Owner:** `design`, narrow-deployed to `cranelisp-backend`. **Subordinate to:**
[backend.md](backend.md).

**Status:** the current design of the backend mechanisms that consume the
ownership analysis without deciding a count: stack placement, value
flattening, reuse counters, the redefinition machinery and the supporting
contracts. Counting — move, duplicate and drop — is
[uniform counting](uniform-counting.md), built at S123 W2. The counting
mechanisms this document used to carry (borrow elision, the static uniqueness
proof, the tail and COW counting contracts, the borrowed extern sibling) are
deleted; their section numbers remain as one-line stubs because source and
tests cite them. §0 records each mechanism's disposition under
[Principle 27](../arch/principles/27-dev-tier-optimises-only-against-blow-up.md):
the dev tier keeps an optimisation only against a change of growth rate.
Verified against source on 2026-11-16. The increment ladders, as-built
narratives and falsified analyses are in Git history.

**Governing authority:** [the ownership spine](../arch/ownership-inference.md)
(arch). Where this design and the spine disagree, the spine governs. The
producer of every fact consumed here is
[typecheck's ownership inference](../typecheck/ownership-inference.md).

> **Standing invariant.** The conservative lowering — every use duplicating,
> every RC operation atomic, every allocation on the RC heap — is permanently
> reachable under the master analysis-off toggle (§2), and every mechanism below
> is gated by a present fact whose absence selects the conservative path. The
> conservative path is the spine's all-`Owned` oracle
> ([spine contract](../arch/ownership-inference.md#62-the-differential-oracle-r7)).

---

## §0. Scope and state

The disposition column applies Principle 27's acid test: remove the mechanism
and scale the input; if only the constant changes, the mechanism leaves the dev
tier. The user ruled the schedule on 2026-11-16 (no new dev-tier optimisation;
confined counting retires in S123; the rest in S124 with their API packets and
spec rulings). A retiring mechanism's typecheck facts keep being produced.

| Mechanism | Section | State | Disposition |
|---|---|---|---|
| Master analysis-off toggle and cache key | §2 | Built | Stays: the differential oracle, not an optimisation |
| Borrow elision | §3 | Retired (uniform counting) | — |
| Stack placement for `NoEscape` | §4 | Built for scalar-payload ADT constructor calls; closures and Vec literals decline | Constant factor: retires in S124 (§4). The region arena (§4.4) is release-tier |
| Non-atomic RC for `Confined` | §5 | Retired at S123 W4: no classifier or census; every emitted RC operation is atomic unless the probe is set | Constant factor: release tier (§5). The unsound measurement probe stays |
| Dynamic Vec COW check and reuse counters | §6 | Built | Stays: rule U2 holds an update loop linear ([uniform counting](uniform-counting.md) §2). The counters are instrumentation |
| General drop-guided reuse | §6.1 | Not built | Release tier |
| One-word value flattening | §7 | Built | Constant factor: retires in S124 (§7). The value-layout predicate stays a published fact |
| Redefinition machinery (backend half) | §8 | Fresh slots built; the trap stub retired at S123 W4 (P13) | Not an optimisation |
| Dual-symbol extern convention | §9 | Retired: no position borrows | The carrier's removal is `arch`'s, scheduled for S124 |
| Vec-query trio in value position | §12.7 | Built | A required lowering, not an optimisation |
| Spark density axis | §13.4 | Built, disabled by default | Retires in S124. Parallel evaluation itself stays (Principle 27's carve-out) |
| Supporting contracts (golden oracle, counters, wrapper contracts, unit scenarios, producer pins) | §13 | Current | — |
| RC/alloc seam assertion density | §15 | Row 6 built; rows 2 and 5 retired; rows 1, 3 and 4 open | — |

---

## §1. Seams

The mechanisms land on existing seams; there is no new pipeline stage, graph or
store. The main ones, by module (the seam map is `crates/cranelisp-backend/CLAUDE.md`):

- **`cranelisp-backend/src/heap.rs`** — the inline RC emission helpers, the
  atomicity decision (`use_nonatomic_arm`), `emit_stack_alloc`,
  `HeapCategory::classify`. The atomicity decision and stack-slot
  initialisation live only here. Header layout is also read by
  `compiler/rc_emission.rs` and `drop_glue.rs`.
- **`compiler/fn_compiler.rs`** — the stack-eligibility gates and the site-fact
  readers `node_escapes` and `node_confined`.
- **`compiler/apply.rs`** — the stack-eligible constructor path.
- **`compiler/vec_codegen.rs`** — the inline COW cores and their reuse
  counters.
- **`compiler/control_flow/fn_as_value.rs`** — value-position and auto-curry
  wrappers.
- **`compiler/control_flow/sparkability.rs`** — the spark density axis.
- **`cache/`** — the ownership toggle as a manifest key.

Typecheck supplies advisory site facts on `MonoExpr` nodes. The backend reads
the escape and confinement facts, reads no mode summary for emission, and
derives no ownership, escape, confinement or uniqueness of its own.

---

## §2. The master analysis-off toggle

### 2.1 One switch

`CRANELISP_NO_OWNERSHIP=1` forces the conservative point everywhere.
Typecheck's ownership pass does not run, so no site facts exist, and every
consumer takes its absent-fact arm. The backend reads the same polarity
(`ownership_analysis_off`) in two places: the ownership plan, which selects
moves off ([uniform counting](uniform-counting.md) §2.1), and the cache
manifest. The toggle is the permanent differential oracle switch; the default
is analysis-on.

### 2.2 Absent facts select the existing code

Producer-side gating does not by itself prove the conservative lowering is
unchanged, so the backend is shaped to make it so:

1. **The else-arm is the existing helper.** Each mechanism is a guard of the form
   `if let Some(fact) = … { new emission } else { the existing helper call }`.
   The conservative arm is never a copied or reflowed variant.
2. **No unconditional new instructions.** A mechanism emits nothing on the
   fact-absent path. The redefinition machinery (§8) is the one exception class,
   and it runs only on the redefinition path.
3. **The differential evidence is `qa`'s**: toggle-off CLIF against the golden
   corpus (§13.1), and analysis-on versus analysis-off observable output.

### 2.3 The toggle is a cache invalidation key

Code compiled analysis-on and analysis-off differs: moves on or off, stack
placement, and the facts the cache persists. Loading one polarity's cache under
the other would make the differential compare a mixture. The toggle's polarity
is therefore one of the manifest's global invalidation dimensions alongside the
compiler fingerprint, target and format: flipping it invalidates the whole
cache, at the price of a rebuild on flip.

### 2.4 The measurement probes

`CRANELISP_NONATOMIC_RC` is a documented-unsound non-atomic probe and an
independent, off-by-default measurement toggle. It is the only selector of the
non-atomic emission arms, and it covers the inline helpers only (§5.2). It participates in neither the canonical run
nor the golden corpus. It is an instrument, not a dev-tier optimisation: it
measures the ceiling a release-tier non-atomic mechanism could reach.

---

## §3. Borrow-elision emission

Retired at S123 W2 with §3.1–§3.5: no position borrows
([uniform counting](uniform-counting.md) §1, §5). A test or comment citing
this section names a mechanism that no longer exists.

### 3.5 The Decision-24 wrapper

Retired as an adapter. A value-position wrapper consumes every parameter like
any other call, so every code pointer reachable from a closure targets a
consuming entry with nothing to adapt (§13.3).

---

## §4. Stack placement for `NoEscape`

The mechanism is live: `STACK_ALLOC_ESCAPE_FACT_SOUND = true`, with
`CRANELISP_NO_STACK_ALLOC=1` as the fine runtime oracle and
`CRANELISP_NO_OWNERSHIP` as the coarse one.

**Disposition: retires from the dev tier in S124** (Principle 27; it replaces
the 2026-11-15 ruling that kept stack placement pending a cost measurement).
Without it a `NoEscape` construction allocates on the RC heap, which costs a
constant per construction and changes no growth rate. Until the S124 change
lands, this section is the current design. The retirement is one change-set:

- **Deleted:** `emit_stack_alloc` and `IMMORTAL_RC` (`heap.rs`), the
  eligibility verdict and its five gates (§4.1), the spark-relocation flag
  (§4.3) where the gate is its only reader, the `CRANELISP_NO_STACK_ALLOC`
  oracle (§13.2.2 N4) and the `stack_slot` tally push.
- **Kept:** typecheck's escape fact, produced and tested where it is computed.
  With stack placement gone the backend has no escape reader except the spark
  density scorer, which retires in the same sprint (§13.4).
- **Evidence shape:** emission changes at every eligible construction, so the
  golden corpus is re-baselined with attribution, and the analysis-on and
  analysis-off lowerings agree on allocation placement. `BUILD_ID` invalidates
  cached objects, so no schema bump is needed for placement alone.
- **Other owners:** the `[RC_STATS]` `stack_slot` field belongs to intrinsics'
  print surface; whether it stays as a zero or leaves is `design`(intrinsics)'s
  and `arch`'s. Spec §12.1's descriptive layouts should not describe stack
  placement after S124 (`spec`).

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
scalar-capture gate). Declining is always sound. A stack value is counted like
any other; its releases are drift on the immortal count (§4.2).

### 4.2 The immortal header

Stack slots keep the standard header with `rc = IMMORTAL_RC` (`1 << 62`). Any
RC traffic a `NoEscape` value meets — duplicates, drops, callee consuming
decs, guarded ops — is a harmless drift on a frame-local cell; the free path
(`old == 1`) is unreachable, so `dealloc` never sees a stack pointer; and the COW
unique check never succeeds, so a buffer-freeing grow path is unreachable. No
call site changes for stack-ness. When stack placement extends to Vec literals,
vecs with in-frame writes should decline, because they would never mutate in
place.

### 4.3 Spark relocation — gate 5

A joined spark reading a parent-frame stack slot through a capture is sound:
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

**Disposition: retired from the dev tier** (Principle 27; user ruling
2026-11-16). A confined cell counted atomically costs a constant per RC
operation, so non-atomic counting belongs to the release tier. Typecheck keeps
producing the `confined` site fact. Under uniform counting the classifier
already had no caller: its one consumer was the return protect's increment,
which [uniform counting](uniform-counting.md) §5 deleted, so its removal at
S123 W4 left the golden corpus byte-identical.

### 5.1 One decision point, one selector

Every inline RC helper asks one question, `heap::use_nonatomic_arm`, and its
only input is the process-global `CRANELISP_NONATOMIC_RC` probe (§2.4). There
is no per-site atomicity input. Every emitted RC operation is atomic unless the
probe is set.

`node_confined` stays as a site-fact reader for the spark density scorer
(§13.4) and leaves with that axis in S124. Each probe-selected helper has a
unit cell for both polarities, run in a child process because the probe is
read once per process.

**Re-entry rule, for a release-tier design.** Under uniform counting the RC
operations are a binder's duplicates and drops, so a future consumer needs
"this binder's cell is confined", which the analysis does not produce today.
Key such a fact on the plan's binder identity, never on the name. A former
`Symbol`-keyed binding carrier had no shadow save/restore and would have leaked
an outer confined verdict onto an inner crossing binding, which is a data
race. Shared artifacts (Vec element adapters, extern copy loops, canonical
glue bodies) have no site identity and stay atomic in any design.

### 5.2 What the probe covers

The probe selects the count update inside the inline helpers that call
`use_nonatomic_arm`, wherever they are emitted. It does not reach the
decrements other emitters write directly:

| Emission | Under the probe |
|---|---|
| Inline increments and decrements in `heap.rs`, plain and nullary-guarded | non-atomic |
| The Vec-aware decrement in `compiler/vec_codegen.rs`, including its use as the Vec glue adapter | non-atomic |
| Canonical ADT, String and IO drop glue's own decrement (`drop_glue.rs`) | atomic |
| Closure release (`compiler/rc_emission.rs`) and IVar releases (`let_if.rs`, `dependent_spark.rs`) | atomic |
| Rust-side counts inside extern bodies (`cranelisp-intrinsics`) | atomic |

A probe measurement therefore still includes those atomic operations and every
free-path fence (§5.3). It approximates the per-site ceiling of a release-tier
confined mechanism, not a blanket non-atomic build: it also reaches the Vec
glue adapter, which the re-entry rule (§5.1) keeps atomic. Attribute a probe
measurement to that set, not to all counting. The probe is unsound outside a
single strand by design.

### 5.3 The free path

Every decrement, probe-selected or not, keeps the `old == 1` → Acquire fence →
drop glue → `dealloc` sequence; the probe changes only the count update. The
fence runs once per free, not per operation, so it does not distort the
per-operation measurement. The probe leg of the helper unit cells asserts
that it survives.

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
is settled: the check is always emitted
([uniform counting](uniform-counting.md) §2.2). **Hazard:** reuse on a non-unique value is
heap corruption; the reuse emission needs value-correct and heap-balanced
evidence under allocator perturbation.

### 6.4 The static-uniqueness proof elides the check

Retired at S123 W2: the dynamic probe is the only uniqueness check
([uniform counting](uniform-counting.md) §2.2). Typecheck's `unique_static`
site fact has no backend reader.

### 6.5 Reuse counters

The COW cores emit `runtime/reuse_hit` on the in-place arm and
`runtime/reuse_miss` on the copy arm, gated at codegen time on
`CRANELISP_RC_STATS` (off ⇒ no emitted IR). Reuse permission is dynamic, so the
split is a runtime tally, reported in the `[RC_STATS]` line (§13.2.1).

---

## §7. One-word value flattening

**Disposition: retires from the dev tier in S124** (Principle 27). A
one-word single-constructor value held on the heap costs an allocation and its
counts, a constant per value. Until the S124 change lands, this section is the
current design. What the retirement must respect:

- **The predicate stays.** `value_layout` in `cranelisp-types` is a retained
  fact (Principle 27, "Retained facts"); only the backend's use of it as a
  representation retires. Typecheck's `Copy` mode no longer couples to
  emission, because the backend reads no mode summary (§1), so §7.1's
  "missing increment" hazard does not arise while `Value` is gone.
- **It changes representation.** Removing the `Value` category changes
  compiled layout, so `CACHE_SCHEMA_VERSION` is bumped (§7.4), the descriptor
  baker renders those types as heap values (§7.5), and Vecs of them gain
  element functions (§7.3).
- **It changes the public surface.** `HeapCategory::Value` is a public
  variant, so its removal goes through `arch` and the user's API gate.
- Spec §12.1's descriptive layouts should not describe flattening after S124
  (`spec`).

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
positions or drop points; and a `Value` field inside
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
- A `Copy` parameter emits no inc and no dec.
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

Retired at S123 W4 with packet row P13. A call to a symbol a redefinition
would leave broken is refused at compile time (user ruling, 2026-11-15;
`spec/12-runtime.md` §12.7.1), and int installs no stub
([session transaction §5.2](../int/session-transaction.md#52-no-symbol-is-left-broken)).
The backend no longer emits one; the raise helper's consumers are the three
source messages ([backend.md §7](backend.md#7-runtime-failure)).

### 8.2 Fresh slots and frozen slots

An ABI-changing redefinition allocates a fresh slot through the ordinary
monotone allocator, and recompiled callers embed it through the unchanged GOT
load, so slot versioning needs no emission change. The ABI-preserving path stays
the in-place slot patch. The per-module GOT slab's base is baked into finalized
code, so the slab must never move while slots grow; retaining superseded `Code`
is int's session pool.

### 8.3 The interface to int

1. `compile_to_module` — unchanged, called per affected symbol.
2. The GOT's `store_slot` and slot allocation — existing. Freezing a slot is
   session bookkeeping, not a GOT mechanism.

---

## §9. The dual-symbol extern convention

Retired at S123 W2 with §9.1–§9.4. A borrowed-convention extern sibling has no
position to serve, because no position borrows
([uniform counting](uniform-counting.md) §1). The carrier
`Realization::ExternShim { borrowed_sibling }` and its cache validation remain
in `cranelisp-types` and the cache loader with no selector; whether to remove
the carrier is `arch`'s.

---

## §10. What must not ship

- A reuse token or uniqueness bit on any ABI surface.
- A borrowing position on any call edge
  ([uniform counting](uniform-counting.md) §1).
- A backend-local escape, strand or uniqueness analysis duplicating typecheck's.
- An emission change on a fact-absent path (§2.2).
- GOT slot-hole reclamation.

---

## §11. Quality attributes

- **Simplicity.** Every mechanism rides an existing seam: the null
  element-function path, the panic machinery and the slot allocator. Net-new
  machinery is stack-slot emission with its sentinel and one manifest key. The S124 retirements (§0) remove the stack-slot emission.
- **Maintainability.** The atomicity decision and slot initialisation stay in
  `cranelisp-backend/src/heap.rs`.
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

The questions this design routed onward were delivered, retired, or are
carried by the sections above. One settled defect keeps its number because
source cites it.

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
- `rc_nonatomic` and `rc_atomic` count only the probe-selected helpers (§5.2):
  `rc_nonatomic` is non-zero only under the probe, and `rc_atomic` is not the
  total of atomic operations emitted.

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
- **N3 — per-site residual atomic RC** (`[RC_SITE_STATS]`) — retired at S123
  W4 with the confined classifier, its only record site (§5.1).
- **N4 — fine stack oracle** — `CRANELISP_NO_STACK_ALLOC=1`, read once at codegen
  and ANDed with `STACK_ALLOC_ESCAPE_FACT_SOUND`, declines stack placement only
  while every other mechanism stays live. Built.

### 13.3 Wrapper contracts

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
entry: an inline primitive lowers inline (§12.7); a slotted target calls
through its slot. Every wrapper parameter arrives owned and is consumed by the
call, like any other consuming position
([uniform counting](uniform-counting.md) §4).

The COW source polarity, the tail-call flushes, the branch-forward rule, the
consuming-COW fact and leads L2–L10 that this section used to carry are
retired with the counting they described. Their faults are mapped in
[uniform counting](uniform-counting.md) §6.

**Attribution discipline.** Design hypotheses in this area have named a
plausible but wrong seam more than once. Before fixing an RC defect here,
confirm the mechanism against `CRANELISP_RC_STATS` and the CLIF dump on the
reduced repro.

### 13.4 Spark density — the fact supply

The density admission axis is designed in [lenient-eval.md](lenient-eval.md)
§2.7 and ships disabled by default (`SPARK_DENSITY_MAX_DEFAULT = 0`). It is a
tuning mechanism, not parallel evaluation itself, so it retires in S124
(Principle 27's carve-out excludes it); with it go the backend's last readers
of `node_escapes` and `node_confined`. Until then, this design's obligation is
the fact supply: `spark_density` scores a candidate
subtree through the same `node_escapes` and `node_confined` readers, counting heap-result sites not covered by `NoEscape` and RC sites not
confined. **As built, the scorer also excludes sites it reads as borrow-elided
projections.** Nothing elides them since the S123 cutover, so that exclusion
under-counts; removing it is `dev`'s, and the axis ships disabled. A subtree
carrying no ownership fact returns `None`, so the axis is inert and admission
unchanged whenever analysis did not run.

### 13.5 Unit scenario spaces

`dev` derives unit scenarios per submodule and scenario class, and `qa` audits
coverage against these spaces. Each space's negative class — absent facts emit
the unchanged instruction sequence — is the unit-tier half of the golden
oracle.

| Seam | Scenario space |
|---|---|
| RC helpers (`cranelisp-backend/src/heap.rs`, `rc_emission.rs`) | helper × probe {unset, set} → unchanged atomic arm or the non-atomic arm (§5.1) |
| Wrappers (`fn_as_value.rs`) | dispatch kind {user function, extern, inline primitive, constructor, trait method, operator} × use {HOF argument, partial application, returned, stored, bound} × instantiation count {1, 2 same op, 2 different ops, n} × mode {REPL, `--run`} |
| COW cores (`vec_codegen.rs`) | branch {mutate, copy, grow} × source count {1, >1} × call site {static, wrapper, curry} → the source is always owned; mutate and grow forward its reference, copy releases it; the result owns exactly one reference on every branch. Counting scenarios are the ownership plan's ([uniform counting](uniform-counting.md) §8) |
| Vec literal element move-in | element {fresh temporary, COW-aliased result} × escape |
| Stack placement | the five gates × `escapes` × site kind → stack slot or unchanged heap; sentinel behaviour |
| Spark density (`sparkability.rs`) | facts {present, absent} × body {allocation-dense, compute-dense, mixed} × threshold boundary → admitted, declined, inert |
| GOT | exhaustion, freeze, in-place patch |

### 13.6 Producer pins

- **Facts are final.** Typecheck writes site facts in one annotation walk after
  its fixpoint converges, so an absent fact always means "concluded
  conservative, or did not run", never "not yet written". The backend needs no
  staleness handling.

### 13.7 COW mutate and grow branches — the settled contract

Retired at S123 W2. A COW source is always owned, so the mutate and grow
branches forward its reference and the copy branch releases it
([uniform counting](uniform-counting.md) §2, rule U2). The R14 count-truth
condition — the in-place branch is sound iff every live reference is counted —
now holds because every binder owns its reference
([safety invariants](../arch/safety-invariants.md) §4 owns the row).

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
| 2 | COW consumed-source seam | — | No emitter assertion is owed: every COW source is owned | retired |
| 3 | drop-glue builders | A | the glue identity for a value equals the keyed identity of its concrete type | open |
| 4 | `compile_vec_lit` element move-in | A | a heap element moved into the container is a producing temporary, not a borrow | open |
| 5 | `vec-get` element inc elision | — | The elision is retired with §3 | retired |
| 6 | inline dec seams (COW copy-branch source, drop-glue element decs, Vec-literal and match teardown) | B | `CRANELISP_RC_DEC_CHECK` covers every backend-emitted dec | built |

Production stays unasserted by design (the R8 carve-out in
[safety-invariants.md](../arch/safety-invariants.md)).
