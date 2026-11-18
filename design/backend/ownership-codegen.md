# Ownership codegen

**Owner:** `design`, narrow-deployed to `cranelisp-backend`. **Subordinate to:**
[backend.md](backend.md).

**Status:** the current design of the backend mechanisms that consume the
ownership analysis without deciding a count: reuse counters, the redefinition
machinery and the supporting contracts. Counting — move, duplicate and drop — is
[uniform counting](uniform-counting.md), built at S123 W2. The counting
mechanisms this document used to carry (borrow elision, the static uniqueness
proof, the tail and COW counting contracts, the borrowed extern sibling) are
deleted; their section numbers remain as one-line stubs because source and
tests cite them. §0 records each mechanism's disposition under
[Principle 27](../arch/principles/27-dev-tier-optimises-only-against-blow-up.md):
the dev tier keeps an optimisation only against a change of growth rate.
Verified against source on 2026-11-16, and §0, §1, §4 and §13 again after
S124 B1 on 2026-11-17, and §0, §2.1, §7 and §10 at `441e31ea` on
2026-11-18, and §0, §1, §4, §5, §9 and §13 at `1e4b0ce4` on 2026-11-18.
The increment ladders, as-built
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
| Stack placement for `NoEscape` | §4 | Retired at S124 B1 with packet row D5 | Constant factor: dev tier no longer carries it. The region arena (§4.4) is release-tier |
| Non-atomic RC for `Confined` | §5 | Retired at S123 W4: no classifier or census; every emitted RC operation is atomic unless the probe is set | Constant factor: release tier (§5). The unsound measurement probe stays |
| Dynamic Vec COW check and reuse counters | §6 | Built | Stays: rule U2 holds an update loop linear ([uniform counting](uniform-counting.md) §2). The counters are instrumentation |
| General drop-guided reuse | §6.1 | Not built | Release tier |
| One-word value flattening | §7 | Retired at S124 B5 with packet row D4 | Constant factor: dev tier no longer carries it. The value-layout predicate stays a published fact |
| Redefinition machinery (backend half) | §8 | Fresh slots built; the trap stub retired at S123 W4 (P13) | Not an optimisation |
| Dual-symbol extern convention | §9 | Retired: no position borrows | The carrier leaves in S124 with packet row D6 (§9) |
| Vec-query trio in value position | §12.7 | Built | A required lowering, not an optimisation |
| Spark density axis | §13.4 | Retired at S124 B9 | Tuning, not parallel evaluation. Parallel evaluation itself stays (Principle 27's carve-out) |
| Supporting contracts (golden oracle, counters, wrapper contracts, unit scenarios, producer pins) | §13 | Current | — |
| RC/alloc seam assertion density | §15 | Row 6 built; rows 2 and 5 retired; rows 1, 3 and 4 open | — |

---

## §1. Seams

The mechanisms land on existing seams; there is no new pipeline stage, graph or
store. The main ones, by module (the seam map is `crates/cranelisp-backend/AGENTS.md`):

- **`cranelisp-backend/src/heap.rs`** — the inline RC emission helpers, the
  atomicity decision (`use_nonatomic_arm`) and
  `HeapCategory::classify`. The atomicity decision lives only here. Header layout is also read by
  `compiler/rc_emission.rs` and `drop_glue.rs`.
- **`compiler/vec_codegen.rs`** — the inline COW cores and their reuse
  counters.
- **`compiler/control_flow/fn_as_value.rs`** — value-position and auto-curry
  wrappers.
- **`cache/`** — the ownership toggle as a manifest key.

Typecheck supplies advisory site facts on `MonoExpr` nodes. Since the density
retirement (§13.4) the backend reads neither the escape nor the confinement
fact, reads no mode summary for emission, and derives no ownership, escape,
confinement or uniqueness of its own.

---

## §2. The master analysis-off toggle

### 2.1 One switch

`CRANELISP_NO_OWNERSHIP=1` forces the conservative point everywhere.
Typecheck's ownership pass does not run, so no site facts exist, and every
consumer takes its absent-fact arm. The backend reads the same polarity
(`ownership_analysis_off`) in the ownership plan, which selects moves off
([uniform counting](uniform-counting.md) §2.1), and the cache manifest; heap
classification does not read it. The toggle is the permanent differential oracle switch; the default
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

Code compiled analysis-on and analysis-off differs: moves on or off, and the
facts the cache persists. Loading one polarity's cache under
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

**Retired from the dev tier at S124 B1** (`b0f48914`, `8f44040e`; packet row
D5; Principle 27). Every construction allocates on the RC heap, whatever its
escape fact. Without stack placement a `NoEscape` construction costs a
constant per construction and changes no growth rate. The mechanism's
description is in Git history. What stays live:

- **Kept:** typecheck's escape fact, produced and tested where it is computed.
  The backend reads it nowhere since the density retirement (§13.4).
- **Kept:** the shared self-call predicate `is_self_call`, consumed by the TCO
  back-edge decision and the spark classifier. The stack gate was its third
  reader.
- **Pinned:** a `NoEscape` scalar-payload constructor call takes the heap
  path, identical to its escaping twin
  (`compiler/apply/heap_placement_tests.rs`).
- **Golden corpus:** B1 recorded no diff and so no re-baseline. The corpus held
  no stack-placed construction, so no attributed whole-corpus re-baseline
  was owed. Analysis-on and analysis-off lowerings now agree on allocation
  placement.
- **ACT-1049 and ACT-1066 close by subtraction.** No stack-placed value reaches
  the armed decrement check or drop glue's liveness assertion, so neither
  needs an exemption for immortal headers. *Refuted if* REPRO-1066
  ([evidence delta](../../tests/plan/s124-evidence-delta.md) §3.10) is still
  RED on the B1 tree; the attribution then returns to `qa`.
- **Other owners:** spec §12.1's descriptive layouts should not describe stack
  placement after S124 (`spec`).

### 4.1 Eligibility

Retired with §4. The five eligibility gates (static size, all-scalar payload,
no TCO back-edge, backend-emitted, not relocated into a spark thunk) are
deleted with the mechanism. A citation of gate 3 or gate 5 names a check that
no longer exists.

### 4.2 The immortal header

Retired with §4. `IMMORTAL_RC` is deleted; no header the backend emits is
immortal.

### 4.3 Spark relocation — gate 5

Retired with §4, together with `FnCompiler::in_spark_thunk` and its
propagation into lambda bodies and the dependent-spark thunk.

### 4.4 The region arena — deferred

An arena for `NoEscape` allocations of one structural lifetime (a `let` body, a
match arm, a `ParBind` arm) would reach dynamically sized and extern-produced
allocations. It would consume typecheck's escape facts and free a
`ParBind`-arm arena in the joining parent after the join. It is release-tier
work (§0). **Trigger to design it:** a release-tier optimisation pass, an
allocator seam that lets extern allocations be redirected, **and** a fixture
whose hot allocation is `NoEscape`, so that the arena would deliver a
measured win.

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

The backend reads no confinement fact since the density retirement (§13.4).
Each probe-selected helper has a
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

## §7. One-word value flattening — retired

**Retired from the dev tier at S124 B5** (`441e31ea`, with packet row D4),
under Principle 27: holding a one-word single-constructor value on the heap
costs an allocation and its counts, a constant per value. The current design
is what replaced it:

- **One representation.** `HeapCategory::classify` does not consult
  `value_layout` or the analysis toggle. A one-word single-constructor ADT
  classifies like any other single-data-constructor ADT, as a heap value, in
  either toggle polarity. It is constructed on the RC heap
  ([compile-to-module](compile-to-module.md) §2.6.1), released through its
  canonical glue, given element functions as a Vec element and glue as a
  field, and displayed and traced as an ordinary heap ADT.
- **The predicate stays published.** `value_layout` in `cranelisp-types` is a
  retained fact whose design home is
  [the ownership spine](../arch/ownership-inference.md) §6.3 and its rustdoc.
  Its only reader is typecheck's `Copy` classifier, and a `Copy` mode no
  longer couples to emission, because the backend reads no mode summary (§1).
  A new representation reader of it is a reject (§10).
- **Cache.** The representation change bumped `CACHE_SCHEMA_VERSION` to 32,
  so every object compiled against the flattened layout is refused.
- **Emission acceptance.** B5's golden re-baseline is attributed when its diff
  is confined to frames that handle a value of a type `value_layout` admits,
  directly, as a Vec element or as an ADT field, and to those fields' glue,
  in any golden lane. Any other frame's diff is unattributed and blocks.
- **ACT-1069.** Its trace cells, the small-payload leg and the two controls
  are expected to pass on the B5 tree with no change made for them, because
  the formatter is correct for heap values. A cell still RED refutes the
  attribution and returns to `qa`, who disposes of the record.

The binary's half is [int §16.0](../int/int.md#160-open-binaryint-obligations-verified-against-source-2026-09-21),
*`HeapCategory::Value` removed (D4)*, and
[result owner §1.1](../int/result-owner.md#11-classification-is-a-shared-predicate-not-an-absence-test).

The subsections below are anchors for existing citations; the mechanism they
described is in Git history before `441e31ea`.

### 7.1 `HeapCategory::Value` and its single source

Retired: the variant is deleted. The eligibility predicate is §7's
*The predicate stays published*.

### 7.2 One word, single constructor

Retired with §7.1. The size bound is the predicate's constant,
`VALUE_LAYOUT_MAX_WORDS`. The multi-word trigger retired with the mechanism:
flattening returns only with a release-tier lowering
([ownership spine](../arch/ownership-inference.md) §6.3).

### 7.3 Vec of values

Retired: a Vec of these types gets element functions like any heap element.

### 7.4 Cache and `--link` parity

Retired: §7, *Cache*.

### 7.5 Trace and display descriptors

Retired: §7, *ACT-1069*.

### 7.6 Compatibility rules

Retired with the variant.

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
`Realization::ExternShim { borrowed_sibling }` has had no producer since
ACT-0974 and leaves `cranelisp-types` in S124 (packet row D6, with row D9).
Not in source at `1e4b0ce4` (read 2026-11-18).

**The backend's half.**

- The cache loader's validation of the persisted sibling slot is deleted with
  the field. That is the `ExternShim { borrowed_sibling: Some(slot) }` arm in
  `cache/serialize.rs`, together with its row in that module's validation
  table.
- The public variant `CacheStale::SiblingSlotOutOfRange` is removed with its
  only producer (row D9, approved 2026-11-16). Its diagnostic tag arm and its
  display arm go with it. Backend `public-api.txt` loses three lines.
- `CACHE_SCHEMA_VERSION` goes from 32 to 33 (`cache/mod.rs`), because
  `Realization` is persisted. The schema pin cell in
  `cache/serialize/tests.rs` follows it.
- In `cache/serialize/tests.rs`, the sibling fixtures
  (`install_primitive_with_sibling`, `roundtrip_sibling_slot`) and the cell
  that plants an out-of-range sibling slot are deleted. The cells that cover
  every persisted index, the accept fence and the class-distinctness cell,
  lose their sibling leg and keep the rest.
- Every backend call of `SymbolTable::install_extern` drops the sibling
  argument if `arch`'s change removes that parameter. Every such call is in
  test code: `compiler/extern_call.rs`'s test module and four test files.

**Commit shape: one commit, types first in the working tree.** `sprint`
sequences it as one callee-first migration:

1. `arch` removes the field from `cranelisp-types`, touching `lifecycle.rs`,
   `module.rs` and the types tests. The workspace then stops compiling, and
   the broken build is the checklist. `SymbolTable::install_extern` takes the
   sibling as a parameter. The packet row names neither that parameter nor
   typecheck's production callers of it, so before this step `arch` confirms
   that the approved delta covers the parameter, or returns the row to the
   user.
2. `dev`(backend) makes the half above.
3. `dev`(typecheck) follows in its own crate: the `install_extern` calls in
   `result.rs` and `builtins.rs`, and the field in three test fixtures
   (`infer/tests.rs`, `program/finalize/tests.rs` and
   `program/mono_collect/tests/multi_sig.rs`). The binary has no reader.
4. The workspace builds, the suite runs, and the tree is committed once.

Two constraints force this shape:

- **The schema bump belongs to the commit that changes the persisted shape.**
  A commit with the field removed and the version unchanged would read
  sidecars of the other shape as current.
- **Neither half compiles without the other.** The backend matches the field
  by name, and the types change removes it. A backend-first commit would also
  delete the validation while the field is still persisted.

No commit leaves the workspace unbuildable. No e2e cell is owed: the default
emission is unchanged, and a pre-bump sidecar is a miss under the existing
version cell ([evidence delta](../../tests/plan/s124-evidence-delta.md) §9.4).
Safety register row R5's wording for the sibling slot is `arch`'s and changes
in the same commit.

---

## §10. What must not ship

- A reuse token or uniqueness bit on any ABI surface.
- A borrowing position on any call edge
  ([uniform counting](uniform-counting.md) §1).
- A backend-local escape, strand or uniqueness analysis duplicating typecheck's.
- An emission change on a fact-absent path (§2.2).
- GOT slot-hole reclamation.
- A representation decision read from `value_layout` anywhere outside
  typecheck's `Copy` classifier (§7).

---

## §11. Quality attributes

- **Simplicity.** Every mechanism rides an existing seam: the null
  element-function path, the panic machinery and the slot allocator. Net-new
  machinery is one manifest key.
- **Maintainability.** The atomicity decision and slot initialisation stay in
  `cranelisp-backend/src/heap.rs`.
- **Observability.** `[RC_STATS]` attributes the mechanisms (§13.2), the CLIF
  dump shows fact-gated deltas, and the toggle gives every observation an A/B
  baseline.
- **Concurrency safety.** The backend adds no strand reasoning and no shared
  state; confinement and escape arrive as typecheck verdicts. The else-arm
  discipline (§2.2) is this crate's structural guard.
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
           reuse_hit=N reuse_miss=N rc_nonatomic=N rc_atomic=N \
           str-len_adapt=N alloc_bytes=N
```

- `rc_inc`, `rc_dec`, `allocs`, `deallocs`, `reuse_hit`, `reuse_miss` and
  `alloc_bytes` are **runtime** tallies.
- `rc_nonatomic` and `rc_atomic` are **codegen-time** counts,
  honest for `--run` and the REPL (compile and run share a process) and honestly
  zero for a `--link` binary, which did no codegen.
- `rc_nonatomic` and `rc_atomic` count only the probe-selected helpers (§5.2):
  `rc_nonatomic` is non-zero only under the probe, and `rc_atomic` is not the
  total of atomic operations emitted.

The counter state and the print surface live in `cranelisp-intrinsics::rc`; the
backend is the sole writer, pushing (`tally_rc_emit`) from host code during
compilation. The pushes emit no IR. The `stack_slot` field left with stack
placement (§4, packet row D5), moving every later field one position left;
readers that parse by name are unaffected.

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
- **N4 — fine stack oracle** — retired with stack placement (§4).

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

The fact supply has no consumer: the density axis retired at S124 B9
(`4b8660c9`; Principle 27). It was a tuning mechanism, disabled by default,
not parallel evaluation itself. The scorer, the
decline verdict, the threshold and trace statics with their
`CRANELISP_SPARK_DENSITY_MAX` and `CRANELISP_SPARK_DENSITY_TRACE` variables,
and the fact readers `node_escapes` and `node_confined` are deleted. Admission
is the compute-worthiness test alone
([lenient evaluation](lenient-eval.md) §2.7). Default emission was
byte-identical. One module cell asserts that admission ignores ownership facts
at both spark sites (`compiler/control_flow/sparkability_tests.rs`).

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
