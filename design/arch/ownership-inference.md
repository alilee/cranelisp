# Ownership inference — one analysis, five queries (the memory-model spine)

**Status:** DESIGN (S100 Phase 3) — the master architecture spine for interprocedural
ownership inference. Authored by `/arch` under the S100 Phase-2 **SIGN-OFF WITH REVISIONS**
(R1–R8, `sprints/SPRINT.md` §Architecture review) and the **user-directed R3 resolution**
(2026-07-02: dependent recompilation, not ABI-pinning). Pre-implementation; pre-user-ratification
at sprint close. **Phase-3 exit gate passed 2026-07-03 (§12 — PASS-with-notes; FIXMEs
0467/0468/0469 drained into §3.3/§6.3/§3.1(b)).**
**Owner:** `/arch`. Subsystem-design peer of `effect-concurrency.md`.
**Role:** the **scope authority** the per-crate proposals cite —
`design/typecheck/ownership-inference.md` (parts 6–11), `design/backend/ownership-codegen.md`
(parts 12–16), and the `/qa` verification plan (parts 17–18, `tests/plan/`). Where a per-crate
proposal and this spine disagree, this spine governs until amended.
**Provenance / measured basis:** the S99 ablation settlement (`sprints/archive/sprint-99.md`;
`effect-concurrency.md` §3.1; `ring2-rc.md` §5.5.2.6–.7; `tests/plan/s99-measurement.md`) —
the parallel slowdown is essentially all contention, dominated on release by **(b) atomic-RC
cache-line bouncing**, whose driver is **vec-COW leaf-refcount volume** (~81 `rc_inc` + 2 allocs
per shared 81-cell copy; ~170M `rc_inc` across 2.1M copies); no pre-Phase-H substrate lever
restores the floor; (a) allocator and (b) RC contention **couple** and must be co-designed.

---

## §0. What this designs, and the bar it must clear

**The thesis.** "Escape analysis", "ownership inference", and "RC optimisation" are not three
subsystems; they are different **queries** against **one** interprocedural lifetime/flow analysis,
computed **in typecheck, after monomorphisation, over the resolved call graph, with no user
annotations**, and consumed by **distinct backend codegen mechanisms**. Doing the analysis over the
resolved call graph at typecheck gives the interprocedural propagation escape analysis lacks — the
fact "`xs` is borrowed" rides through every caller *by inference* — without the annotation burden
of declared ownership types. Precedents: Roc (inferred RC + reuse, zero annotations), MLKit region
inference, GHC demand/cardinality signatures.

**The performance north-star (binding acceptance frame; both required):**

1. **Unnoticeable small-case overhead** — the single-threaded / small-data path must not
   perceptibly regress; machinery invisible until the workload profits.
2. **Strong parallelisation dividends at scale** — copy-a-`Vec`-of-shared-heap-ADTs under
   speculative parallelism runs at a *slight per-core discount to serial*, not today's measured
   2–15× penalty.

**Carried constraints (binding):** keep nested ADTs (no `0416` bitmask dodge); the win lives in
substrate/stdlib/compiler, not exemplar hand-tuning; storage and RC are co-designed (the S99
(a)/(b) coupling finding).

**Semantics boundary (G3).** Nothing here changes language semantics. A "mutable borrow"
(increment II) is a physical-cell write permission sound *because* exclusivity guarantees no
observer can witness the mutation — observationally still immutable; the in-tree precedent is
Vec-COW mutate-in-place (rc==1 + last-use ⇒ in-place write), already spec-clean.
**Standing precondition (Phase-2 finding 6):** the language exposes **no reference-identity
observer** — no pointer-eq, no address in `trace` output, no identity hash. True today; the
mutable-borrow soundness argument *depends on it*. Any future introspection feature that would
expose heap addresses or identity MUST be routed through `/arch` against this precondition before
it lands. `/spec` is not engaged (the mechanism is inferred and invisible; the only optionally
surfaced piece — `Copy`/`clone` as stdlib vocabulary — is deferred, default internal-only).

---

## §1. Actors and functions first (Principle 21)

Before any mechanism: the actors, and the functions between them. The five-query table **is** the
actors map — one producer, one boundary, five queries, five consumers.

**The actors:**

- **The inference pass** (typecheck, `crates/cranelisp-typecheck/` — where monomorphisation
  already lives, `traits/monomorphise.rs`): computes the analysis per module-cluster, after
  mono instantiation, as a fixpoint over the mono call graph.
- **The boundary** (`cranelisp-types`, `/arch`-owned): `MonoDefn`/`MonoExpr`
  (`src/mono_expr.rs`) + the callable's symbol-table entry (`src/module.rs`). Carries the
  analysis outputs down; persists the per-function **mode summary** via `.meta.json`
  (a serialised `SymbolTable` — `module-caching.md` §14.1).
- **The backend lowering** (shared Cranelift path — see §3.4): five mechanisms, each consuming
  one query's output; all intra-function analyses (`compute_last_uses`,
  `HeapCategory::classify`) and all mechanism internals stay here.
- **The session** (`src/session_v4.rs` + scheduler): owns the R3 dependent-recompilation
  transaction — the who-calls-whom index, the recompilation ordering, the cascade-error
  surfacing (§5).
- **The cache** (`.meta.json` + manifest): persists summaries; invalidation stays conservative
  (§5.1).

**The functions between them (the five-query table):**

| # | Query (asked of the one analysis) | Output (per what) | Rides where | Backend mechanism it drives | Increment |
|---|---|---|---|---|---|
| Q1 | Is this param only **read**? | `Borrowed` vs `Owned` — per param of a callable | **ABI-bearing** mode vector on `MonoDefn` + symbol-table summary (§3.1) | pointer-pass; elide the consuming `inc` (caller) and the scope-cleanup `dec` (callee); **borrow-through-projection** makes read access rc-free (§4.4) | I |
| Q2 | Does the value **escape its frame**? | escapes / does-not-escape — per allocation/binding site | **advisory** per-site fact on `MonoExpr` nodes (§3.2) | stack/region allocation instead of heap `emit_alloc` (kills the alloc *and* its RC pair) | I |
| Q3 | Can RC ops on this cell run **concurrently on more than one thread**? | confined / crossing — per cell, op-wise (§2.3) | advisory per-site fact | **non-atomic** RC ops for confined values (plain `iadd` vs `atomic_rmw`) | I |
| Q4 | Is the value **uniquely owned** here? | unique / shared — static proof OR dynamic rc==1 check (R4, §4.3) | advisory per-site fact (static part); reuse token (dynamic part, intra-function only) | in-place **reuse / mutable borrow** (Perceus drop-guided) vs clone at write sites | II |
| Q5 | How is this **type** duplicated? | `Copy` / RC-share / deep-clone — per concrete type | derived classification (structural); representation decision per §6.3 | bit-copy (`memcpy`, zero RC) for value-flattened Copy types / `rc_inc` share / structural copy | II (design named now — R5) |

Two facts make the frame land: **escape (frame) and confinement (thread) are distinct axes**
driving distinct mechanisms — a value can outlive its frame yet never cross a thread (non-atomic
but heap), or die in-frame after being handed `Owned` to a joined spark (stack/region-eligible
yet atomic while alive — op-wise per §2.3, it is the spark-side RC ops that force atomicity, not
the crossing itself).
And the pre-S100 state — `borrowed_vars` (`ring2-rc.md` §5.5), spark-capture-by-borrow (§5.5.2),
Vec-COW last-use — is three ad-hoc instances of this one missing analysis; the design subsumes
them as special cases (§8) rather than adding a fourth.

**Where it bites S99:** the 81 per-copy `rc_inc` come from projecting `Cell`s out of the `Vec` —
Q1's borrow-through-projection makes all read access rc-free, shrinking the problem to genuine
materializations; each materialization is then served by Q4 (reuse when unique) or by
clone / persistent-delta (shared; §8.1), and Q5's value-flattening plausibly removes the `Cell`
refcounts entirely (§6.3).

---

## §2. The lattice (part 1)

Three dimensions. The **mode** dimension is a per-param/per-value lattice; **escape** is a
per-site binary fact with edge-defined semantics; **confinement** is a per-cell fact defined
**op-wise** over the RC operations that exist on the cell (§2.3). They are independent
coordinates, not points on one chain.

### 2.1 The mode lattice

```
        Owned            ⊤ — the conservative point (Decision 24)
          │
       Borrowed
          │
        Copy             ⊥ — no ownership obligation at all
```

Formally: `M = {Copy, Borrowed, Owned}` with the total order `Copy ⊑ Borrowed ⊑ Owned`, plus a
**uniqueness refinement flag on Owned** (below). `⊑` reads "demands less of the caller than". Join
(`⊔`) moves **toward Owned**: a summary joined over call sites / callee uses takes the most
demanding mode any of them requires. The **absent summary is `⊤` everywhere** — no summary ⇒
every param `Owned` ⇒ byte-for-byte Decision 24 (`ring2-rc.md` §3.1). The refinement is therefore
*strictly additive*: every existing cache, every unresolved edge, every HOF site is already at a
valid lattice point.

**Semantics of each point** (for a heap-typed param/value; non-heap types are trivially `Copy`):

- **`Owned`** — the callee receives responsibility for one reference: it decs what it does not
  return (scope cleanup), the caller emits the consuming inc for a reused variable arg or
  transfers a temporary at rc=1. Exactly today's uniform consuming convention (Decision 24).
- **`Borrowed`** — the callee may read the value for the dynamic extent of the call but owns no
  reference: the caller emits **no** inc, retains ownership, and its own scope-cleanup dec is the
  single accounting; the callee emits **no** dec for the param. Sound only when the analysis
  proves the callee never stores, returns, captures-into-escaping-closure, or
  sends-across-suspension the param (else the mode joins back to `Owned`). The value is guaranteed
  live for the whole call because the caller's frame outlives the (synchronous) call — the same
  structural argument as `borrowed_vars` (§5.5) and spark-capture borrow (§5.5.2.3).
- **`Copy`** — the value has no heap identity to account: duplication is a bit copy, no RC ops
  exist for it anywhere. For a type to sit here its *representation* must be a value
  (unboxed/inline) — see the R5 mechanism ruling (§6.3). Scalars (`Int`, `Bool`, `Float`) are
  `Copy` today by construction.
- **`Unique` (refinement flag on `Owned`, NOT a fourth chain point).** `Owned+unique` = the callee
  holds the *only* live reference, which grants write/reuse permission (Q4). It is deliberately
  not in the ⊑ chain because **uniqueness is not a type-instantiation property and is not fully
  static** (R4): rc==1 is call-site-*dynamic*. The analysis emits a static uniqueness proof where
  it can; the general increment-II discriminator is the **dynamic rc==1 check** (Perceus reuse
  tokens / drop-guided reuse — exactly today's Vec-COW mutate-in-place precedent). The contract
  treats the dynamic check as a **first-class outcome**, not a failure of inference (§4.3).

**The monotone-soundness property (normative — this sentence is load-bearing).** *Widening any
inferred mode toward `⊤` (`Owned`), and ignoring any advisory fact, preserves correctness; only
performance degrades.* A mode-ignoring lowering is always correct, only slower. This property is
what makes the conservative all-Owned lowering permanently available as the differential-testing
oracle (§6.2), makes increment staging safe (§7), and makes every fallback edge (§4.2) sound by
construction. The one place widening is NOT free is the ABI-bearing mode vector, where *both sides
must widen together* — which is precisely why it is classed ABI-bearing (§3.1) and why R3 exists
(§5).

### 2.2 The escape axis (frames)

Per allocation/binding site: does the value's lifetime exceed its defining frame?
`E = {NoEscape ⊑ Escapes}` (join toward `Escapes`). A value **escapes** iff it flows along an
**escape edge**:

1. **Return** — flows into the frame's return value (directly or embedded in a constructed value).
2. **Store** — stored into a longer-lived value (constructor field of an escaping ADT, Vec element
   of an escaping Vec).
3. **Escaping capture** — captured by a closure that itself escapes by rules 1/2/4.
4. **Suspension crossing (R6 — REQUIRED, the S98-0486 class).** The value flows into anything
   whose *dynamic* extent is deferred beyond the frame's own: a **trampoline-deferred `ParBind`
   continuation** (captures living in a returned IO tree run later by the trampoline), a
   **`LaunchContinue` launched sub-tree** (detached strand, no join in the parent's extent), or
   any **IO-tree capture** handed to the trampoline. Suspension points ARE escape edges. This is
   how the §5.5.2 ParBind-across-suspension caveat **dissolves by classification, never by
   widening the borrow**: the escape query classifies these captures as "escapes", so the retain
   stays — the general analysis reproduces the ad-hoc exclusion as an inferred fact. `/qa` keeps
   the ASan/UAF guard on exactly that site (part 17).
5. **Owned handoff at an opaque edge** — passed `Owned` to a callee with no summary (undeclared
   extern, platform effect, HOF) — conservatively escapes. Extern primitives/intrinsics carry
   the §3.1(a) declared fact table precisely so this rule does not fire at every leaf of user
   code.

`NoEscape` drives Q2's stack/region mechanism. Passing a value `Borrowed` to a summarised callee
is **not** an escape edge (the callee provably does not extend its lifetime) — that
non-edge is what makes the interprocedural analysis strictly stronger than the backend-local walk
release-doc §8.3 originally defaulted to.

### 2.3 The confinement axis (threads) — op-wise, not reachability-wise

Per cell: `C = {Confined ⊑ Crossing}` (join toward `Crossing`). **What atomicity protects is
concurrent RC operations on the same count word** — nothing else. The definition is therefore
**op-wise** (user-directed 2026-07-02, replacing the earlier reachability-based draft): a cell
is **`Crossing`** iff RC ops on it may execute **concurrently on more than one thread**; it is
**`Confined`** — and its RC ops non-atomic (Q3) — otherwise. Mere reachability from another
thread never forces atomicity; only the possibility of a concurrent RC op does. The
reachability draft conflated two very different edge classes:

- **Lenient-eval sparks are structured fork-join** (spec §12.4.3; `lenient-eval.md`
  §4.2/§4.4/§4.5) — always joined within the parent frame's dynamic extent. A cell whose only
  cross-thread accesses are **borrowed joined-spark reads** — which increment I makes rc-free
  on the spark side (borrowed capture §8.2 + borrow-through-projection §4.4) — has **all its
  surviving RC ops on the parent thread** ⇒ stays `Confined` ⇒ non-atomic. This directly
  attacks the S99 (b) atomic-bouncing term on the exact F2 shape: the shared board read by
  guess sparks.
- **Genuinely deferred edges** — trampoline-deferred `ParBind` continuations, `LaunchContinue`
  trees, reactor/trampoline handoffs — have no join-in-frame argument (deferred dynamic
  extent) and stay at the conservative point, `Crossing`. Precision there is deliberately not
  pursued: it is swamped by IO magnitude anyway.

The reachability rule survives as the **conservative approximation** the analysis widens to
whenever the op-wise proof fails: a value reachable from a spark thunk's captures or result, a
`ParBind` branch, a `LaunchContinue` tree, anything handed to the reactor/trampoline, or an
`Owned` handoff at an opaque edge is `Crossing` **unless the analysis proves no RC op on it can
execute off the owning thread** (e.g. all spark-side access is borrowed and
projection-covered); a spark-side path that joins to `Owned` or otherwise materializes
re-widens the cell to `Crossing`. The fork boundaries are all representationally visible
(`MonoExpr::ParBind`/`LaunchContinue` variants, the spark sites) — Principle 20: read, not
analysed. Interprocedural propagation is what the summary adds: "does this callee spark over
its param, and does the spark side hold RC ops on it?" rides the callee's summary instead of
forcing every caller to assume `Crossing`.

**`Transferred` — the named middle point (adoption routed to the typecheck proposal).** Between
the ends sits a third semantic class: a value whose thread crossings all occur **across
synchronization edges** (IVar put→force, spark join — each a happens-before edge) has RC ops on
multiple threads but never *concurrently* — non-atomic RC remains sound, provided every
inter-thread op pair is ordered by such an edge (the Send-vs-Sync analogy: *moved* between
threads, never *shared* between them). The spine **names** the point
(`Confined ⊑ Transferred ⊑ Crossing`) but does not commit it for increment I: whether it is
worth carrying as a distinct lattice point — versus collapsing to `Crossing` until the F-series
data demands it — is **part-9 territory** (§10 item 3), with the happens-before proof
obligation stated explicitly. Collapsing it is monotone-sound by construction.

**Coordinates compose per value-site:** `(mode, escape, confinement)` — e.g. a joined-spark
capture is `(Borrowed, NoEscape, ·)` with the *parent's* cell's confinement decided op-wise:
if the spark side is provably rc-op-free (borrowed capture, projection-covered reads), the
cell is `Confined` and non-atomic **even while a live borrow crosses a thread**; it stays
`Crossing`/atomic only if some spark-side path actually holds RC ops on it (joins to `Owned`,
materializes). The confinement query is about which RC ops *exist on the cell and where they
can run*, computed over **all** its reachable sites — the per-crate typecheck proposal owns the
precise per-cell join (part 9).

---

## §3. The typecheck→backend contract (part 2 — the two-class contract, R1)

The contract distinguishes **two classes of boundary fact**. Do not conflate them; they have
different soundness obligations, different carriers, and different redefinition consequences.

### 3.1 Class A — ABI-bearing: the per-param mode vector

**What:** one `Mode` per parameter of a callable, plus the callable's **result mode**
(`Fresh` / `ProjectionOf(i)` / `AliasOf(i)` — §3.3/§4.4; a borrowed result is a caller/callee
agreement exactly as a borrowed param is), attached to the callable's signature.
**Where it rides:** `MonoDefn` (each `MonoDefnVariant`) for the compile in hand, and the
callable's symbol-table entry for persistence (serialised into `.meta.json` — §5.1).
**Why ABI:** caller and callee MUST agree. A callee compiled `Borrowed` (emits no param dec)
called by a caller emitting the Decision-24 consuming inc **leaks**; the reverse **double-frees**.
The mode vector is therefore part of the function's ABI exactly as its type signature is —
`access-pattern-as-ABI` is the fact that forces §5.

**R2 — the first-order pin (binding).** Per-param modes attach **only to statically-resolved
calls** (`resolved_call = Some` — `mono_expr.rs`; trait dispatch is already static post-mono).
Closure-valued / higher-order call sites keep the **uniform Decision-24 convention**: **no modes
on arrow types, no multiplicity polymorphism** (`Fn`/`FnMut`-style machinery is exactly what this
design declines). A function called *through a closure value anywhere* must therefore be
compiled so its closure-entry path is Decision-24-conformant; the per-crate proposals resolve the
mechanics (dual entry vs. mode-erased wrapper vs. join-to-Owned for closure-converted functions —
part 11/12 question, §10). Sound either way by monotone widening.

**The in-tree precedent for the dual-entry question is the primitives themselves.** Primitives
already exhibit exactly the dual-entry shape §10 item 6 asks about for user functions: an
**inline lowering at statically-resolved sites** (`compile_vec_get`/`compile_vec_set`/
`compile_vec_push`/`compile_vec_len`, `cranelisp-backend::compiler::vec_codegen`) plus a
**GOT-backed Decision-24 value path** for closure/HOF use (synthesized zero-capture closure
wrappers resolving through standard GOT-indirect dispatch — `compile_operator_as_value`,
`compiler/literals.rs:263`, operator wrapper map at `:239`). The per-crate proposals treat this
as the precedent informing the dual-entry candidate. **As-built gap, recorded honestly:** the
precedent is only partially real today — `vec-get`/`vec-set`/`vec-push` allocate GOT slots that
stay **NULL** (no extern body exists; `cranelisp-primitives/src/lib.rs` rustdoc on the
vec-query-family insert, ~:245–262); only `vec-len` has an extern shim; and the
operator-as-value wrapper map covers arithmetic/comparison only. Value-use of the vec query
family is a **verified defect** (`/qa` triage, S100 Phase 3: `vec-get`/`vec-set`/`vec-push` as
values SIGSEGV through the NULL slot in both `--run` and the REPL; failing-not-ignored repros
`tests/vec_query_value_use.rs` + green `vec-len` control; owner `/backend`). **Sequencing pin:
the fix precedes the §3.1(b) sibling landing (same registration seam) and the R2
value-wrapper seam — wrapper emission must never route value-use of a summary-carrying
primitive through a NULL slot** (backend proposal §12.7 carries the same requirement). The
target design implies every primitive gets a real GOT-backed value entry.

**Boundary pins (all Decision-24-by-construction — modes never cross these edges):**

- **Constructors:** field-store consumes; always `Owned` per param (the ADT owns its fields).
- **Extern primitives / intrinsics — the ABI pin stands; the analysis facts do NOT ride it
  (split ruling, user-directed 2026-07-02).** The Rust bodies dec their own heap args (§3.3
  extern audit, `ring2-rc.md`) and the consuming convention is unchanged — but two separable
  things were previously conflated here, with the deferral miscalibrated:
  - **(a) Hand-declared per-primitive analysis facts — REQUIRED in increment I.** Per param:
    only-read? retained/escaped? Without them, §2.2 rule 5 (Owned handoff at an opaque edge ⇒
    conservatively escapes) poisons every argument flowing into any primitive — and since
    virtually every leaf of user code is a primitive use, increment I would infer almost
    nothing: `(vec-len xs)` would widen `xs` to `Owned`/`Escapes`, killing the flagship
    sum-loop inference. `vec-get` is covered by the §4.4 projection rule, but `vec-len`, `eq`,
    `display`/`trace`, the string family etc. need a declared fact table; the `ring2-rc.md`
    extern audit is its seed. Declared facts are **analysis inputs only** — no ABI change, no
    Rust-body change: with the consuming convention unchanged, a `Borrowed` caller adapts at
    the extern site per §4.3 (inc before the consuming call), paying the 2-op pair but never
    poisoning the mode. Primitive summaries are **declared constants seeding the fixpoint at
    the leaves** — the ground-truth base case, zero analysis cost — and have **no R3
    exposure**: primitives are never redefined at the REPL; a summary change is a
    compiler-version change, covered by the `CACHE_SCHEMA_VERSION` bump.
  - **(b) Calling-convention refinement — OPTIONAL, routed to the backend proposal (§10
    item 14).** Eliding the caller-inc/body-dec pair at extern sites via a borrowed-convention
    **sibling symbol** (dual-symbol pattern: the existing consuming export stays untouched, so
    the analysis-off oracle's byte-identity (§3.4) is preserved; the backend targets the
    borrowed sibling when summary + toggle allow). A secondary win by measurement: the
    dominant S99 term — the 81 `rc_inc` per copy — lives **inside** the
    `vec-set-copy`/`vec-push-copy` Rust bodies and is cured by R5/Q4, not by call convention.
    The increment-I template instance is **`str-len`** (backend proposal §9.2) — a genuinely
    extern-consuming only-read leaf. `vec-len` is NOT a sibling candidate (FIXME 0469
    correction, verified against source): its statically-resolved sites are inline-lowered
    (`compile_vec_len` — zero RC ops on a borrowed arg today) and its extern shim serves only
    the Decision-24 value path, which R2 pins to the consuming convention permanently — there
    is no caller-inc/body-dec pair to elide. `vec-len`'s increment-I role is entirely its
    (a) fact-table row.
- **Platform effects (the C-ABI DLL edge):** the platform ABI (`platform-interface.md`) is
  version-gated and binary-decoupled; mode vectors do NOT join the manifest. Platform calls stay
  Decision-24. Same for every named-extern intrinsic call.
- **The `--link`/exe-bundle startup contract** (DEF-6 class): untouched.

### 3.2 Class B — advisory: per-site facts

**What:** escape (§2.2), confinement (§2.3), static uniqueness (§2.1) on allocation / capture /
binding nodes.
**Where it rides:** fields on the relevant `MonoExpr` nodes.
**Soundness class:** *may-optimize permissions*. A backend that ignores any or all of them is
still correct, only slower (the monotone-soundness property, §2.1). They impose no cross-function
agreement obligation, survive partial consumption, and are safe to drop on the floor in any
lowering path — which is what keeps the conservative lowering reachable (§6.2) and keeps
increment staging trivially safe.

**Most of the S99 win is advisory-class.** Borrow-through-projection (rc-free reads), stack/region
for non-escaping temporaries, non-atomic RC for confined values, and reuse are all consumed as
per-site permissions; the ABI-bearing vector is what makes the *interprocedural* read-path
(callee-borrows-its-param) reach through calls.

### 3.3 The designed carrier fields (NOT landed this sprint)

> **No `cranelisp-types` edit lands in S100.** The fields below are the designed shape the first
> implementation sprint lands, `/arch`-authored, with the `public-api.txt` + `interfaces.md` +
> BC §7 cascade and a `CACHE_SCHEMA_VERSION` bump in that change-set. Landing them now would be
> speculative-interface debt (Phase-2 ruling).

Sketch (still subject to the implementing sprint's `/arch` pass; enriched shape folded in
2026-07-03, resolving FIXME 0467 — the typecheck proposal's §2.2 carries the field-by-field
justification):

```rust
// cranelisp-types/src/mono_expr.rs (designed)
pub enum Mode { Owned, Borrowed, Copy }            // §2.1; Unique is NOT a Mode — see below

pub struct ModeSummary {                            // per callable
    // ABI-bearing half (input to the §5.4 summary-diff gate + §5.6 slot versioning):
    pub param_modes: Vec<Mode>,                     // one per param, positional
    pub result: ResultMode,                         // default Fresh = Decision-24 as-built
    // Advisory analysis-fact half (#[serde(default)] ⇒ conservative; sound to ignore):
    pub param_flow: Vec<ParamFlow>,                 // where an Owned param's reference goes
    pub spark_ops: Vec<bool>,                       // per param: callee may run RC ops on it
                                                    // off the calling strand (§2.3)
    pub result_unique: bool,                        // increment II (§10 item 5(b) chaining);
                                                    // emitted false throughout increment I
    // uniqueness-as-mode deliberately absent: not static ABI (R4)
}

pub enum ResultMode { Fresh, ProjectionOf(usize), AliasOf(usize) }  // §4.4
pub enum ParamFlow  { Consumed, IntoResult, Retained }              // makes Q2 interprocedural

// MonoDefnVariant gains: pub mode_summary: Option<ModeSummary>,   // None ⇒ Decision 24
// Site-fact fields on MonoExpr alloc/capture/binding/projection nodes (advisory):
//   escapes: Option<bool>, confined: Option<bool>, unique_static: Option<bool>,
//   plus the provenance root for borrowed projections (§4.4 — the one interprocedural
//   fact the backend cannot derive locally once a projection has crossed a call)
//   (None ⇒ conservative: escapes/crossing/shared/no-provenance)
```

**Why the result mode is ABI-bearing (the 0467 folding rationale).** The S99 read shape
projects through **compiled accessor functions** (`(vec-get (gcells g) 0)` — `gcells` is an
ordinary `Def`); for borrow-through-projection (§4.4) to compose *across calls*, an accessor's
summary must say "result is a borrowed view rooted in param i" — and whether a returned
reference is owned (caller decs) or borrowed (caller must not dec) is a caller/callee agreement
exactly like the param vector: wrong on either side is a double-free or a leak. It therefore
joins the §5.4 summary-diff gate and the §5.6 slot-versioning discipline — one more compared
field, no new machinery. The advisory trio stays out of the ABI by construction (ignoring it is
monotone-sound): `param_flow` is what makes Q2 interprocedural (without it, §2.2 rule 5 fires
at every summarised call — `(defn keep [x] (Some x))` vs `(str-len s)` are indistinguishable);
`spark_ops` is what makes Q3 interprocedural (§2.3's propagation question, now with a field).
Defaults preserve strict additivity: absent/omitted ⇒ `Fresh` / all-`Retained` / all-set /
`false` — byte-for-byte the Decision-24 conservative point, so old caches and unresolved edges
deserialise to today's behaviour. Two small carriers ride the same implementing-sprint
change-set: the **per-entry value-use mark** (typecheck §8.3 — tells the backend wrapper
emission is required) and the **declared-fact payload on `DefKind::Primitive` entries**
(§3.1(a); plus the optional `borrowed_sibling_slot` when a §3.1(b) sibling is registered —
backend §9.1).

The symbol-table half: `ModeSummary` joins the **callable `DefKind` variants** (the S83
Principle-20 reshape put `got_slot` on `UserFn`/`Primitive`/`Constructor`/`PlatformEffect`; the
mode vector correlates with callable-ness the same way and rides the same variants —
non-callable kinds carry no summary field by construction). Serde-visible ⇒ persisted in
`.meta.json`; `#[serde(default)]` = `None` = Decision 24, so old caches deserialise to the
conservative point (§5.1).

**The narrowness counterweight (Principle 2 — binding on both per-crate proposals).**
`compute_last_uses`, `HeapCategory::classify`, reuse-token plumbing, and every intra-function
site decision **stay in the backend**. The boundary carries only what locality cannot compute —
interprocedural facts. Phase-3+ proposals must resist enriching the contract with anything the
backend can derive soundly in-function; every proposed field addition is an `/arch` FIXME, judged
against this sentence.

### 3.4 Tier statement + oracle (R7)

**The mechanisms land in the shared Cranelift lowering** — not in `--release`. The S99 contention
lives on the only tier that exists, and FIXME 0408's exemplar-witness is scheduled before
`--release`. This **supersedes D-Rel-4's "the Cranelift dev path stays unoptimized" for the
memory-model subset** (Q1–Q5 mechanisms); the codegen-engine mechanisms (M-LLVM, M1 direct calls,
M2 LTO, M3 IR-level RC fusion) remain release-tier-only per `release-llvm-backend.md`. The
correctness-oracle role D-Rel-4 assigned to the unoptimized path is preserved by the contract
itself: **the conservative all-Owned / all-atomic / all-heap lowering remains reachable via an
analysis-off toggle** (env-gated, byte-identical to today's lowering when on) and is the standing
differential baseline / correctness oracle for `/qa`'s harness (part 17). `--release` later
consumes the *same* facts through the same `MonoExpr` boundary — two tiers, one input, one
analysis (Principle 7).

### 3.5 Increment-compatibility constraint (from finding 4)

Increment I must not ship any borrow ABI that increment II's reuse machinery would break.
**Reuse tokens / drop-guided-reuse plumbing are intra-function (Perceus-style) and stay OFF the
call ABI** — part 16 designs them as function-local values threaded from a drop site to a
same-layout allocation site, never as params/returns. With that constraint, II adds queries and
mechanisms without reshaping I's contract: the `ModeSummary` type never migrates, only emitted
precision grows.

---

## §4. Pipeline sequencing (part 3)

### 4.1 Where the analysis runs

**Inside typecheck, AFTER monomorphisation instantiation, over the mono call graph** — in the
crate that owns the graph it walks (`traits/monomorphise.rs`; Principle 3: facts flow from where
they are stable; Principle 7: no graph re-derivation in the backend). Per **module-cluster**, with
**imported summaries as boundary conditions** (Principle 17 module locality — the MLKit/GHC
per-module-with-persisted-signatures shape; no whole-universe pass, no closure walk: callee
summaries are read through the same per-symbol chain-follow every other cross-module fact uses).
**Fixpoint within a cluster** for recursion: the mode lattice is finite and the transfer functions
monotone (joins only move toward `Owned`/`Escapes`/`Crossing`), so the fixpoint terminates;
initialise optimistic (`Borrowed`/`NoEscape`/`Confined`) and widen on evidence. **Conservative
default at every unresolved edge** — HOF sites (R2), missing summaries, undeclared externs,
platform effects: the Decision-24 point (extern primitives/intrinsics carry the §3.1(a) declared
fact table, so they are declared leaves, not unresolved edges). No pipeline re-sequencing is
needed; the pass slots after the existing mono step and before `MonoDefn` hand-off to codegen.

### 4.2 Cross-module and generic instantiations

- **Concrete (non-generic) callables:** the summary is computed in the defining module's cluster
  and persisted on its entry; importers consume it as a boundary condition.
- **Generic definitions:** a scheme has no single summary — modes are per *instantiation*
  (monomorphisation is the enabler: it dissolves borrow-vs-owned mode polymorphism into concrete
  per-instantiation vectors). Instantiations are minted at the use site from the callee's
  persisted `ast` (the entry already carries it — `module-caching.md` §14.1), which is where
  mono itself runs; the **instantiation's summary is inferred at mint site** alongside the
  instantiation. No cross-module generic-summary store is needed; dedup/caching of repeated
  instantiations is a typecheck-proposal concern (part 7), correctness is not at stake
  (re-inference is deterministic over the same inputs).

### 4.3 The borrow-monomorphisation chicken-and-egg — resolved for I, open-by-design for II

**Mode does NOT enter the mono key in increment I.** One summary per instantiation, joined over
all its call sites. A caller whose argument is more-owned than the callee's summary requires
adapts **caller-side** (keeps ownership, decs after the call) — sound and near-optimal, no body
duplication. Mode-in-key specialization (two bodies: borrowed-param vs owned-param) is a
precision-vs-code-bloat trade that part 11 explores **with data** for increment II (the
three-mechanism write-path comparison, §10 item 5); the contract
must not preclude it, and does not — the key is a mono-internal concern, invisible on the boundary.

**Monomorphisation dissolves mode polymorphism; it does NOT dissolve uniqueness (R4).** rc==1 is
dynamic. The general increment-II write-path discriminator is the **dynamic rc==1 check** (reuse
tokens / drop-guided reuse — how Koka and Roc do it, and what today's Vec-COW mutate-in-place
already is). This is a first-class designed outcome, not an inference failure — and it defuses
most of the mode-in-key pressure, since the reuse decision stays dynamic per-site rather than
forcing duplication.

### 4.4 Borrow-through-projection (the rule that shrinks S99; detail = part 8)

Projecting a component out of a `Borrowed` aggregate yields a `Borrowed` component: `(get xs i)`
on a borrowed `xs` produces a borrowed element — no inc at extraction, no dec at release, the
aggregate's owner covers the read (the `borrowed_vars` match-arm rule, §5.5, generalised from
"scrutinee field binding" to every projection out of a borrowed value). Chained projections
compose. This makes the entire read path rc-free and shrinks the S99 term to genuine
materializations. The typecheck proposal owns the precise rule (interaction with last-use,
projection out of `Owned`, lifetime nesting proof); the spine pins that the rule MUST exist and
MUST compose transitively. **Interprocedurally, transitivity rides the summary's result mode**
(§3.3): an accessor whose result is a borrowed view of param i publishes `ProjectionOf(i)`, and
the caller roots the call's result at its own argument's root — without it, every accessor call
re-materializes (2 RC ops per projection) and the read-path win shrinks to intra-function +
inline-`vec-get` shapes.

---

## §5. Mode summaries, module caching, and the R3 redefinition model (part 4)

### 5.1 Batch (`--run`/`--link`): already conservatively covered

The `.meta.json` **is** a serialised `SymbolTable` (`module-caching.md` §14); the per-callable
`ModeSummary` joins the serde-visible payload on the callable `DefKind` variants (§3.3), gated by
the existing `CACHE_SCHEMA_VERSION` bump discipline — old caches deserialise summaries as `None`
= Decision 24 and, being pre-bump, are invalidated wholesale anyway.

**Invalidation needs no new key.** Two existing mechanisms compose to keep summaries transitively
fresh: (1) an importer is invalidated when any **direct import's source hash** changes
(`module-caching.md` §3) — over-approximating "callee summary changed" for direct edges; and
(2) the session **`recompiled`-set cascade** (`src/session_setup.rs`: "if a dependency was
recompiled, all its dependents must also recompile") makes it transitive — if C's change recompiles
B (B's summaries may change with B's source unchanged), B's membership in the recompiled set
recompiles A in turn. Any upstream change therefore transitively recompiles all dependents before
their compiled inc/dec schedules could disagree with a callee summary. Conservative, correct,
zero new machinery — exactly the §6 "invalidation is conservative" discipline.

### 5.2 The REPL hazard — and the R3 ruling (BINDING, user-directed 2026-07-02)

**The hazard.** Per-param mode is ABI (§3.1). Today, redefinition is a **GOT-slot patch only**
(`session_v4.rs:267` — the old `ModuleEntry::Def` drops, the new code pointer lands in the slot;
callers are never recompiled; they pick up the new callee through GOT-indirect dispatch at their
next call). Under mode summaries, a redefinition that changes a param's inferred mode invalidates
**every already-compiled caller's emitted inc/dec schedule** — the patched slot silently connects
old-ABI callers to a new-ABI callee: leak or double-free. This is the DEF-6 class (invisible below
a threshold, catastrophic above it) and MUST NOT be left implicit.

**The ruling.** The ABI-pinning dodge (Phase-2 candidate (i): dev-session pins call ABI to
Decision 24, consumes advisory facts only) is **REJECTED** — it forfeits the interprocedural
read-path win in the tier developers live in. Instead: **the dev session re-typechecks and
recompiles caller functions on redefinition, managing the cascading type/mode errors that
follow** — building the dependent-recompilation machinery the session currently lacks. This is the
load-bearing new subsystem the sprint commits to.

**It also closes a latent pre-existing hole.** Signature-as-ABI did not arrive with modes: a
*type-changing* redefinition already invalidates callers' compiled assumptions (an old caller
passing an `Int` where the redefined callee now reads a pointer), and today nothing re-typechecks
or recompiles them — the session is coherent only for signature-preserving redefinitions. Mode
joins the signature; the machinery below cures **both**. That is why it is designed as a general
signature-coherence subsystem, not a mode-special-case.

### 5.3 Actors and functions of the redefinition subsystem (Principle 21)

- **The user / REPL turn** — submits a redefinition of `f`; turn-based and synchronous
  (`overview.md` §cadences: one prompt → one submission → wait → display).
- **The session eval path** (`session_v4.rs`) — today: typecheck the form, codegen, replace the
  entry, patch the GOT slot. Gains: the transaction of §5.5.
- **The symbol-level dependency graph** — forward edges **already persisted**:
  `ModuleEntry::Def.callees: Vec<FQSymbol>` (Decision 21, `module.rs:725`, serde-visible in
  `.meta.json`). The subsystem adds the **reverse index** (who-calls-whom⁻¹), *derived* from
  `callees` — never a second authored store (Principle 7) — maintained incrementally as entries
  are (re)registered. **The ownership fixpoint (§4.1) walks the same edges**: one graph, two
  consumers; building the index is not R3-only cost.
- **The scheduler / worker machinery** — the recompilation executor. Precedents generalised:
  module-level dependent reload (the file-watcher path in `session_v4/lifecycle.rs` scans all
  tables' `imports` for dependents of a changed module and `reload_module`s each — S35/S37
  lineage), `re_register_module` (fresh-sexps re-queue), and the S45 error-cascade machinery
  (`scheduler.reset_module` / `reset_all_failed_modules` + embedded-original-error reporting).
- **The GOT** — the commit substrate: per-slot atomic writes, append-only slot allocation.
  ABI identity is encoded in slot identity (§5.6 — an ABI-changing redefinition allocates a
  fresh slot; the old slot freezes).
- **The heap and the runtime cadence** — the actors recompilation *cannot* reach: closure values
  embedding direct code pointers, suspended IO-tree continuations, in-flight frames, detached
  strands. §5.6's design exists because of them.

### 5.4 The transaction — trigger and affected-set computation

On redefinition of `f` (same flow for a file-watcher single-defn delta once symbol-level diffing
exists; wholesale module reload remains the coarse path):

1. **Typecheck + infer `f` as usual** (its cluster fixpoint re-runs; `f`'s new `ModeSummary` and
   type scheme are produced).
2. **Summary-diff gate (the fast path — most redefinitions).** If `f`'s **ABI-relevant surface**
   — type scheme + per-param mode vector + result mode (§3.3) — is unchanged, the existing
   behaviour is already sound:
   codegen `f`, patch its slot, done. Body-only edits, docstring edits, and mode-preserving
   changes stay exactly as cheap as today.
3. **Affected-set closure (the slow path).** Otherwise, compute the caller closure over the
   **reverse index, statically-resolved edges only**: callers reaching `f` via
   `resolved_call = Some` compiled against `f`'s old vector. Closure-valued uses are
   **insensitive by construction** (R2 — closure call sites are permanently Decision-24) and do
   not join the set for *mode* changes; they DO join it for *type* changes (a type-changing
   redefinition breaks closure-typed uses too — the type checker surfaces those as ordinary
   cascade errors in step 4; the reverse index therefore records value-references alongside call
   edges, a typecheck/int-proposal detail, with the module-level reload of step 4 as the
   conservative fallback where per-reference precision is missing).
4. **Re-infer + re-typecheck + recompile the affected set in reverse-topological order**
   (callees before callers), re-running the cluster fixpoint for recursive clusters. A recompiled
   caller `g`'s own summary may change in turn (its param modes can depend on what it passes to
   `f`), so the closure is **iterated to fixpoint over summaries** — the same monotone machinery
   as §4.1, run incrementally from the edit; termination by the same finite-lattice argument.
   Cross-module callers participate via FQSymbol edges exactly as intra-module ones; where
   symbol-level precision is unavailable (e.g. a module loaded cache-only without a live reverse
   index), the **conservative fallback is the existing module-level dependent reload** — sound by
   over-approximation, per the same discipline as §5.1.
5. **Commit** (per §5.6 — no stop-the-world) **and surface** (per §5.5).

**Sizing honesty:** the slow path is bounded by the real dependency cone of an ABI-changing edit —
the same work a batch recompile would do for that cone, moved into the interactive turn. The
summary-diff gate is what keeps the common case at today's cost; the fixpoint's optimistic
initialisation keeps re-inference from ping-ponging.

### 5.5 Cascading type/mode error management

A caller that no longer typechecks under `f`'s new signature/mode is a **cascade error**. The
design generalises the S45 model (module-level `reset_module` + embedded-original-error) to
symbol level:

- **The failing caller `g` is marked BROKEN, with provenance.** Its entry stays in the table
  (scheme/docstring/ast intact for introspection and recovery) but its `code` is cleared and its
  **GOT slot is patched to a trap stub** that, if called, raises a clean runtime error naming the
  provenance: `g is broken by the redefinition of f: <original type/mode error>`. Note that under
  §5.6's slot versioning `g`'s *old* code is ABI-consistent (it references frozen old slots), so
  serving it stale would be memory-safe — the trap is a **deliberate UX ruling**, not a soundness
  necessity: silently executing code that diverges from the source the user just changed is the
  worse dev experience (the self-documenting-REPL principle: fail loud, with provenance,
  recoverably). (The stub is the symbol-level analogue of the scheduler's Failed pool; its
  mechanism — one intrinsic + per-symbol baked message vs. per-symbol stub emission — is a
  backend-proposal question, §10.)
- **The turn reports the full cascade**, grouped: `f` redefined; recompiled OK: [...]; broken:
  `g` (error), `h` (error). The REPL's self-documenting principle applies — each broken symbol
  answers `/info`/`/sig` with its broken status + provenance.
- **Recovery is by redefinition**, either direction: redefining `g` to match, or redefining `f`
  back, re-runs the transaction; a broken symbol that re-typechecks is recompiled and its slot
  re-pointed at real code. Broken-ness is ordinary session state, not a sticky mode.
- **Transitivity:** a broken `g` cannot be recompiled-against, so callers of `g` compiled against
  `g`'s (unchanged) old summary remain valid **only if** `g`'s ABI surface didn't change — and it
  didn't (it failed before producing a new one). Callers of `g` therefore stay live and simply
  hit the trap through `g`'s slot at runtime. No transitive breaking is needed; provenance chains
  are depth-1 by construction.

### 5.6 Commit soundness — ABI-epoch slot versioning (no stop-the-world)

**Why in-place patching cannot be rescued.** Rebinding `f`'s existing slot to a new-ABI body,
even under a stop-the-world multi-slot patch, is unsound against code the transaction cannot
recompile: **closure values are heap data embedding direct code pointers to old bodies** (the
`HeapClosure` code-ptr field), and suspended IO-tree continuations hold such closures across
trampoline turns. A closure minted by old-`g` before the redefinition — stored in a binding, an
IVar, or a pending continuation — resumes its old-ABI body *after* any patch window and calls `f`
through the rebound slot: a mixed-ABI edge no quiesce can prevent. Recompilation reaches symbol
table entries; it cannot reach the heap.

**The design: an ABI-changing redefinition never rebinds the old slot** (Principle 20 — make the
illegal state unrepresentable by encoding ABI identity in slot identity):

- **ABI-changing redefinition ⇒ fresh slot.** New `f` is installed at a **newly allocated GOT
  slot**; `f`'s entry now carries the new slot. The **old slot freezes**, permanently pointing at
  the old implementation. Every recompiled caller whose own ABI surface changed in the fixpoint
  gets a fresh slot the same way; a recompiled caller whose ABI is unchanged is patched in place
  (its callers need no recompile). A BROKEN caller's trap stub is patched **in place** on its
  existing slot — the stub raises without touching its arguments, which is signature-safe, and
  in-place is what makes existing unrecompiled callers reach it. Stale code — heap closures,
  suspended continuations, in-flight frames, and the old bodies of every not-yet-recompiled or
  BROKEN caller — references old slots exclusively, reaching only old-ABI implementations.
  **No mixed-ABI edge can exist, by construction**; the chain is consistent transitively (an old
  body's calls resolve through old slots to old bodies, recursively). Each slot write is
  independently atomic and independently safe — **no quiesce, no trampoline pause, no patch
  window.**
- **ABI-preserving redefinition (the §5.4 fast path) ⇒ in-place patch, as today.** Late binding —
  stale closures and in-flight strands pick up the new body at their next call — is the prized
  REPL semantic and remains safe exactly because the ABI is unchanged.
- **Retention rule.** The frozen slot's target must stay executable: the superseded entry's
  `Code::Jit` handle is retained by the session for the frozen slot's lifetime instead of
  dropping (extending Decision 31 Scenario 2, whose reclaim currently fires on entry
  replacement; precedent for session-lifetime retention: `kept_dlls`). A dev-session-bounded
  leak, proportional to ABI-changing redefinitions — acceptable and measurable.
- **Persistence footprint (binding facts, user-verified against source 2026-07-02).**
  (i) `got_slot` values AND `next_got_slot` are serialized in `.meta.json` (§5.1's carrier;
  `module.rs:135` — a serde-visible monotone counter, no free list; allocator at `:609`), and
  REPL definitions **persist** (regenerated backing file per `repl/spec.md` §15.4 + the
  nice-worker `.o`/`.meta` writes). (ii) `.meta` slot numbers are **load-bearing against the
  `.o`'s machine code** — GOT-indirect call sites embed slot indices
  (`load(slab_base + slot*8)`) — so faithful-write after every redefinition is mandatory and
  renumbering-at-cache-write is **impossible by construction**; compaction only ever rides the
  cache-invalid full-recompile path. (iii) An ABI-changing **persisted** redefinition therefore
  leaves a **permanent hole** in the slot space that survives restart in a valid cache — 8
  bytes of GOT slab each (body-only edits take the §5.4 fast path and keep their slot).
  (iv) The persisted `next_got_slot` high-water mark **is the freeze boundary**: a new session
  allocates strictly above anything any cache could reference. Frozen-slot **bindings** — the
  retained `Code::Jit`, the old code pointers — die with the session: freezing is a
  **session-memory commitment only**, and restart is the zero-cost reclamation of the
  retention-rule leak. (v) Load-time hole reclamation would be sound (after restart no referent
  survives) but is **rejected — deferred indefinitely, trigger-based**: see FIXME 0466
  (`design/arch/fixmes/0466-got-frozen-slot-reuse-at-session-load.md`).
- **Semantics note.** Stale code sees pre-redefinition behaviour of the whole old chain (frozen
  world), rather than today's mid-chain late-binding mix — for ABI-changing edits this is the
  *more* coherent semantic, and recompiled callers (the reachable-by-name world) are fully
  current. The turn's cascade report (§5.5) is where the user sees which world each symbol is in.
- Batch modes are untouched (no redefinition; `--link` a fortiori). The slot-allocation cost is
  one GOT entry per ABI-changing redefinition.

### 5.7 Sequencing constraint (binding)

**The dependent-recompilation machinery lands BEFORE (or with) the first increment that enables
ABI-bearing modes in the dev session.** An increment-I build with summaries emitted but the
transaction absent is not shippable to the REPL path — that would be the DEF-6 hole open. The
implementation roadmap (sprint-planned) must order: machinery (type-cascade cure, valuable
standalone) → increment I modes. The analysis-off oracle toggle (§3.4) doubles as the interim
guard: with analysis off, summaries are absent and the session degenerates to today's sound
Decision-24 behaviour.

---

## §6. Fallback and soundness discipline (part 5)

### 6.1 The conservative point is total

Every dimension has a defined conservative value equal to as-built behaviour: mode `Owned`
(Decision 24), escape `Escapes` (heap), confinement `Crossing` (atomic), uniqueness `shared`
(clone/COW), duplication `RC-share`. **Every fallback is correct, only ever suboptimal** — the
analysis can time out, a summary can be missing, an edge can be opaque, a whole crate-feature can
be disabled, and the program still runs with today's semantics and today's costs. There is no
"analysis required for correctness" path anywhere in this design; the analysis is a pure
performance refinement of a sound baseline. (The one obligation that is NOT optional once modes
ship is agreement on the ABI-bearing vector — §3.1/§5 — which is a coherence obligation between
compiles, not a precision obligation on the analysis.)

### 6.2 The differential oracle (R7)

The **analysis-off toggle** (all-Owned/atomic/heap lowering — byte-identical to pre-S100 codegen)
is a permanent, reachable configuration: the correctness oracle for `/qa`'s differential harness
(same corpus, analysis-on vs analysis-off, byte-identical observable output; sustained-load +
ASan/checking-allocator lanes for the UAF classes — S98 bug-#2, DEF-6, the R6 suspension site),
and the honest baseline for every performance claim. This is the release-doc §11 discipline
applied one tier earlier.

### 6.3 The `Copy` row's mechanism (R5) — named, routed to the backend proposal

For an ADT that stays heap-allocated, "bit-copy" is vacuous — copying the pointer still bumps the
refcount. The `Copy` row pays only when the **representation is a value** (unboxed/inline). The
named mechanism is **value-representation flattening of Copy-eligible ADTs** under the S83 §12.1
relaxation (spec §12.1 value-representation is backend-internal once codegen is fully concrete —
`concrete-boundary-type.md` §Phase 5): a `Copy`-eligible concrete ADT (all fields transitively
`Copy`, within a size bound) is laid out as an inline value — in registers, in Vec slots, in
parent ADT fields — with **no header, no refcount, no drop glue**. `Copy`-ness is structurally
derivable (Copy iff all fields Copy); eligibility is per **concrete type** (post-mono, so the
classification is total — no `Type::Var` reaches codegen).

**This is plausibly the single largest lever on the S99 `Cell` shape:** an 81-slot Vec of
value-`Cell`s copies with one `memcpy` and **zero** RC ops — the entire 170M-inc term vanishes,
independent of uniqueness. It is therefore a **named backend design question (part 12/16 scope,
increment II)**, not an implicit hope. Its consequences the backend proposal MUST work through:
`HeapCategory` gains a value/inline classification arm; ABI at boundaries (a flattened value
passed where a word is expected — size bound vs boxing-at-edges); Vec-of-values element layout +
`vec-set`/COW interaction; `.o`-cache and `--link` parity (layout decisions must be deterministic
inputs to the cache key discipline); trace/display descriptors. **Until it lands, the `Copy` chain
point is inhabited only by scalars** — stated so the row is never load-bearing-but-mechanismless.

**The eligibility predicate is single-sourced (ruling 2026-07-03, resolving FIXME 0468).** When
R5 lands, TWO crates consume the same per-concrete-type predicate ("Copy-eligible ∧ within the
size bound ∧ single-constructor ⇒ represented as an inline value"): typecheck's mode classifier
(a type sits at the `Copy` lattice point only when its representation is a value — typecheck
proposal §2.2) and the backend's layout decision (`HeapCategory`'s `Value` arm — backend
proposal §7.1). The two are **soundness-coupled, not merely consistency-coupled**: a param
moded `Copy` whose representation the backend did NOT flatten is a pointer bit-copied with no
`rc_inc` — a missing-inc use-after-free. Two independently-maintained copies of a
soundness-coupled pure predicate is the Principle-7 mirror-defect class, so ONE predicate lives
in **`cranelisp-types` beside `HeapHeader`** (`src/heap.rs`) as a pure function over the
persisted type-def view both crates already hold (illustrative:
`value_layout(ty: &ConcreteType, type_defs: …) -> Option<ValueLayout>`); both consumers
delegate to it. The size bound (one word for the first landing — backend §7.2) is a named
constant beside the predicate; **any change to predicate or bound is a `CACHE_SCHEMA_VERSION`-
bump event** (representation change). The alternative — backend-computed classification carried
per-type across the boundary — is rejected: it inverts the derivable-⇒-below-the-boundary
narrowness rule (§3.3) for typecheck's side. **This is a design-level pin only: no
`cranelisp-types` edit lands in S100**; the predicate lands with the R5-increment `/arch`
carrier change-set. Until then no unsound configuration is reachable — the `Copy` point is
scalars-only and `HeapCategory` has no `Value` arm.

### 6.4 The G3 precondition (standing)

Restated from §0 as a numbered discipline: **no reference-identity observer enters the language**
(no pointer-eq, no address in `trace`, no identity hash) while inferred sharing/reuse/flattening
is in force. Uniqueness-driven mutation (Q4) and representation flattening (Q5) are unobservable
*only* under this precondition. Any spec/stdlib/introspection proposal that would breach it routes
through `/arch` first.

---

## §7. Two-increment staging (Principle 8)

The lattice, the contract types, and the caching schema include **every dimension from day one**
(`Unique` flag, escape, confinement, duplication) — the contract never migrates. Implementation
stages:

- **Increment I — borrow inference (the read path).** Q1 + Q2 + Q3: `Borrowed`/`Owned` vectors on
  statically-resolved calls; borrow-through-projection; escape → stack/region; confinement →
  non-atomic RC; **the §3.1(a) hand-declared primitive fact table** (required — the leaves'
  ground truth, without which the analysis infers almost nothing). Subsumes capture-by-borrow
  and `borrowed_vars` as inferred cases (§8.2). Cheaper analysis, no dynamic checks, no
  representation change. Ships only with the §5 machinery (§5.7).
- **Increment II — uniqueness → mutable borrow → reuse (the write path), + the `Copy` mechanism.**
  Q4: static uniqueness where provable, **dynamic rc==1 reuse tokens** as the general
  discriminator (R4), drop-guided in-place reuse generalising Vec-COW mutate-in-place; Q5:
  value-representation flattening (§6.3). Mode-in-mono-key explored here with data (§4.3),
  not before.

**I is subsumed, not discarded, by II and by `--release`:** I's outputs remain consumed unchanged
(II adds queries and mechanisms; reuse tokens stay off the ABI per §3.5); `--release` consumes the
same boundary facts through the same `MonoExpr` input and layers its engine-side mechanisms
(M-LLVM/M1–M3) on top. The absent-summary-⇒-Decision-24 default extends the same property
downward: increment I is itself a strict refinement of the as-built convention.

---

## §8. Composition and subsumption (reconciled interactions)

### 8.1 Persistent data structures (Axis 2) — composed, not competing

HAMT/RRB persistent structures remain the **shared-case** copy cure (O(log n) copy without
uniqueness) and are a separate representation/stdlib axis, NOT scheduled by increments I/II. They
compose: **borrow the shared spine, mutate the unique delta in place** —
persistent-structures-plus-transients with the transient *inferred* (Q4 supplies the uniqueness
that makes a delta mutable). The write-side materialization target for shared values is
persistent-delta where the structure is persistent, deep-clone where it is not.
Representation-flip-below-N (small collections stay flat vectors — north-star #1) is noted as a
stdlib/backend co-design question for that axis's own design pass.

### 8.2 Capture-by-borrow and `borrowed_vars` — subsumed via the escape query (R6)

The S99 §5.5.2 spark-capture borrow is the special case "capture only-read + parent provably
outlives ⇒ `Borrowed`", now derived by Q1/Q2 instead of pinned structurally; the §5.5 match-arm
`borrowed_vars` rule is the intra-function seed of borrow-through-projection (§4.4). **The
ParBind-across-suspension caveat dissolves by classification:** a capture flowing into a
trampoline-deferred continuation crosses a suspension edge (§2.2 rule 4) ⇒ `Escapes` ⇒ the retain
stays — never by widening the borrow. The `LaunchContinue` exclusion likewise falls out (detached
= suspension edge by construction, and stays representationally visible per Principle 20). The
existing UAF/exclusion guards (`ring2-rc.md` §5.5.2.6) carry forward as the regression fence for
exactly these inferred classifications (part 17).

### 8.3 The lenient-eval spark gate (`0459`) — fed, not blocked

The gate is scheduling; this analysis is memory. The gate's missing allocation/RC-density axis
(`effect-concurrency.md` §3.1 static layer) becomes **derivable from the analysis outputs**: a
branch whose materializations are borrow-/reuse-/Copy-served is cheap ⇒ admit; an
allocation-dominated branch under shared data stays declined. `0459` remains deferred-Phase-H with
this design as its input; nothing here pulls it forward or blocks on it. As the memory model
removes contention at the source, the gate's conservative declines convert to admits — the
composition already pinned in `effect-concurrency.md` §3.1(c).

---

## §9. Acceptance framing for `/qa` (the R8 principle — the plan itself is part 17–18)

The spine does not author the verification plan; it pins the **staged-acceptance principle** the
plan inherits: **F1–F4 targets are stated per increment, and each increment is graded against its
own bar, not the composed end-state's** — (i) increment I alone (read-path: rc_inc collapse on
projection-heavy reads; alloc-count drop from stack/region; user-time contention delta on F2);
(ii) I+II (write-path: reuse hit-rate on copy-per-guess; F2/F4 wall vs serial); (iii) the composed
end-state (persistent DS and/or Copy-flattening in play — the only configuration honestly
comparable to the north-star's "slight per-core discount"). Every stage keeps the two-sided bar:
scale dividends AND unnoticeable small-case overhead (a serial/1-worker non-regression lane on
the same fixtures). Metrics discipline carries from S99: RC-op + alloc counts
(`CRANELISP_RC_STATS`), wall+user+sys separately, release-tier attribution, per-rep spread against
false greens. Mandatory guards: the analysis-off differential oracle (§6.2), the ASan/UAF lane on
the R6 suspension-escape site, and the S98-bug-#2 class (any "skip the inc" emission gets a
starved-inc regression fence). The §3.1 triage candidate is **RESOLVED — real defect**: `/qa`
verified value-use of the vec query family SIGSEGVs through NULL GOT slots in both `--run` and
the REPL (4 failing-not-ignored repros + 1 green `vec-len` control,
`tests/vec_query_value_use.rs`, ledgered; owner `/backend`; no FIXME filed — the tests are the
record and trigger per `memory/feedback_no_fixme_with_failing_test.md`). The §3.1 sequencing
pin applies: fix before the sibling lands and before the R2 wrapper reaches primitives.

---

## §10. Open questions routed to the per-crate proposals

**To `design/typecheck/ownership-inference.md` (parts 6–11):**

1. Summary/fixpoint representation + iteration strategy; cost budget for the cluster fixpoint in
   the interactive path (the §5.4 slow path shares it).
2. Borrow-through-projection: the precise composition rule, interaction with last-use, projection
   out of `Owned` aggregates (§4.4).
3. Per-cell confinement join (§2.3, now op-wise): how per-site facts aggregate to a cell's
   RC-op atomicity decision across all reachable sites — carrying the two new proof
   obligations: provability of "no RC ops on other threads" for the joined-spark borrow shape
   (the S99 F2 cell), and the sync-edge happens-before reasoning behind `Transferred` —
   decide whether `Transferred` is adopted as a lattice point or collapsed to `Crossing` for
   increment I.
4. Generic-instantiation summary dedup at mint sites (§4.2).
5. The static-uniqueness subset worth proving (vs deferring everything to the dynamic check), and
   the mode-in-key data question (part 11, increment II). **Framing note (user-originated
   design discussion, 2026-07-02): part 11 evaluates THREE named write-path mechanisms**, under
   the two-axis separation below.
   - **(a) The default (R4): one body + dynamic rc==1 check.** For bulk ops an entry check
     selects the in-place vs fresh path — one branch per *call*, not per element.
     `vec-set-copy` is the in-tree precedent, and it already makes a set-loop `map` adaptive:
     zero copies when unique, exactly one when shared.
   - **(b) Uniqueness-specialized additional monomorphisation behind a STATIC proof:** a
     branch-free, allocation-free body — and, the deeper criterion, a RESULT that is also
     provably unique, so proofs **chain across call boundaries** (`(map inc (map dec v))`
     fuses to two in-place passes). Static proof is what makes uniqueness *compose*; the
     dynamic check re-establishes uniqueness but cannot propagate it. Cost: code bloat /
     mono-key expansion — explored with data in increment II per §4.3. **The success metric
     for static proving is proof CHAINING, not per-site wins.**
   - **(c) Callee-demands-unique (caller copies if required): REJECTED in pure form** —
     unconditional copy at unprovable sites is a pessimization vs (a), and it puts uniqueness
     into the ABI contra R4. Its refined form (call-site `rc==1 ? pass : copy-then-pass`) is
     just (a) with the check hoisted to the caller, and a static proof elides the check —
     coherent, and the same family as §4.3's caller-side adaptation.

   **The two-axis separation (binding on part 11): ELIGIBILITY is static; PERMISSION is
   dynamic-or-proven.** Eligibility = layout compatibility per instantiation, decided at mono
   (`inc : Int→Int` is in-place-eligible; `Int→String` never is); permission = uniqueness per
   call. And R2 does **not** block HOFs like `map` from carrying a moded vec param: R2 pins
   modes off closure-*valued* call sites, and `map` called by name is statically resolved —
   only its *closure argument* rides Decision-24.
6. HOF/closure-conversion mechanics under R2: how a function both statically-called (moded) and
   closure-converted (Decision-24) is served — dual entry, erased wrapper, or join-to-Owned
   (§3.1; the primitives' inline-plus-GOT-wrapper dual path is the in-tree precedent, with a
   named as-built gap). Coordinate with backend part 12.

**To `design/backend/ownership-codegen.md` (parts 12–16):**

7. Borrow-elision emission (caller inc / callee dec elision keyed off the vector) + the
   R2/closure-entry answer's codegen half.
8. Stack/region mechanics for `NoEscape` (frame slots vs region arena; interaction with
   `ParBind`-arm lifetimes = M7's shape, landed on the shared tier per §3.4).
9. Non-atomic RC emission for `Confined` (the `CRANELISP_NONATOMIC_RC` probe generalised, now
   soundness-gated by Q3 instead of documented-unsound).
10. Reuse tokens / drop-guided reuse — intra-function only (§3.5); generalising Vec-COW
    mutate-in-place; the dynamic rc==1 check's cost model.
11. **The R5 value-representation flattening design** (§6.3) — `HeapCategory` arm, ABI/size
    bounds, Vec-of-values layout, cache/`--link` parity, trace descriptors; the eligibility
    predicate is single-sourced in `cranelisp-types` per the §6.3 ruling (FIXME 0468 resolved).
12. The R3 machinery's backend half: the trap-stub mechanism for broken callers (§5.5 — stub
    args-untouched raise semantics + the RC-mid-panic caveat), fresh-slot allocation + frozen-slot
    retention (§5.6 — the `Code::Jit` retention rule extending Decision 31 Scenario 2) — jointly
    with `/int` (session transaction orchestration, the reverse-index lifecycle, diagnostics UX,
    file-watcher interplay), whose design home is `design/int/`.
13. The analysis-off toggle's exact scope (one master switch; byte-identical-off proof
    obligation — §6.2).
14. The §3.1(b) extern calling-convention refinement (optional): borrowed-convention sibling
    symbols for extern primitives — dual-symbol pattern, consuming export untouched
    (byte-identity for the analysis-off oracle preserved), summary+toggle-gated targeting;
    bring when-worth-it data (the dominant S99 term is cured by R5/Q4, not by convention).
    Increment I ships the pattern + one template instance, `str-len` (backend §9.2; `vec-len`
    is not a candidate — inline-lowered at static sites, no pair to elide).

**To `/qa` (parts 17–18):** the plan per §9, including the differential harness shape and the
per-increment F1–F4 target numbers.

---

## §11. Manifestation sites when implemented (forward ledger)

- `cranelisp-types`: `Mode`/`ModeSummary` (enriched shape per §3.3: `result: ResultMode` +
  advisory `param_flow`/`spark_ops`/`result_unique`) + `MonoDefnVariant.mode_summary` +
  `MonoExpr` site facts (incl. projection provenance) + callable-`DefKind` summary field +
  the per-entry value-use mark + the `DefKind::Primitive` declared-fact payload (§3.3) —
  `/arch`-authored, first implementation sprint, with `public-api.txt` + `interfaces.md` +
  BC §7 + `CACHE_SCHEMA_VERSION` cascade.
- `cranelisp-types` (R5 increment, separately): the single-sourced Copy/value-layout predicate
  beside `HeapHeader` + its size-bound constant (§6.3 ruling) — lands with the R5-increment
  `/arch` carrier change-set, not before.
- `bounded-contexts.md` §2 (typecheck: the inference pass joins the bounded context) and §3
  (backend: the five mechanisms + oracle toggle) — with the implementing sprints.
- `release-llvm-backend.md` §7/§8.3/§13 — amended NOW (S100 Phase 3) per the inversion ruling.
- `effect-concurrency.md` §3.1 — forward-pointer added NOW (the (b)-cure's designed home).
- `ring2-rc.md` §3 (Decision-24 prose gains the conservative-point framing) — FIXME filed to
  `/design`(backend), owning-skill edit.
- `repl/spec.md` — the §5.5 cascade-reporting/broken-symbol UX needs a normative home when the
  machinery is scoped for implementation; file to `/repl` at that sprint, not now.
- Sequence diagrams: a redefinition-transaction diagram (REPL turn × scheduler × GOT slot
  allocation/freeze × cascade report) joins `sequences/` when the machinery's facade signatures
  exist (nothing to draw against until the `/int`/backend proposals name the calls).

## §12. Phase-3 exit gate — interface-set confirmation (2026-07-03, `/arch`)

**Verdict: PASS-with-notes.** The four-document set — this spine, the typecheck proposal
(parts 6–11), the backend proposal (parts 12–16), and the `/qa` verification plan (parts
17–18) — is complete and mutually coherent for the two implementing increments. Findings:

1. **Interface-set completeness.** Every cross-crate seam the increments need is specified:
   typecheck→backend (the §3.3 carrier — now including the result mode, the advisory
   analysis-fact half, projection provenance, and the value-use mark, folded from FIXME 0467);
   typecheck→backend coordination for the R2 wrapper (typecheck §8.4 states what the backend
   consumes and what it owes back; backend §3.4/§3.5 answers each owed item — the adaptation
   algebra, `__d24wrap_{fq}_{slot}__` naming, curry composition); backend→`/int` (backend §8.3:
   `compile_to_module` unchanged, `compile_trap_stub` NEW, `store_slot`/`allocate_got_slot`
   existing); primitives→typecheck (the §3.1(a) declared facts riding `DefKind::Primitive`
   entries, typecheck §9). **The one seam deliberately not yet designed** is the R3 session
   transaction's orchestration interior (reverse-index lifecycle, cascade reporting, frozen-
   `Code` pool residency) — its design home is `design/int/` (a later fire, §10 item 12), its
   consuming interface is pinned (backend §8.3), and it MUST be scheduled at the machinery
   sprint per §5.7. Deferred-with-pinned-interface, not unspecified.
2. **Contract coherence.** No contradictions found. Verified pairs: `Transferred`
   collapse-at-emission (typecheck §5.4) ↔ backend §5.3 (promotion arrives as more
   `Some(true)` verdicts, zero emission change); R2 moded-body-on-the-slot + lazy wrapper
   (typecheck §8.2) ↔ backend §3.5 slot-keyed wrapper naming, which composes correctly with
   §5.6 ABI-epoch slot versioning (slot identity = ABI identity ⇒ fresh slot ⇒ fresh wrapper
   name, stale closures keep old-world consistency transitively); `result_unique` chaining
   (typecheck §7.2, advisory, emitted false in I) ↔ backend §6.2 check-elision — off the ABI
   per §3.5, both sides; `borrowed_vars` as the callee-side carrier (backend §3.2) ↔ the §8.2
   subsumption; per-site non-atomic re-gating of the existing emission arms (backend §5) ↔
   typecheck §5's op-wise per-cell join, with the backend performing no strand reasoning
   (narrowness counterweight held on both sides).
3. **QA-plan routing confirmed** — the plan's four flagged gaps are increment-sprint
   obligations, not S100 gaps: (i) CLIF-dump determinism (hook H1) is decided at increment-I
   drafting and is `/backend`'s implementing-change-set obligation; (ii) the L-B1 golden
   capture MUST be the first-scheduled item of the increment-I sprint (baseline commit before
   any mechanism lands) — `/sprint` carries this ordering into the roadmap at close; (iii)
   trap-stub UX wording stays substring-anchored until the `/repl` normative half lands at the
   machinery sprint (§11 already routes it); (iv) observability hooks H2–H5 land in the
   implementing change-sets per `tests/CLAUDE.md` §Diagnostic Requirements — several
   acceptance gates (I-G3, I-G7, II-G2, L-D2, L-D5) are unmeasurable without them, so they are
   in-increment deliverables, never follow-ups.
4. **Known defect accommodated.** The NULL-GOT-slot fn-as-value SIGSEGV
   (`tests/vec_query_value_use.rs`, owner `/backend`) is pinned in §3.1/§9 with its sequencing
   constraint: the fix precedes the §3.1(b) `str-len` sibling (same registration seam) and the
   R2 wrapper's reach into primitives (backend §12.7). The §5.7 ordering (machinery →
   increment I) is unaffected; the pin binds within increment I's internal sequencing.

**Notes carried to `/sprint` for close:** the `design/int/` R3-orchestration design fire must
be scheduled at (or before) the machinery sprint; the golden-capture-first ordering inside
increment I; the F2v fixture decision is worth user ratification (qa plan §1.1); root
`CLAUDE.md` §Testing's intentional-failing count (16→20) needs its owner's update at close.

## Next skills

(Parts 6–18 are delivered: `design/typecheck/ownership-inference.md`,
`design/backend/ownership-codegen.md`, `tests/plan/s100-ownership-verification.md` — exit gate
§12 passed 2026-07-03.)

- `/sprint` — sequence the implementation roadmap at close: machinery (§5.7, incl. the
  `design/int/` R3-orchestration design fire) → increment I (golden capture first; NULL-slot
  fix before sibling/wrapper reach) → increment II; `--release` stays gated behind the settled
  memory model. Carry the §12 close notes (F2v ratification; intentional-failing count).
- `/design` (int, at the machinery sprint) — consume backend §8.3 and design the session
  transaction in `design/int/`; `/repl` receives the cascade-report/broken-symbol UX spec half
  at the same sprint (§11).
- `/qa` + per-crate `/dev` triads — QA-first drafting lists per implementing sprint are in the
  verification plan §6.
