# Session transaction — dependent recompilation + ABI-epoch slot versioning (R3 machinery, int half)

> **Status: DESIGN (S101 Phase 3); implemented S101 Wave 4; amended S102 Phase 3; T1 full-cure
> promoted to implementation-ready S103 Phase 3** (the §9.1.1 downgrade `stale:` section — interim
> T1 cure, `repl/spec.md` §18.1.1 — and the §10 T1 full-cure end-of-turn mechanics + preconditions;
> companion doc `design/int/s102-defect-wave.md`). **S103 Phase-3 amendment (FIXME 0507, /design
> src/): the §10 T1 full-cure change-sets are now implementation-ready** — its S102-preconditions
> (regen fidelity D1/D2, the 0489 prompt floor, D3/0487 env) landed at S102, so §10 T1 lists the
> dependency-ordered change-sets, the F2 slot-refined trigger, the F5a macro-target handling, the
> two coherent-stale pins to flip, and the F3 0491-exclusion resolution (macro-clause staleness).
> Three deliberate as-built
> divergences, upheld at change-set review (FIXME 0477, drained by this amendment), are
> recorded in place: the §10 T1 module-grain downgrade, the §7.3 deleted-symbol leg
> (recorded gap), and the §9.2 rendering seam (`broken_status_line`, not
> `SymbolDescription`). This is the seam the S100 exit gate
> deferred-with-pinned-interface (`design/arch/ownership-inference.md` §12): the dev-session
> redefinition transaction of spine §5.3–§5.7, designed at implementation grain for `src/`.
> The consuming interface is **pinned at `design/backend/ownership-codegen.md` §8.3's three
> calls** (`compile_to_module` — existing; `compile_trap_stub` — new; `got().store_slot` /
> `allocate_got_slot` — existing). This doc consumes that interface; it does not redesign it.
>
> Scope authority: spine §5 (R3 ruling, user-directed 2026-07-02). Acceptance authority:
> `tests/plan/s100-ownership-verification.md` §2.1 (stage M) + §3.6 (lanes L-R1–L-R5) +
> L-D1. Master design: `design/int/int.md` (§8.6 cites this doc).
>
> **Stage-M frame:** no ownership analysis exists yet. The ABI comparand is the **type scheme
> only**; the machinery is designed as a general signature-coherence subsystem (it cures the
> latent type-changing-redefinition hole that exists today — spine §5.2) with named seams
> (§2.4, §3.5) where increment I's mode vectors slot in without restructuring.

---

## §1. Actors and functions first (Principle 21)

Spine §5.3 names the actors at architecture grain. This section extends them to
implementation grain — each actor, the functions it performs in the transaction, and the
as-built anchor it grows from.

| Actor | Function in the transaction | As-built anchor |
|---|---|---|
| **The REPL turn (eval thread)** | Sole driver. Submits the redefinition, runs the whole transaction synchronously inside the turn (one prompt → one submission → wait → display), prints the cascade report. Never delegates the entry or the closure to pool workers (Invariant SW — the entry module never enters `TypecheckBlocked`). | `eval.rs::process_form_cluster` (`eval.rs:216`), `codegen_and_execute` |
| **Typecheck (via cluster staging)** | Produces the redefined symbol's new scheme (increment I: + `ModeSummary`); records the forward call-graph edges (`Def.callees`) — after the §3.2 enrichment. Pins the prior slot into the staged variant (`redef_slots`, Pass-1). | `check_forms` staging; `program.rs::extract_call_graph_edges` (`program.rs:690`) |
| **The commit gate** | The staging→live commit's redefinition branch. Gains the classification (§2): computes the ABI-surface diff, applies the slot policy (reuse vs fresh+freeze), moves superseded `Code` into retention. **The single slot-policy authority** (§7.1). | `worker.rs` `finalize_cluster` commit loop (`worker.rs:421–470`) |
| **The reverse dependency index** | Derived on demand from `Def.callees` across the live tables (§3.3) — who-calls-whom⁻¹. Never a second authored store (Principle 7). | new, `src/redefine.rs`; feed = `ModuleEntry::Def.callees` (`module.rs:725`) |
| **The transaction executor** | Affected-set closure, SCC condensation, reverse-topo walk, per-symbol re-typecheck + recompile, BROKEN marking (§4–§5). | new, `src/redefine.rs` |
| **The recompile executor** | Per-SCC JIT recompilation of affected symbols. | `worker::inline_jit_codegen_for_names` (`worker.rs:916`) → `cranelisp_backend::compile_to_module` (pinned call 1) |
| **The trap-stub compiler** | Emits the per-symbol ~5-instruction stub over `runtime/panic` (backend §8.1). | `cranelisp_backend::compile_trap_stub(msg_ptr, msg_len) -> Result<(ptr, Code), _>` (pinned call 2) |
| **The GOT** | The commit substrate: per-slot atomic writes; append-only monotone allocation. ABI identity is encoded in slot identity (spine §5.6). | `SymbolTable::allocate_got_slot`, `got.store_slot` (pinned call 3); `repoint_callable_slot` (`worker.rs:480`) |
| **The retention pool** | Session-lifetime, append-only storage pairing every retained `Code` handle with its trap-message buffer (§6). The `kept_dlls` precedent (`session_v4.rs:290`). | new field `SharedState.retained_code` |
| **The broken registry** | Symbol-level BROKEN state + provenance for display and retry (§5). | new field `SharedState.broken` |
| **The report + introspection surfaces** | The turn's cascade report; `/info`/`/sig` broken-status answers (§9). | `redefine.rs::broken_status_line` (`redefine.rs:1044`), rendered at `handle_sig` / `handle_info` / bare lookup (`repl.rs:711/:1275/:2159`) — §9.2 as-built |
| **The persistence writers** | Faithful `.meta`/`.o` writes (slot numbers load-bearing), regenerated backing file, cache-write poisoning for broken modules (§8). | `lifecycle.rs::regenerate_backing_file` (`lifecycle.rs:936`), nice-worker persist |
| **The heap and the runtime cadence** | The actors recompilation **cannot** reach: heap closures embedding direct code pointers, suspended IO-tree continuations, detached strands, in-flight frames. §7 (frozen world) exists because of them. | — |

The function flow between them, one turn:

```
user submits (defn f …)             [redefinition of f]
  → cluster staging typecheck       [new scheme; edges; redef_slot pin]
  → COMMIT GATE: AbiSurface diff    [§2]
      = AbiPreserving → reuse slot, carry code, codegen patches in place — DONE (today's path; L-D1)
      = AbiChanging   → fresh slot for f; freeze old slot (retention pool); codegen f
  → TRANSACTION (eval thread, synchronous)                                 [§4]
      reverse index (on demand) → affected closure → SCCs, reverse-topo
      per SCC: re-typecheck from stored sexps
        ok  → commit through the SAME gate (per-symbol slot policy) → recompile (inline_jit_codegen_for_names)
        err → BROKEN: entry retained, code → pool, slot patched in place to trap stub  [§5]
        slot-less member (constrained template): pass-through — callers visited
          unconditionally, whatever its own outcome                                    [§4.1]
  → REPORT: recompiled [...]; broken [...] (+ /info, /sig answer thereafter)           [§9]
  → regenerate_backing_file; persistence pins honoured                                 [§8]
```

---

## §2. Trigger classification — the summary-diff gate

### 2.1 Where it runs

The hook is the staging→live commit's redefinition branch (`worker.rs:421–470`). Today that
branch **unconditionally** reuses the prior live slot and carries the prior `code` forward;
typecheck's Pass-1 `redef_slots` pin means the staged slot already equals the reused slot.
The gate replaces "unconditionally reuse" with a three-way classification:

```rust
enum RedefKind {
    New,            // no prior live Def under this name — today's fresh-allocate path
    AbiPreserving,  // prior exists; ABI surface unchanged — today's reuse-and-patch path
    AbiChanging,    // prior exists; ABI surface changed — fresh slot + freeze (§7)
}
```

computed by `AbiSurface::of(&prior_entry) != AbiSurface::of(&staged_entry)`.

The gate runs at the commit **because the slot decision must be made before codegen embeds
slot indices** — a recompiled caller must embed `f`'s new slot, and `f`'s own codegen writes
into whichever slot the committed entry carries.

### 2.2 The comparand at stage M

`AbiSurface` is the **alpha-canonical rendering of the entry's fully-qualified type scheme**
(arity is implicit in the scheme). Raw `Scheme` structs must NOT be compared directly — two
checks of the same source produce different type-variable ids; the canonicalising renderer
the REPL already uses for scheme display (normalized var names, FQ type names) is the
comparison key. `AbiSurface::of` is one pure function in `src/redefine.rs` — the seam.

What is **not** in the comparand: docstrings, param names, visibility, `seq`, the body.
A body-only edit, a docstring edit, a param-rename — all `AbiPreserving`.

Which entries classify: **concrete callable `UserFn` Defs** (`DefKind::UserFn { fn_state:
Concrete }`). Anything else that gets redefined (generic/constrained base, `Overloaded`
base, `Macro`, `Constructor`/deftype, trait decl/impl) is outside per-symbol precision at
stage M and classifies `AbiPreserving` with `per_symbol: false` — today's reuse-and-patch,
no transaction (`src/redefine.rs::classify_redefinition`, the `!per_symbol` arm; see §10 T1
for the as-built downgrade from the originally-designed module-grain reload and the named
residue). That routing governs the
**redefined target** only: a slot-less entry reached mid-walk as a closure **member**
(e.g. a constrained template between the target and its mono-minting callers) stays at
per-symbol grain under §4.1's pass-through rule — it does not degrade the transaction to
module grain.

### 2.3 The L-D1 pin — body-only stays at today's cost

The fast path is **today's path plus exactly one `AbiSurface` computation-and-compare** per
redefined symbol. Everything else — reverse-index derivation, closure computation, SCC
ordering — is gated behind `AbiChanging` and never runs on a body-only turn. This is also
why the reverse index is derived on demand (§3.3) rather than incrementally maintained:
incremental maintenance would tax **every** registration, including body-only turns.

Late binding is preserved verbatim on this path: reuse slot → in-place `store_slot` patch →
stale closures and in-flight strands pick up the new body at their next call (L-R2's
ABI-preserving leg).

### 2.4 The increment-I seam

When `ModeSummary` lands (spine §3.3), `AbiSurface` gains the **ABI-bearing half only**:
`param_modes: Vec<Mode>` + `result: ResultMode`. The advisory trio (`param_flow`,
`spark_ops`, `result_unique`) stays out of the comparand by construction — ignoring it is
monotone-sound, so it cannot be ABI. The change is confined to the `AbiSurface::of`
constructor and its derived `PartialEq`; the gate, the transaction, and the slot policy do
not restructure. Note the stage-M/increment-I interplay with `CRANELISP_NO_OWNERSHIP`:
none — the stage-M comparand is analysis-independent, so the transaction is live regardless
of the toggle (and with the toggle off in increment I, summaries are absent = Decision 24 =
mode fields compare equal, degrading exactly to the stage-M gate).

---

## §3. The reverse dependency index

### 3.1 Fire-checklist item (ii) — what `Def.callees` actually records (source evidence)

The spine (§5.3) treats `ModuleEntry::Def.callees` as the persisted forward edge set. The
S101 fire checklist asks whether it records fn-as-value references. **Verified against
source, the answer is worse: it records neither fn-as-value references nor plain direct
calls to ordinary user functions.**

- Edges are extracted **exclusively** from `method_resolutions` — `extract_call_graph_edges`
  iterates `ResolvedCall` values (`program.rs:690–706`) and `resolved_call_to_fqsymbol`
  (`program.rs:710–752`) maps only `TraitMethod`, `SigDispatch`, and `AutoCurry` to edges
  (`BuiltinFn` deliberately skipped; the `#[non_exhaustive]` default arm yields no edge).
- A **plain fully-applied call to a single-sig concrete user fn inserts no `ResolvedCall`**:
  `infer_apply`'s resolution block (`infer.rs:585–604`) tries trait-method resolution, then
  primitive-name resolution — an ordinary user fn matches neither, so nothing is recorded
  and no edge is extracted. `(defn g [] (f 1))` produces an **empty** `g.callees` today.
- **Value-position references resolve only for trait methods**:
  `resolve_value_position_trait_methods` gates on `is_trait_method_with_state`
  (`infer.rs:824–856`) — an ordinary fn passed to a HOF keeps `resolved_call: None`. The
  FIXME-0374 collector confirms it in as-built prose: fn-value args "are not callees (so the
  call-site collectors above miss them)" (`program.rs:3217–3223`).

Consequence: the as-built graph cannot feed the affected-set closure for the **common
case**. An L-R4 fixture (`g` plainly calling `f`; `f`'s param type changes) would find zero
callers and silently leave `g` unsound — the exact hole the sprint exists to cure. And the
module-level fallback alone cannot substitute: L-R3's negative half ("the recompiled set
names exactly the static callers, and NOT unrelated fns") is unsatisfiable at module grain.

### 3.2 Ruling — typecheck-side edge-extraction widening (FIXME 0470, load-bearing for S101)

The edge set is enriched **where resolution knowledge lives — in typecheck** (filed as
`design/arch/fixmes/0470-typecheck-callees-static-reference-edges.md`, `target:
/typecheck`): record an edge for **every statically-resolved reference from a checked body
to a module-resident callable `Def`** — both call-position applies and value-position `Var`
references — into `call_graph_edges`, flowing through the existing
`write_callees_to_module_entries` sink unchanged.

- **Why not an int-side AST walk:** deriving edges in `src/` from the stored annotated
  `ast` would require re-implementing scope-aware name resolution (params/let shadowing,
  import chain-follow, module-locality — Principle 17) outside the crate that owns it —
  a behavioural duplicate of typecheck's resolution (Principle 7). The annotated AST does
  not carry resolved targets for plain user-fn references (that is the gap itself).
- **No `cranelisp-types` change at stage M.** `callees: Vec<FQSymbol>` keeps its shape;
  value-references and call-references are recorded **uniformly**. This is sound at stage M
  because every ABI change is a type change, and type changes break value-uses too (spine
  §5.4 step 3) — the value/call discrimination only matters in increment I (mode-only
  changes exclude value edges) and lands as a carrier enrichment in the same
  implementing change-set as `ModeSummary` (which already opens `cranelisp-types`).
  Until then, treating value edges as call edges only over-approximates (recompiles a
  value-user on a mode-only change) — monotone-sound.
- **`CACHE_SCHEMA_VERSION` bump rides the enrichment.** A cache-restored module carrying
  pre-enrichment sparse `callees` would silently starve the closure; the bump invalidates
  old caches wholesale (the spine §5.1 discipline), so every live table's edges are
  extraction-current by construction.
- Edges already point at **mangled names** for `SigDispatch`/mono variants and trait-impl
  methods — the reverse index inherits that grain for free.

### 3.3 Derivation — on demand, at transaction time

The reverse index is **derived by a scan of the live tables' `Def.callees` at the moment an
`AbiChanging` classification fires**, producing `HashMap<FQSymbol, Vec<FQSymbol>>`
(callee → callers) over all registered modules. Ruling rationale:

1. **L-D1** — zero cost on the fast path (§2.3). Incremental maintenance is paid on every
   registration; on-demand is paid only on the slow path it serves.
2. **No staleness invariants** — module reloads, cache restores, staging commits, and BROKEN
   transitions would each need an invalidation protocol for a maintained index. A scan is
   correct by construction against whatever the tables hold now.
3. **Scale** — a dev session holds 10²–10³ Defs; the scan is microseconds against the
   recompiles it precedes (Principle 6 — complexity has a budget).

Spine §5.3's "maintained incrementally" is realised as a **named upgrade option for
increment I** if the §4.1 ownership fixpoint (which walks the same edges repeatedly) makes
scanning measurably hot: the `ReverseIndex` type's surface (`build(tables)`,
`callers_of(&fq)`) does not change, only its refresh policy. Derived-never-authored
(Principle 7) is satisfied maximally by on-demand derivation.

---

## §4. The affected-set closure and recompile ordering

### 4.1 Closure and ordering

On `AbiChanging` commit of `f`:

1. **Potential closure.** Transitive closure over reverse edges from `f` (statically-resolved
   edges only — that is all the enriched `callees` contains). Members are FQSymbols across
   all modules; cross-module edges participate identically (spine §5.4 step 4).
2. **SCC condensation** of the affected subgraph (forward edges restricted to the closure).
   A mutually-recursive group is one SCC and re-typechecks as **one cluster** — the existing
   two-pass cluster machinery is the fixpoint for recursive groups.
3. **Reverse-topological walk** (callees before callers) over the condensation. Per SCC:
   - **Skip test:** if none of the SCC's in-closure callees **propagates**, the SCC is
     **not** re-typechecked and does not join the recompiled set. A **slotted** callee
     propagates iff it was re-typechecked and classified `AbiChanging`; slotted
     `AbiPreserving` and slotted BROKEN callees do not (§5). A **slot-less** callee
     propagates **unconditionally** (pass-through, below). The skip test is what makes the
     reported set exact (L-R3 positive + negative) and gives single-pass termination: the
     walk visits each SCC once, after all its callees have settled.
   - Otherwise **re-typecheck** the SCC (§4.2); on success, **commit through the §2 gate**
     (each member's own ABI diff decides in-place patch vs fresh-slot-and-propagate) and
     **recompile** via `inline_jit_codegen_for_names(module, members)`; on failure, mark
     BROKEN (§5) and — for slotted members — do **not** propagate (a broken symbol's ABI
     did not change — spine §5.5 transitivity, which reads at slotted grain: its rationale
     presupposes an ABI surface the member owns).
   - **Slot-less pass-through (the FIXME-0473 ruling).** The skip test and the BROKEN
     no-propagation rule evaluate a member's **own** ABI/slot status — meaningful only for
     members **with codegen artifacts**. A **slot-less member** — constrained/generic
     template `UserFn`, `Overloaded` base: any codegen-less entry the enriched edges
     reach — owns no slot and no code; the artifact that embeds a changed callee's old
     slot is the **mono instance in each caller's module** (`t$Int`, minted by caller
     `c`), which only the *caller's* re-typecheck can re-mint. So a slot-less member is
     still re-typechecked in its SCC position (its scheme and edges must stay
     world-coherent), but its own classification **never gates the walk** — its callers
     are visited unconditionally, whatever the outcome:
     - **Re-checks green** (scheme changed or unchanged — both): callers re-typecheck;
       each re-minted mono instance is concrete and commits through the §2 gate on its
       **own** ABI diff (typically `AbiPreserving` → in-place slot patch, so existing
       captures of the instance late-bind to the new-world body).
     - **Goes BROKEN**: registry record only — there is no code to retain and no slot to
       trap-patch (§5.1). Propagation continues: callers re-typecheck, fail on the same
       instantiation, and go BROKEN **as themselves** — slotted, so §5.1's trap patch
       lands there. Breakage surfaces at the nearest slotted ancestors instead of
       vanishing.

     **How the walk knows a member is slot-less:** the live entry's
     `ModuleEntry::callable_got_slot() -> Option<usize>` accessor (`module.rs:1303`) —
     `None` ⇔ slot-less. The S83 reshape (Decision 35 amendment, Principle 20) moved
     `got_slot` onto the four callable `DefKind` variants, making the kind⇔slot pairing
     structural; one existing accessor is the whole discriminator — no new field, no new
     flag, nothing for `/dev` to maintain in parallel with the kind.

Because commits happen callee-first, a recompiled caller's codegen reads the callee's
**new** slot off the committed entry — the ordering is what makes the embedded slot indices
land right, with no second bookkeeping.

**Worked — the two constructible stoppers (FIXME 0473) through the amended rule.** Setup:
concrete `c` calls constrained template `t`; `t` calls `f`; `c`'s module holds the minted
mono instance `t$Int` embedding `f`'s slot. `f` is redefined `AbiChanging`; the closure is
`{t, c}` (mono entries are deliberately edge-less; the chain `f → t → c` is represented
via the template — the Wave-2b feed verification).

- **(A) Absorbed change.** `f : (Fn [Int] Int)` → `(Fn [a] Int)`; `t`'s body still checks
  and `t`'s scheme is unchanged. *Without* the rule: `t` classifies `AbiPreserving` → the
  skip test stops the walk before `c` → `t$Int` stays silently pinned to `f`'s frozen old
  slot. *With* it: `t` is slot-less (`callable_got_slot()` = `None`) → pass-through → `c`
  re-typechecks green → its recompile re-mints `t$Int` against new `f` (new slot);
  `t$Int`'s own gate diff is `AbiPreserving` (same instance scheme) → its slot patched in
  place → every existing reference — `c`'s code, wrapper closures, curried partials —
  late-binds to the new-world instance. `c`'s own surface is unchanged → `AbiPreserving`,
  in-place patch; the walk ends at `c` (a slotted `AbiPreserving` member does not
  propagate). Report: `{t, c}` per §9.1's definition (members re-typechecked green; `t`
  regenerates no artifact of its own) — L-R3-exact, no unrelated symbol visited.
- **(B) Template goes BROKEN.** `f`'s new signature fails `t`'s body. *Without* the rule:
  BROKEN no-propagation stops the walk AND §5.1's trap-patch has no slot to land on —
  runtime paths through `t$Int` keep executing old-world code with no trap: invisible
  breakage. *With* it: `t` takes a registry record only (`broken_by: f`, its own type
  error); pass-through → `c` re-typechecks, fails instantiating `t`, goes BROKEN as a
  slotted member — code → pool, `c`'s slot trap-patched, provenance depth-1 to the
  transaction target `f` (§5.2). Every live path to the breakage — direct calls of `c`,
  pre-break closures and partials over `c` — now traps with provenance. The stale `t$Int`
  entry keeps its old-world code: coherent by the frozen-world argument (§4.3 — it calls
  old `f` through the frozen slot), reachable only via stale captures (ordinary L-R2
  semantics), and re-minted/re-pointed when `c` recovers (§5.3).

**Ruling rationale — option 1 (pass-through) over option 2 (module-grain degrade).** The
rejected alternative routed callers of any slot-less member to the §10 conservative
fallback (one line of design). But constrained templates are pervasive in any polymorphic
cone — the degrade would make module grain the *common* case, unsatisfying L-R3's negative
half ("exactly the static callers, NOT unrelated fns") for precisely the workloads the
per-symbol design exists for. Option 1's recorded costs: one existing-accessor call per
member, and one extra propagation hop past unchanged templates — callers of a slot-less
member re-typecheck even when (rarely) no minted instance actually embeds the changed
callee, e.g. a value-position-only reference that never minted an instance. That
over-visit is monotone-sound, bounded by the template's recorded caller set, and typically
terminates immediately in `AbiPreserving` in-place patches.

### 4.2 Per-symbol re-typecheck mechanics

- **Input is the raw stored sexp** — `introspection[fq].sexp` (populated at every REPL
  definition, `process_form.rs:620`; the transaction is dev-session-only, where the
  introspection store exists — D1/D1b). Re-expansion from the raw sexp is deliberate:
  macros may themselves have changed, and retry-from-top is the established discipline.
- **Cache-restored modules** never populate introspection; rehydrate from the backing `.cl`
  first (the FIXME-0220 lazy-rehydration precedent,
  `save::rehydrate_userfn_introspection_from_source`, called at `lifecycle.rs:977–986`).
  If rehydration cannot recover the form → conservative trigger T2 (§10).
- **Module context:** each SCC re-typechecks with `current_module` = the members' home
  module (Principle 17 — resolution roots at home), through the standard staging path
  (expand → build → `check_forms` fresh staging → commit-on-Ok), exactly the
  `process_cluster_once` shape minus the scheduler: **no pool transitions**. Affected
  modules stay in their terminal pools; the transaction is eval-thread-synchronous and
  staging-based. This avoids every entry-module/pool hazard by construction (Invariant SW:
  the entry never enters `TypecheckBlocked`; here *nothing* does).

### 4.3 No quiesce, no patch window (the §5.6 argument, restated at this grain)

Between `f`'s commit and a caller `g`'s recompile there is no unsound window: `g`'s old
machine code embeds `f`'s **old** slot index, which is frozen and still points at old `f` —
a coherent old-ABI chain, transitively. Detached strands and heap closures executing during
the transaction resolve through frozen slots only. Each `store_slot` is independently
atomic and independently safe. The eval thread never needs to pause the trampoline, the
watcher, or the nice workers.

---

## §5. Cascading error management — BROKEN state

### 5.1 Marking

A closure member `g` that fails re-typecheck under `f`'s new signature:

- **Entry stays** in the table — scheme, docstring, `ast`, `param_names`, and crucially
  `callees` intact (edge retention is what lets the *reverse* recovery direction find `g`
  again). Its `code` is **moved to the retention pool** (§6) — not dropped, not `None`d.
- **Slot patched in place to a trap stub**: the session composes the provenance string
  (`"g is broken by the redefinition of f: <original type error>"` — exact wording is
  `/repl`'s normative item; L-R1 asserts substrings only), allocates it as a stable buffer
  in the retention-pool entry, calls `compile_trap_stub(ptr, len)`, stores the returned
  code pointer onto `g`'s **existing** slot, and retains the returned `Code` in the same
  pool entry. In-place is load-bearing: existing unrecompiled callers, wrapper closures,
  and curried partials all reach the trap through the slot they already embed (L-R1
  (a)/(b)/(c)); the stub never reads its argument registers, so one body is
  signature-safe for any arity (backend §8.1).
- **Registry record**: `SharedState.broken: DashMap<FQSymbol, BrokenInfo>` with
  `BrokenInfo { broken_by: FQSymbol, original_error: String, provenance: String }`.
  `DashMap` because the eval thread writes and the REPL display paths read via
  `&self.shared`; population is transaction-only (dev session), the field itself is
  unconditional session state like the scheduler's Failed pool.

**Slot-less members degenerate to the registry record alone** (§4.1 pass-through): a
constrained template that fails re-typecheck has no `code` to move to the pool and no slot
for the trap stub to land on — the marking is the `BrokenInfo` record only (entry, scheme,
edges retained as above). Trappability is delivered by propagation, not by patching: the
slotted callers that consequently fail take the full three-part marking above, each with
`broken_by` = the transaction target.

This generalises the S45 module-level machinery (`scheduler.reset_module` /
`reset_all_failed_modules` + embedded-original-error, `scheduler.rs:1726/:1750`) to symbol
level; the module-level machinery remains in place for the module-grain paths (§10).

### 5.2 Depth-1 provenance; no transitive breaking

`g` failed **before** producing a new ABI surface, so `g`'s callers were compiled against a
still-valid surface: they stay live and simply reach the trap through `g`'s slot at run
time. The closure walk treats a BROKEN **slotted** member as ABI-unchanged (skip test
§4.1) — no propagation (spine §5.5, which reads at slotted grain — its rationale
presupposes an ABI surface the member owns). A BROKEN **slot-less** member propagates
(§4.1 pass-through): the slotted callers that consequently fail are marked on their own
account, each with `broken_by` = the transaction target and its **own** type error —
provenance stays **depth-1 to the root** by construction, never chained through the
template (whether the rendered message additionally names the intermediate template is
`/repl`'s normative call, §9.1).

### 5.3 Recovery — both directions (L-R1(e))

Broken-ness is ordinary session state, not a sticky mode. Both exits are just the next
transaction:

- **Redefine `g` to match.** An ordinary redefinition of `g`; the §2 gate compares against
  `g`'s retained entry surface. Matching old ABI ⇒ `AbiPreserving` ⇒ in-place patch of `g`'s
  slot with real code; broken record removed. New ABI ⇒ `AbiChanging` ⇒ `g` gets a **fresh
  slot**; `g`'s **old slot stays permanently on the trap stub** — this is the fire-item-(i)
  scenario (§6.2) and why stub retention is session-lifetime.
- **Redefine `f` back.** The transaction on `f` re-runs; `g` is in `f`'s caller closure
  (edges retained at marking); `g` re-typechecks green, recompiles, its slot is re-pointed
  at real code in place (its ABI never changed); broken record removed.

Retry needs no saved state beyond what marking preserved: `g`'s sexp is still in
introspection (it was never redefined).

### 5.4 Interactions

- **Nice-worker `.o`/`.meta` persistence is poisoned for a module holding any BROKEN
  symbol** (§8.3) — a cache must never capture a trap stub as the module's compiled truth.
- **Test discovery / execution**: no special-casing. A broken test fn's wrapper reaches the
  trap; the trap **is** the clean failure with provenance (self-documenting-REPL principle).
- **RC-mid-panic caveat** (L-R1(f)): the caller's consuming incs are not released when the
  trap raises — one bounded leak per trap invocation, same class as every `runtime/panic`
  raise (backend §8.1). Documented tolerance, not asserted zero.

---

## §6. Retention — fire-checklist item (i) resolved

### 6.1 The pool

```rust
// SharedState (illustrative)
pub retained_code: Mutex<Vec<RetainedCode>>,   // append-only, session-lifetime

struct RetainedCode {
    fq: FQSymbol,               // whose supersession/trap this is (observability)
    module: ModuleFullPath,
    slot: usize,                // the frozen or trap-patched slot
    code: Code,                 // the retention handle (Arc<Jit> keeps pages mapped)
    trap_msg: Option<Box<str>>, // Some ⇔ code is a trap stub whose iconst'd address
                                // points into this buffer
}
```

One pool serves both retention classes: **frozen-slot supersession** (ABI-changing
redefinition: the prior entry's `Code` clone is pushed with `trap_msg: None` *before* the
commit replaces the entry) and **trap stubs** (`trap_msg: Some(buffer)` paired with the stub
`Code`). The `kept_dlls` precedent exactly (`session_v4.rs:290`): a `Mutex<Vec<…>>`, never
drained, documented leak-by-design, reclaimed wholesale at session end.

### 6.2 The lifetime pairing (fire item (i))

The trap stub bakes the message buffer's address and length as `iconst`s (backend §8.1) —
the buffer must live **exactly as long as any slot points at the stub**. §8.1's "retained
until the symbol recompiles" understates it: a broken symbol recovered with a **new** ABI
freezes its old slot pointing **permanently** at the trap stub (§5.3), so the stub — and
therefore the message — can be reachable until session end.

**Resolution: structural pairing + uniform session-lifetime retention.** The message buffer
and the `Code` handle ride the *same* pool entry, so neither can outlive or underlive the
other (Principle 18 — enforce invariants structurally); a `Box<str>`'s heap buffer address
is stable under `Vec` growth (only the box pointer moves). And the pool is **append-only to
session end** — entries are never freed on recovery, because:

1. the recovered-with-new-ABI case needs them forever anyway (above);
2. even a same-ABI recovery cannot prove no detached strand is mid-call in the stub at
   re-point time — freeing on re-point is a use-after-free hazard traded for a few hundred
   bytes;
3. the leak is bounded by the count of ABI-changing redefinitions + breaks in one session,
   measurable (got_trace §9.3), and restart reclaims everything (spine §5.6 pin (iv)).

This extends Decision 31 Scenario 2 (per-redefinition reclaim) with an explicit carve-out:
**reclaim-on-replacement applies only to `AbiPreserving` redefinitions**; `AbiChanging`
supersessions retain.

### 6.3 A latent as-built hazard this pool also cures (flag for `/dev`, in-sprint)

The Replace/reload paths clear compiled code by `*code = None`
(`lifecycle.rs:1069–1076`; `process_form.rs:702–708`), and both carry comments claiming the
`Arc<Jit>` handles "in `kept_jits`" keep the old pages alive — but `kept_jits` was dissolved
in S58 (Decision 35; retention moved per-entry onto `Code::Jit`). Today `*code = None` drops
what may be the **last** Arc and frees machine-code pages that in-flight frames or heap
closures can still execute. Under this design the Replace path moves superseded `Code` into
`retained_code` instead of `None`-ing it (§7.3) — the stale comments get corrected in the
same change-set. *Landed S101* (`clear_module_codegen`, §7.3). A third displacement site
of the same class — slotted prior replaced by a slot-less staged Def at the ordinary
commit — was missed by the Wave-4 change-set and cured in Wave 5 (FIXME 0479; see §10 T1's
residue paragraph).

---

## §7. ABI-epoch slot versioning — the bookkeeping

### 7.1 The commit gate is the single slot-policy authority

Slot policy per `RedefKind` (§2.1), applied where slots are already re-pointed today
(`worker.rs:450–468` + `repoint_callable_slot`):

| Kind | Slot | Prior `Code` | Callers |
|---|---|---|---|
| `New` | `allocate_got_slot()` (as today) | — | — |
| `AbiPreserving` | **reuse** prior slot (as today); codegen patches in place | carried, then replaced at codegen (Decision 31 Scenario 2 reclaim — as today) | untouched; late binding |
| `AbiChanging` | **fresh** `allocate_got_slot()`; the old slot is never written again | pushed to `retained_code` **before** `live.insert` | transaction (§4) |

The existing invariant comment ("we must NOT introduce a second allocation policy that
could disagree with typecheck's", `worker.rs:439–449`) is **superseded in the redefinition
case**: typecheck's `redef_slots` Pass-1 pin remains (it is the fast-path identity), and
the commit gate is the documented single authority that overrides it on `AbiChanging`.
`/dev` updates that comment in the implementing change-set.

**Fresh-slot is unconditional on ABI change, independent of the recorded caller set.** Even
with zero `callees` edges, invisible value captures exist — a wrapper closure minted by a
bare REPL expression (`(let [h f] …)` evaluated at the prompt) has no `Def` entry and no
edge, yet holds old-ABI code that loads `f`'s slot. Frozen-world covers it only if the old
slot freezes.

### 7.2 Freezing is structural, not a runtime check

"Never rebind a frozen slot" needs no frozen-set lookup at write time: **every slot writer
derives its slot index from a live entry** (`callable_got_slot()` — codegen's internal
write, the commit re-point, the trap patch, the zeroing walk), and after an `AbiChanging`
commit **no live entry carries the old index**. The illegal write is unreachable by
representation (Principle 20). The retention-pool entry records `(module, slot)` for
observability/debug assertions, not as a gate.

### 7.3 The watcher/Replace path joins the same discipline

The module-grain reload path (S35/S37 lineage: `try_pop_changes`' dependents scan,
`lifecycle.rs:871–897` → `reload_module` → Replace commit) is redefinition too, and today it
is ABI-unsound in exactly the spine-§5.2 way *plus* it opens a NULL window
(`clear_module_codegen` zeroes every slot during recompilation, `process_form.rs:676–695` —
a stale closure calling mid-window SIGSEGVs today). Changes:

- **Stop zeroing slots.** Old pointers stay live until each symbol's new pointer lands
  (per-slot atomic swap) — the ABI-preserving members get gap-free late binding; nothing is
  ever NULL. *Landed S101:* `process_form.rs::clear_module_codegen` (`:667`) no longer
  zeroes; displaced `Code` goes to the retention pool (§6.3), pool-less contexts keep the
  old drop.
- **Per-symbol gate at Replace commit**: each recommitted symbol classifies against its
  prior entry — `AbiPreserving` reuses + patches; `AbiChanging` takes a fresh slot and
  freezes the old one (prior `Code` → pool). *Landed S101:* the Replace path commits
  through the same shared gate, `worker.rs::commit_staging_to_live` (§7.1) — one slot-policy
  authority, both granularities.
- **Deleted symbols** (present before, absent in the new source): *designed* — entry
  removed, slot frozen, `Code` → pool (heap closures may still reference the deleted fn's
  old body). **As-built: NOT implemented — a recorded gap (FIXME 0477 item 2), not landed
  machinery.** The Replace commit never removes absent entries: the module table is
  preserved wholesale, and `clear_module_codegen` displaces every entry's `Code` to the
  pool but removes nothing. Ghost entries remain resolvable, and the synth-def sweep can
  resurrect a deleted body — pre-existing behaviour, unchanged by S101. The removal leg
  (entry removal + slot freeze on deletion) stays open design intent for a future
  change-set.
- The **affected set stays module-grain** on this path (the imports-scan dependent cascade
  reloads whole dependent modules) — sound by over-approximation; symbol-level watcher
  diffing is a named future refinement (spine §5.4 preamble), not stage M.

### 7.4 Inherited slab invariant

The per-module GOT slab's base address is baked into finalized code, so the slab must not
move while `next_got_slot` grows — verified by `/dev`(backend) before enabling fresh-slot
churn (backend §8.2, S101 wave-carry item). Cited, not restated; nothing in this design
adds a new growth *kind*, only more growth *events*.

---

## §8. Persistence — pins (i)–(iv) honoured

Spine §5.6's binding facts, mapped to mechanism:

1. **(i) Slot numbers + `next_got_slot` serialize already** — `got_slot` rides the callable
   `DefKind` variants (S83 reshape) and `next_got_slot` is a serde-visible monotone counter
   (`module.rs:135`, allocator `:609`); both land in `.meta.json` via the existing
   SymbolTable serialisation. Fresh slots allocated by the transaction ride the same paths;
   **no new serialisation is introduced by this design.**
2. **(ii) Faithful write after every redefinition** — `regenerate_backing_file` runs at the
   end of every defining eval (as today), and the nice worker's `.o`/`.meta` persist reads
   the live table (with the §8.3 poisoning rule). Slot indices are load-bearing against
   `.o` machine code (`load(slab_base + slot*8)`), so **no code path renumbers** — no
   compaction exists, and FIXME 0466 keeps load-time reclamation rejected.
3. **(iii) The permanent hole** — an ABI-changing **persisted** redefinition leaves the
   frozen index unreferenced by any entry while `next_got_slot` stays above it; the
   regenerated `.meta` faithfully carries both. Cache load must size/populate the slab from
   the persisted `next_got_slot` (≥ high-water), leaving holes as dead 8-byte entries —
   an L-R5 verification obligation on `/dev` at implementation.
4. **(iv) High-water = freeze boundary** — a new session allocates strictly above anything
   any cache references; frozen-slot **bindings** (retained `Code`, trap buffers, old code
   pointers) die with the session — restart is the zero-cost reclamation of §6's pools.

**Broken-state round-trip (the designed restart semantics).** The backing file is
regenerated with what the user actually has: new `f`, and `g`'s **unchanged (now-broken)
source**. On restart the cache cannot mask the break: same-module — the module's source hash
changed, cache invalid, recompile from source surfaces the type error as an ordinary
load-time compile error (the S45-class report); cross-module — `g`'s module imports `f`'s
module whose source hash changed, so the direct-import invalidation + `recompiled`-set
cascade (`session_setup.rs`; spine §5.1) recompiles `g`'s module and surfaces the error.
Broken-ness is therefore **reconstructed as an ordinary compile error, never persisted as a
trap** — which is why (§5.4/§8.2) a module holding a BROKEN symbol must **skip** the
nice-worker `.o`/`.meta` write for that turn: a cache snapshot containing a trap stub's GOT
state would claim compiled health the module does not have. The skip is cheap (the source
hash has diverged anyway, so the stale cache is already unusable) and self-heals at the
first fully-green turn.

---

## §9. Surfacing — the turn report, `/info`/`/sig`, observability

### 9.1 The cascade report (data contract; wording is `/repl`'s)

The transaction returns a report the eval turn renders after the normal eval output:

```rust
struct TransactionReport {
    target: FQSymbol,                 // what was redefined
    kind: RedefKind,                  // AbiPreserving reports render nothing extra (L-R3, L-D1)
    recompiled: Vec<FQSymbol>,        // exactly the SCC members actually re-typechecked green
    broken: Vec<(FQSymbol, String)>,  // member + original error
    recovered: Vec<FQSymbol>,         // previously-BROKEN symbols this transaction fixed
    stale: Vec<FQSymbol>,             // §9.1.1 (S102): compiled callers left on the previous
                                      // definition by a §10 T1 downgrade — mutually exclusive
                                      // with recompiled/broken by construction (per-symbol
                                      // transactions never produce stale; downgrades never
                                      // recompile/break)
}
```

#### 9.1.1 The downgrade (`stale:`) section — S102 interim cure for §10 T1

`repl/spec.md` §18.1.1 is the normative surface (header line, §1.1 name layout,
omit-when-empty, informational-only). The data contract this design owes it:

- **Trigger.** Every commit whose classification took the §2.2 `!per_symbol` arm with a
  prior `Def` under the name (the T1 route — target kind outside per-symbol precision),
  gate-exempt internals excluded. The trigger is the *route*, not the surface diff: even a
  scheme-equal redefinition of a polymorphic template leaves previously-minted mono
  instances (and their compiled callers) on the old body — the split world is about
  artifacts, not schemes.
  - **Slot refinement (S103, FIXME 0507 Issue 1 / F2).** `is_t1_downgrade` also requires
    `o.new_slot.is_none() || o.old_slot.is_none()`. The bare `prior_was_def && !per_symbol`
    predicate over-fires for a **slotted prior replaced by a slotted staged entry** outside
    per-symbol precision — the constructible shape is `deftype` re-entry, whose ctors are
    slotted `DefKind::Constructor` Defs: the commit **reuses** the prior slot and patches
    code in place, so compiled callers dispatch through the same GOT slot and **do** pick up
    the new definition at their next call. Naming them `stale:` would violate §18.1.1's
    negative MUST ("must not name any symbol that picks up the new definition at its next
    call"). Requiring a slot-shape change keeps every designed cell (slot-less **staged** =
    displacement/template shapes; slot-less **prior** = concrete-over-template mint-staleness)
    and excludes the slotted→slotted late-binding case. This same slot-refined predicate gates
    the **full-cure driver** below — a ctor re-entry that late-binds correctly must NOT trigger
    a needless module reload. Gate before §18.1.1's rows earn `[Tested+Neg]`; the existing unit
    `t1_downgrade_trigger_route_cells` fixture (both slots `None`) needs no rewrite, and /qa adds
    the ctor-target e2e cell (both-slots-present ⇒ no `stale:`).
- **`stale` set = the DIRECT reverse-edge callers of the target and of its `$`-mangled
  variants** (`callers_of(f) ∪ callers_of(f$…)` where the variant's base is `f`),
  restricted to entries that hold compiled code (`code: Some` — "compiled callers").
  Never-compiled callers (templates, `ast`-only entries) late-bind at
  their next mint and MUST NOT appear (§18.1.1 exactness, negative half). The feed is the
  same on-demand `ReverseIndex` (§3.3) — built only on downgrade turns, so the L-D1 pin
  (body-only **concrete** redefinitions at today's cost) is untouched; a T1 turn pays one
  table scan, microseconds against the honesty it buys.
  - **Gate-exempt exclusion is `__expr`-only at the FEED (S103, FIXME 0507 Issue 2 / F3 —
    supersedes the "0491 rule applies identically" reading).** `ReverseIndex::build` excludes
    only the synthetic `__expr` wrapper as a caller — never a `__macro_*` clause. The 0491
    safety argument ("a stale wrapper is never re-invoked; each expression turn redefines it
    before invoking") is true of `__expr` alone. A compiled macro clause
    (`__macro_{name}_clause_{idx}`) **persists and IS re-invoked** at the next expansion, and
    per spec §9.3.4/§9.12 a clause body **may** reference a dependency-module fn — so an
    AbiChanging redefinition of that dependency fn leaves the clause coherent-stale (frozen
    world, no crash) and, under the old blanket exclusion, invisible: a silently-stale
    expansion path. Confirmed **reachable**; the feed keeps macro-clause reverse edges.
  - **A macro-clause caller is RENDERED as its owning user macro, never the raw `__macro_*`
    symbol** (§18.1.1 "no internal artifacts" — the same base-fold §18.1.1 applies to
    `$`-mangled mono variants, extended to the `__macro_{name}_clause_{idx}` → `{name}`
    prefix, qualified by the clause's home module). Its **disposition** is module-grain reload
    of its home module, not per-symbol recompile — a synthesized clause has no standalone
    re-typecheck-from-sexp (§4.2) and the only sound refresh is re-**expansion**, which is
    Pass-1 whole-cluster (§9.12). This is exactly the §10 T1 full-cure machinery, so under the
    cure a macro whose clause calls a redefined dependency fn reloads its module and the stale
    set renders empty. (`/refs`' textual-scan leg is now redundant with the index leg for
    macro-clause references — the exclusion no longer hides them — but `/refs` MUST likewise
    render the owning macro, not the raw clause symbol.)
- **Rendering** rides the same `TransactionReport`/`pending_cascade_reports` channel as
  §18.3's sections — the S102 arch review's Principle-8 pin verbatim: the full cure (§10
  T1 end-of-turn reload) recompiles exactly the callers this section names, rendering it
  empty, so the section is kept machinery, not throwaway.
- **Gate-side production.** The commit gate must emit a `RedefinitionOutcome` for **every**
  redefinition-of-a-prior-`Def`, including the T1 shapes (staged slot-less displacing a
  slotted prior — the FIXME-0479 displacement site — and template-replacing-template);
  outcomes are the only channel the driver sees, so a T1 shape that produces no outcome
  is invisible to the print. `/dev` verifies and widens outcome production accordingly.
- **Startup-load exception (S103, FIXME 0507 addendum 4).** `recover_startup_failure`
  (CS-0489) drains `pending_cascade_reports` while re-driving the backing source
  form-by-form against a warm table, so a Def-over-Def during that re-drive **classifies**
  but MUST NOT print a `stale:` (or any cascade) section: startup is a **load**, not a user
  redefinition turn. The suppression is the report-drain at the loader, not a trigger change
  — the classification still runs (it must, to populate slot policy / retention), only the
  rendering is elided at the startup path. The section resumes normally at the first
  interactive redefinition turn.

`recompiled` is exact by §4.1's skip test — the positive **and** negative L-R3 assertions
read this report. Normative rendering (grouping, phrasing, the trap message text) is the
`/repl` spec half (sprint item 7, `repl/spec.md`); until it lands, L-R1's substring anchors
apply (qa plan §5 limit 6).

### 9.2 `/info` / `/sig` broken status

**As-built (S101 Wave 4; supersedes the designed carry-on-`SymbolDescription` shape).**
Broken status renders **directly at the three display sites** — `handle_sig`
(`repl.rs:711`), `handle_info` (`repl.rs:1275`), and the bare-symbol lookup display
(`repl.rs:2159`) — each through the ONE shared helper
`redefine.rs::broken_status_line` (`redefine.rs:1044`), which consults `shared.broken` and
composes the `repl/spec.md` §18.4 provenance comment line (L-R1(d)). Composition is
centralised in the helper, so there is no P7 duplication across the sites.
`SymbolDescription` was **not** extended with a broken-status field. **Recorded residual
(a nicety, not a lane obligation):** the agent-harvest consumer of `SymbolDescription`
does not see broken status; carrying it onto `SymbolDescription` is the follow-up if
harvest context ever needs it. The entry itself still answers with its retained
scheme/docstring — a broken symbol is introspectable, not erased (self-documenting REPL).

### 9.3 Observability

`got_trace` (the existing redefinition observer, `got_trace.rs:280 emit_redefinition`)
gains two event kinds: **slot-freeze** (module, symbol, old slot, new slot) and
**trap-patch** (module, symbol, slot). The retention pool's length is the leak metric.
The report (§9.1) is the primary observable for L-R3; traces are the debugging channel.

---

## §10. Stage-M scope boundary and the conservative fallback (precise triggers)

Per-symbol precision at stage M covers: **redefinition of a concrete single-sig `UserFn`
`Def`** — the shape all of L-R1–L-R5 exercise. Outside it, the designed fallback was the
**existing module-level dependent reload** (S35/S37 machinery: `reload_module` + the
imports-scan dependent cascade), sound by over-approximation and, with §7.3's commit gate,
also ABI-sound. **As built (S101 Wave 4), that fallback fires only for T2**; T1 was
downgraded (below) and T3 is unimplemented-because-unreachable. The triggers, exhaustively:

- **T1 — target kind.** The redefined name's prior entry is not a concrete `UserFn`
  (generic/constrained base, `Overloaded` multi-sig base, `Macro`, `Constructor`/deftype,
  trait decl/impl, platform effect). *Designed:* reload the target's module and cascade at
  module grain. **As-built (FIXME 0477 item 1, upheld at change-set review): DOWNGRADED —
  such targets classify `AbiPreserving` with `per_symbol: false`** — today's
  reuse-and-patch, no transaction, no reload (`src/redefine.rs::classify_redefinition`,
  the `!per_symbol` arm; §2.2).

  **Why the designed reload is unsound for T1 specifically:** `reload_module` reloads
  from the module's **backing file**, and `regenerate_backing_file`
  (`session_v4/lifecycle.rs:942`) runs only at the **end** of the defining eval turn — so
  a mid-turn reload of the *target's* module would reload the **pre-redefinition** source,
  resurrecting the old definition and clobbering the just-committed entry. It would also
  re-enter the entry module the eval thread is itself driving (against Invariant SW's
  spirit — the entry module has a single orchestrator). The asymmetry that keeps **T2's**
  mid-walk reload sound: T2 reloads *member* modules, whose on-disk source is current —
  they were not redefined this turn; T1's target lives in the very module whose backing
  file is mid-turn-stale. The same mechanism is available to one and poisoned for the
  other.

  **Named residue — the T1 type-change hole stays OPEN at stage M.** The design as
  written would have cured the pre-existing type-changing-redefinition hole (spine §5.2)
  for these target kinds; the as-built downgrade does not — callers compiled against the
  old surface are neither recompiled nor trapped. What IS cured this sprint is the
  hole's **crash edge** (FIXME 0479, fixed S101 Wave 5): a slotted prior displaced by a
  slot-less staged Def (concrete → polymorphic/overloaded redefinition) now has its
  `Code` retained in the pool at the commit gate, so the former last-Arc drop → freed
  JIT pages → SIGSEGV becomes **coherent-stale** old-chain execution through the
  still-populated slot (the §4.3 frozen-world argument). The failing guard is FIXME
  0478's `/qa` repro (stale-execution leg RED by design until the cure).

  **S102 interim cure — the downgrade is no longer silent.** The T1 route prints the
  `repl/spec.md` §18.1.1 `stale:` section (data contract: §9.1.1) naming the compiled
  callers left on the previous definition. Informational only: nothing is recompiled,
  broken, or trapped — the coherent-stale residue itself stands until the full cure.

  **Full-cure mechanics — IMPLEMENTATION-READY (S103 Phase 3, FIXME 0507).** The
  end-of-turn-sequenced module reload replaces the S102 interim print. Its two original
  blockers dissolve with machinery that already exists, and its S102-preconditions are now
  landed (below), so this is an implementation-ready change-set set, not a deferred design.
  End-of-turn sequencing dissolves both named blockers:
  (i) *resurrection* — the reload runs **after** `regenerate_backing_file`, so the
  backing source carries the just-committed redefinition (never the pre-redefinition
  source a mid-turn reload would resurrect); (ii) *Invariant SW re-entrancy* — the reload
  reuses the watcher discipline verbatim (`re_register_module` resets the target to
  `TypecheckFirst` + `sexps: Some` and a pool worker re-typechecks it while the eval thread
  blocks in `wait_inmem_complete_blocking` — no second orchestrator because the eval thread
  is waiting, exactly the S93 watcher ruling; the entry module never enters
  `TypecheckBlocked` on this path either, so B1 stays closed).

  **The change-sets, in dependency order (rides the src/ window Block C1 opens):**

  1. **CS-1 — the end-of-turn reload driver** (`eval.rs`/`process_form.rs` eval path).
     After a turn whose `RedefinitionOutcome`s include a T1 downgrade **that survives the
     §9.1.1 F2 slot-refined trigger** (`prior_was_def && !per_symbol && !gate-exempt(__expr)
     && (new_slot.is_none() || old_slot.is_none())`), and **after** `regenerate_backing_file`
     has run for the turn, reload the **target's module** via the watcher-discipline
     `reload_module`/`re_register_module`, then cascade dependents through the `poll_and_reload`
     imports-scan — all committing through the §7.3 Replace commit gate (one slot policy, both
     granularities). Eval-synchronous; the eval thread blocks on the reload's terminal signal.
     The macro-clause staleness of §9.1.1's F3 resolution is cured here for free: a module
     whose `__macro_*` clause calls a redefined dependency fn is a **dependent** (it imports the
     dependency) and reloads in the `poll_and_reload` cascade, re-expanding + recompiling its
     clauses against the new definition.
  2. **CS-2 — module-grain report integration** (`redefine.rs` report channel + a /repl
     wording increment). Module-grain reload outcomes render through the same
     `TransactionReport`/`pending_cascade_reports` channel as §18.3's sections and §9.1.1's
     `stale:` — the Principle-8 pin: the full cure recompiles exactly the callers `stale:`
     named, so the section renders **empty** (kept machinery, not throwaway). Module-grain
     reporting needs a /repl normative-wording increment (routed at CS-2) — until it lands,
     the report asserts the empty-`stale:` acceptance only.
  3. **CS-3 — edge handling** (`lifecycle.rs`/`session_v4.rs`). A reload **failure** MUST
     degrade to the §14.4 error-blocked state (the 0489 prompt floor), never a lockout or a
     session exit; a module whose regen is **suppressed** (FIXME-0343 `should_regenerate`
     guard — e.g. a read-only backing file) keeps the `stale:` print instead of reloading
     stale disk source (the reload's input would be stale). Non-entry `/mod M` targets reload
     from `M`'s regenerated backing file the same way — D2's authorship-fidelity cure is what
     makes that write acceptable.

  **Macro-target handling (S103, FIXME 0507 Issue 3 / F5a).** `defmacro` turns return early
  in `eval.rs` (`eval.rs:329`) **before** `apply_redefinition_outcomes`, so a redefined-macro
  target produces no outcome and the T1 route cannot fire for it today — currently moot because
  macro heads carry no reverse edges, but the CS-1 driver must be reachable from the defmacro
  path (place the end-of-turn reload trigger *after* regen on **both** the ordinary-def and
  defmacro exits, or route the defmacro early-return through the shared post-regen driver).
  A redefined macro whose clauses changed is otherwise cured by its own module's reload; a
  redefined macro that dependents *use* is cured by the dependent cascade (their re-expansion
  picks up the new macro). This closes the F5a pinning note the S102 Wave-4 review filed.

  **Preconditions — now LANDED (S102), so the cure is unblocked** (the S103 scope ruling):
  faithful regeneration (D1/D2 cures: no expansion-artifact/origin double-persist; authorship
  fidelity — `regenerate_backing_file` now emits verbatim source-first, `src/CLAUDE.md`
  §"Degraded startup load"), the 0489 prompt floor + §14.4 degrade path, and the D3/0487
  cache-restore env recompute (a reloaded file-backed module recompiles). The FIXME-0343
  `should_regenerate` guard is CS-3's edge. No increment-II (Block B) mechanism writes the
  lifecycle/save seams the cure consumes, so the two tracks do not contend (§2.4 `AbiSurface`
  seam untouched by the reload driver).
  - **Regen-fidelity scope check (S103, FIXME 0507 addendum 8 / I-4 — precondition-adjacent).**
    The reload reads the **regenerated** backing file, so the cure of a module containing
    **traits/types/impls** depends on regen fidelity in sections 5–7, not only the section-8
    (fns/macros) D1/D2 cures that were the S102 focus (`save::generate_fns_and_macros`'s
    source-first + dedup is section-8-local). Before CS-1 reloads a trait/type-bearing module,
    /dev must confirm sections 5–7 either share the source-first + dedup invariant or are
    provably exempt (Matrix B's entry-kind axis). A section-5–7 regen-poison would silently
    rewrite the user's trait/type source on a T1 reload — the same D1 class one section over.
    This is the one precondition still to *verify* (not a new mechanism); flag to /dev in CS-1.

  **The two coherent-stale pins to flip** (the §18.1 scope-note residue, each carries a flip
  note): `tests/repl_redefinition.rs::redefine_concrete_to_polymorphic_caller_survives_coherent_stale`
  and `redefine_concrete_to_overloaded_caller_survives_coherent_stale` — under the cure the
  compiled caller is **recompiled** against the new definition (or broken+trapped with
  provenance), so their `:primitives/Int 6` old-chain pin flips to the cured value and the
  §18.1.1 `stale:` section renders empty. The S102 L-U1 sibling
  `redefine_unannotated_generic_target_caller_keeps_old_chain_sibling` and the report pair
  (`t1_downgrade_report_*`) carry the same flip (the report pair's positive `stale:` assertions
  invert to empty-section assertions); /qa owns the e2e flips, `/dev` the unit-level.
  Consequence for the normative surface: `repl/spec.md` §18.1's coherence MUSTs, currently
  satisfiable at stage M only for concrete single-sig `UserFn` targets (stage-M scope note,
  FIXME 0481), become satisfiable for the T1 target kinds too once the cure lands — the §18.1
  scope note + the two pins' flip notes retire together.

  (Mono/mangled variants of a *concrete* target do not arise — a single-sig concrete
  fn has none.) **T1 governs the redefined *target* only.** A slot-less entry reached
  mid-walk as a closure *member* — a constrained template between the target and its
  mono-minting callers, the FIXME-0473 case — is **not** a conservative trigger: it takes
  §4.1's pass-through at per-symbol grain. Routing members here (that FIXME's option 2)
  was rejected because templates are pervasive in any polymorphic cone — the fallback
  would become the common case; see §4.1's ruling rationale.
- **T2 — unrecoverable re-typecheck input.** A closure member's raw sexp is unavailable:
  no introspection record AND backing-file rehydration (§4.2) fails. Reload that member's
  module at module grain; continue the walk with the module's symbols treated as
  recompiled-at-module-grain.
- **T3 — untrusted edge feed.** A module transitively importing the target whose entries
  are not body-checked at the current extraction (e.g. signature-registered-only states
  mid-flight). Operationally rare at stage M — the §3.2 schema bump guarantees any *loaded*
  cache is extraction-current, and live tables are always current — but when detected, that
  module joins the affected set at module grain. **As-built: unimplemented** — no
  detection is wired, which is consistent with this paragraph's own rarity argument: the
  §3.2 bump landed (`CACHE_SCHEMA_VERSION = 11`,
  `crates/cranelisp-backend/src/cache/mod.rs:218`), so the trigger is unreachable at
  stage M. Designed-not-built; revisit only if a state arises that the schema gate does
  not cover.

Everything module-grain (T2, and the watcher/Replace path) flows through the one Replace
commit gate (§7.3), so both paths share slot policy, retention, and reporting — one
mechanism, two granularities, not two protocols.

---

## §11. Lane satisfiability map (qa plan §3.6, §2.1)

| Lane | Satisfied by |
|---|---|
| **L-R1(a)** direct call of broken `g` raises with provenance | §5.1 in-place trap patch + composed message; backend §8.1 stub |
| **L-R1(b)** pre-break closure of `g` reaches the trap | wrapper/lambda bodies dispatch GOT-indirect (spine §5.2); slot patched in place — the closure's own code ptr is unchanged but its call loads `g`'s slot. (Primitive-family value-use additionally requires the sprint-item-1 NULL-slot fix — sequenced before this, same seam.) |
| **L-R1(c)** curried partial reaches the trap | AutoCurry wrappers call the target through its slot — same argument |
| **L-R1(d)** `/info`/`/sig` broken status | §9.2 |
| **L-R1(e)** recovery both directions | §5.3 (gate re-classification; retained edges for the reverse direction) |
| **L-R1(f)** bounded RC-mid-panic leak | §5.4 (documented per-trap tolerance) |
| **L-R2** frozen world + preserved late binding | §7.1 policy table (fresh+freeze vs reuse+patch), §4.3 no-window argument |
| **L-R3** exact recompiled-set report, positive + negative | §4.1 skip test (incl. slot-less pass-through — templates never truncate the set) + §9.1 exact `recompiled`; fast path renders nothing (§2.3) |
| **L-R4** type-change hole cured | the whole §2→§4→§5 pipeline at stage M (scheme-only comparand) — the sprint's own RED witness. Scope at S101/S102: concrete single-sig `UserFn` targets only — T1 target kinds retained the pre-existing hole as-built (§10 T1 named residue; guard = FIXME 0478's repro). **S103: the T1 full cure (§10 change-sets CS-1..3) extends the cure to T1 target kinds via module-grain end-of-turn reload — the two coherent-stale pins flip and the §18.1 scope note retires** |
| **L-R5** persistence pins, two-session | §8 items 1–4 + broken round-trip |
| **L-D1** body-only at today's cost | §2.3 (one compare; all slow-path cost gated), §3.3 (no index maintenance on the fast path) |

---

## §12. Quality attributes (per `/design` stewardship)

| Attribute | Disposition |
|---|---|
| **Simplicity** | One classification gate at the one commit chokepoint; one retention pool for both retention classes; on-demand index (no maintenance protocol); module-grain fallback reuses existing machinery wholesale (Principle 6). |
| **Maintainability** | The increment-I evolution is confined to `AbiSurface::of` + an edge-kind flag (§2.4, §3.2); slot policy, transaction, pool untouched. Not interim architecture: the gate/pool/index are the permanent commit mechanism (S101 arch review, Principle 8). |
| **Observability** | Turn report is the primary observable; got_trace freeze/trap events; pool length = leak metric; broken registry answers introspection (§9). |
| **Concurrency-safety** | Transaction is eval-thread-synchronous and staging-based — no pool transitions, no new shared mutable state beyond two session maps (`DashMap`/`Mutex`, write-side eval-only). No quiesce needed: frozen-world makes every interleaving safe (§4.3). Cures the reload NULL-window and the `*code = None` page-free hazards (§6.3, §7.3). |
| **Performance** | L-D1 pinned by construction (§2.3). Slow path bounded by the real dependency cone (spine §5.4 sizing honesty); scan cost §3.3. Stage M has no perf gates beyond L-D1 (qa §2.1). |
| **Testability** | Pure seams for `/dev` unit tests: `AbiSurface::of`/compare (synthetic entries), reverse-index build (tables in, multimap out), closure+SCC+ordering incl. the slot-less pass-through (edge list + entry kinds in, ordered SCCs + propagation decisions out), classification gate (prior/staged entries in, `RedefKind` out). E2E is `/qa`'s L-R1–R5 scripted REPL sessions (Principle 5). |

---

## §13. Implementation grain (for `/dev` on `src/`)

- **New module `src/redefine.rs`** — `AbiSurface`, `RedefKind`, `ReverseIndex`,
  `affected_closure` (+ SCC/reverse-topo ordering, incl. the §4.1 slot-less pass-through:
  propagation decision keyed off `callable_got_slot().is_none()` — no new state), the
  transaction driver (`run_transaction(&mut CompilerSession, target) -> TransactionReport`),
  `mark_broken` (with the §5.1 slot-less degenerate arm: registry record only, no pool
  push, no trap patch), trap-patch composition. Joins the `src/CLAUDE.md`
  §module-decomposition table.
- **`SharedState`** gains `broken: DashMap<FQSymbol, BrokenInfo>` and
  `retained_code: Mutex<Vec<RetainedCode>>` (§5.1, §6.1).
- **Commit gate** in `worker.rs`'s staging→live commit (`worker.rs:421–470`): classification
  + slot policy + retention push; redefinition outcomes ride `ProcessedCluster` (a
  `redefinitions: Vec<RedefinitionOutcome>` field) back to the driver; the eval path
  (`eval.rs::process_form_cluster` / `codegen_and_execute`) runs the transaction for
  `AbiChanging` outcomes after the target's own codegen succeeds.
- **Replace path** (`process_form.rs::clear_module_codegen`, `lifecycle.rs::reload_module`):
  stop zeroing; per-symbol gate; deleted-symbol freezing; `Code` → pool instead of `None`
  (§6.3, §7.3); stale `kept_jits` comments corrected.
- **Display**: broken-status via the one shared `redefine.rs::broken_status_line` helper
  at `handle_sig`/`handle_info`/bare lookup (§9.2 as-built; `SymbolDescription` not
  extended); report rendering in the eval turn per the `/repl` spec half.
- **Cross-crate dependencies**: `compile_trap_stub` (backend, sprint item 5);
  `Def.callees` enrichment + `CACHE_SCHEMA_VERSION` bump (typecheck, **FIXME 0470** — load-
  bearing for L-R3/L-R4, must land before or with the transaction); GOT slab-growth
  verification (backend `/dev`, §7.4).
- **T1 full cure (S103, FIXME 0507 — §10 T1 change-sets, `src/`-only, no cross-crate)**:
  - **`redefine.rs::is_t1_downgrade`** — add the F2 slot refinement (`&& (o.new_slot.is_none()
    || o.old_slot.is_none())`); this needs `RedefinitionOutcome` to carry `old_slot`/`new_slot`
    (verify the commit gate populates them — the ABI-epoch slot policy §7.1 already computes
    both). Same predicate gates the CS-1 driver.
  - **`redefine.rs::ReverseIndex::build`** — narrow the feed exclusion from
    `is_gate_exempt_internal` to `__expr` only (`name == SYNTHETIC_EXPR_WRAPPER`); macro-clause
    reverse edges are retained. (Note the predicate SPLIT: `is_gate_exempt_internal` stays the
    **target**-exclusion at the trigger/classify sites — a macro clause is never a T1 redefinition
    target — but the **caller/feed** exclusion narrows to `__expr` only; do not reuse the one
    predicate at both sites.) Add a render-time base-fold: a `__macro_{name}_clause_{idx}`
    caller renders as `{name}` (home-module-qualified) in `stale:`/`recompiled:`/`broken:`; its
    disposition is module-grain reload, not per-symbol recompile. **This also closes the F3
    per-symbol-transaction leg**: when a *concrete* dependency fn is redefined AbiChanging and a
    cross-module macro clause calls it, the clause is now reachable in the §4.1 affected-set
    closure; it has no standalone sexp, so it routes to §10 T2 module-grain reload (existing
    machinery) — re-expansion refreshes the clause. Flag to /qa: a new scenario (AbiChanging dep
    fn + macro-clause caller ⇒ clause's module T2-reloads).
  - **CS-1 driver** (`eval.rs`/`process_form.rs`) — after `regenerate_backing_file`, for a
    surviving-trigger T1 turn, `reload_module`(target) + `poll_and_reload` dependent cascade
    through the §7.3 Replace gate; eval-synchronous. Reachable from BOTH the ordinary-def and
    the `eval.rs:329` defmacro early-return (F5a).
  - **CS-3 edges** (`lifecycle.rs`) — reload-failure → §14.4 error-blocked (0489 floor);
    `should_regenerate`-suppressed module keeps the `stale:` print (no stale-disk reload).
  - **Unit seams for `/dev`**: the slot-refined trigger (outcome in, bool out — ctor-shape both-
    slots-present cell), the `__macro_*` render-fold (clause symbol in, base name out), the
    `__expr`-only feed exclusion (`reverse_index_neg_excludes_only_expr` supersedes the former
    `..._gate_exempt_internal` guard's `__macro_*` half). E2E is /qa's L-U1 flip + empty-`stale:`
    acceptance (owns the two coherent-stale pin flips).

## Next skills

- `/dev` (src/) — implement per §13 after `/qa`'s failing L-R1–R5 set exists (Phase 5); **S103
  adds the T1 full-cure change-sets (§10 T1 CS-1..3 + the F2 slot-refined trigger + the F3
  `__expr`-only feed narrowing / macro-clause render-fold), `src/`-only, no cross-crate**.
- `/typecheck` — resolve FIXME 0470 (edge-extraction widening + schema bump); sequenced
  before or with the transaction implementation.
- `/dev` (cranelisp-backend) — `compile_trap_stub` (§8.3 pinned call 2) + the §8.2
  slab-growth verification; already sprint items 5/4.
- `/repl` — the normative wording half (trap message, broken-status display, cascade
  report, frozen-world semantics) — sprint item 7; §9.1's data contract is its input.
- `/qa` — draft L-R1–L-R5 + L-D1 against §11's map.
