# Ownership codegen — the backend-crate proposal (parts 12–16)

**Status:** DESIGN (S100 Phase 3, stage 2; amended S101 Phase 3 — §2.3 toggle-timing
reconciled to the `/arch` S101 Phase-2 ruling, §8.1/§8.3 implementation pins added, §12
item 7 upgraded from triage note to fix brief) — the per-crate codegen proposal for the five
ownership-consuming backend mechanisms. Authored by `/design` narrow-deployed on
`cranelisp-backend`, against the S100 sprint scope (`sprints/SPRINT.md` parts 12–16).
**Governing authority:** `design/arch/ownership-inference.md` (the S100 master spine, as amended
2026-07-02). Where this proposal and the spine disagree, **the spine governs**; this proposal
resolves the spine's §10 backend items 7–14. Second governing input:
`design/typecheck/ownership-inference.md` (the typecheck proposal) — its §8.4 coordination
interface and §12 items 1–4 are consumed here as stated inputs. Pre-implementation; no source
edit, no `public-api.txt` movement, no `cranelisp-types` change lands in S100.
**Subordinate to:** `design/backend/backend.md` (the crate master doc; §8 there indexes this
doc). Grounding docs: `ring2-rc.md` (Decision 24 + §5.5/§5.5.2 — now annotated with the S100
conservative-point framing per FIXME 0465, actioned with this doc), `lenient-eval.md` (spark
machinery), `module-caching.md` §3/§14, `design/arch/release-llvm-backend.md` §6–§8 (M4–M7
shapes, landed on the shared tier per spine §3.4).

> **STANDING INVARIANT (never violated by anything below).** The conservative
> all-Owned / all-atomic / all-heap lowering — byte-for-byte today's Decision-24 codegen —
> remains permanently reachable under the master analysis-off toggle (§2), and every mechanism
> in this document is strictly gated behind a present fact/summary whose absence selects the
> unmodified existing emission path. A build with the toggle off is **byte-identical to
> pre-S100 codegen**. This is the spine's §3.4/§6.2 oracle obligation, and it is a design
> constraint on every section, not a test-time aspiration.

---

## §0. Scope and the increment frame

This doc designs the **five consuming mechanisms**: backend codegen changes that consume the
one interprocedural analysis' outputs (ABI-bearing mode vectors + advisory site facts, spine
§3) on the **shared Cranelift lowering**. It answers the spine's §10 items 7–14:

| Spine item | Where answered | Ruling in one line |
|---|---|---|
| 7. Borrow-elision emission + R2 codegen half | §3 | Callee-side: `Borrowed` params join `borrowed_vars` at entry (subsumption made literal); caller-side: skip the consuming inc in `compile_consuming_arg_list` when the callee vector says `Borrowed`; temporaries to `Borrowed` params get a caller post-call dec; R2 value wrapper = per-`(fq, got_slot)`-named synthesized adapter (operator-wrapper precedent), auto-curry **composes** via one shared adaptation-algebra helper, never stacks |
| 8. Stack/region for `NoEscape` | §4 | Increment I = Cranelift **stack slots with immortal-RC headers** for statically-sized, all-scalar-payload backend-emitted allocations; the sentinel makes every residual RC/COW path harmless by construction; region arena (M7 shape, dynamic sizes, extern-adjacent) = increment II, co-designed with the (a) allocator axis |
| 9. Non-atomic RC for `Confined` | §5 | Generalise the existing `CRANELISP_NONATOMIC_RC` emission arms (`heap.rs`) — re-gate them per-site on the `confined` fact instead of the process-global unsound probe; increment I covers inline ops only; the shared per-type helpers stay atomic (inventory named) |
| 10. Reuse tokens / drop-guided reuse | §6 | Increment II; token = function-local SSA maybe-null value, never on the ABI (spine §3.5); bulk ops keep the **per-call entry check** (the as-built inline-COW precedent) — copy-once-then-in-place; static proof (typecheck §7.2) elides the check, never replaces the mechanism |
| 11. R5 value-representation flattening | §7 | `HeapCategory` gains a `Value` arm; **one-word (8-byte) size bound for the first landing** — zero ABI change anywhere, Vec-of-values = the existing null-elem-fn mechanism; classification is a deterministic pure function of type defs ⇒ cache/`--link` parity by construction + `CACHE_SCHEMA_VERSION` bump; predicate single-sourcing filed as FIXME 0468 |
| 12. R3 backend half | §8 | Trap stub = **per-symbol emitted stub baking a provenance-message pointer and calling the existing `runtime/panic` extern — no new intrinsic**; fresh slots ride the existing `allocate_got_slot` path; frozen-slot retention = session-held `Code` list (the `kept_dlls` precedent); the /int-facing interface is three calls, stated in §8.3 |
| 13. Analysis-off toggle scope | §2 | One env switch (`CRANELISP_NO_OWNERSHIP=1`), read producer-side (typecheck emits nothing) **and** enforced structurally consumer-side (every mechanism's else-arm is the unmodified existing helper); the toggle joins the cache manifest's global invalidation keys so no mixed-ABI cache can exist |
| 14. Dual-symbol extern convention | §9 | Sibling = shared-core Rust fn + second export (`<name>$borrowed`); increment I ships the pattern + **one template instance: `str-len`** (`vec-len` is NOT a candidate — its static sites are inline-lowered, no pair to elide; correction of the spine's example against source); expansion is data-driven via `CRANELISP_RC_STATS` attribution |

**Increment staging (binding, spine §7).** Increment I ships §2 + §3 + §4 (stack slots) + §5 +
§9's single sibling (§2's toggle + manifest key were pulled forward to the S101 stage-M
machinery sprint by the `/arch` S101 Phase-2 ruling — see §2.3). Increment II ships §6 +
§7 + §4's region arena. §8 (the R3 half) lands
**before or with** increment I's ABI-bearing modes per spine §5.7 — it is machinery, not a
mechanism, and is valuable standalone (it also cures the latent type-change hole). Every
section below is tagged where the distinction bites.

---

## §1. Actors and functions first (Principle 21)

Before mechanism: the actors this design changes, and the functions between them — all real
seams in today's source (`crates/cranelisp-backend/` unless noted):

- **The RC emission SSOT** (`src/heap.rs`) — `emit_rc_inc` (`:177`), `emit_rc_inc_guarded`
  (`:205`), `emit_rc_dec` (`:312`), `emit_rc_dec_guarded` (`:327`); all `atomic_rmw`
  (Add/Sub, `MemFlags::trusted()`, Release; dec carries the fence + `old==1` free path). The
  representation-containment rule (only `heap.rs` imports layout constants) means §5's
  atomicity change and §4's slot-init change are heap.rs-local. The **non-atomic emission arms
  already exist**: `nonatomic_rc_codegen_enabled()` (`heap.rs:284`, the S99
  `CRANELISP_NONATOMIC_RC` probe) branches to plain load/`iadd`/store at `:185–198`,
  `:230–243`, `:375–390`. §5 re-gates these arms; it does not write new ones.
- **The call lowering** (`src/compiler/apply.rs`) — `compile_consuming_arg_list` (`:682`;
  the caller-side Var inc at `:700–713` keyed on `signature_heap_category`),
  `compile_direct_call` (`:725`) dispatching GOT-indirect via `resolve_got_target` (`:760`) →
  `emit_got_slot_load` (`:920`: `slab_base + slot*8`, load) →
  `emit_got_indirect_call_via_data_id` (`:936`); `compile_closure_call` (`:1497`, code-ptr at
  `HeapClosure::CODE_PTR_OFFSET`). §3's elision and adaptation live here.
- **The intra-function analyses** — `compute_last_uses` (`heap.rs:695`, pre-order
  `(Symbol, Span) → is_last_use` map; callers: `fn_compiler.rs:331`, `lambda.rs:403`,
  `launch.rs:200`, `dependent_spark.rs:207`, `par_bind.rs:228`) and `HeapCategory::classify`
  (`heap.rs:545`). Both **stay below the boundary** (spine §3.3 narrowness counterweight);
  §3.3 extends the former with provenance-rooted use counting, §7 extends the latter with a
  `Value` arm.
- **The ownership sets on `FnCompiler`** — `captured_vars` / `borrowed_vars` and the
  `is_last_use` gate (`compiler/mod.rs:1204`). §3 makes `borrowed_vars` the carrier of
  `Borrowed` params and provenance-rooted projections — the spine's §8.2 subsumption made
  literal in the data structure that already enforces the discipline.
- **The Vec machinery** — inline COW: `compile_vec_set` (`vec_codegen.rs:243`; last-use split
  at `:278–306`), `compile_vec_push_cow` (`:459–544`; the **dynamic rc==1 check** at
  `:472–473` — the in-tree uniqueness-permission precedent §6 generalises); extern copies:
  `vec-set-copy` (`cranelisp-intrinsics/src/vec_runtime.rs:320–355`; retained-element inc
  loop `:337–347`), `vec-push-copy` (`:364–396`), `vec-push-grow` (`:405–437`); element fns
  passed as nullable i64 fn ptrs (`call_elem_fn` `:262`; `vec_drop` skips null `:459`) —
  §7's Vec-of-values rides exactly this null short-circuit.
- **The value-wrapper precedent** (`src/compiler/literals.rs`) — `operator_primitive_name`
  (`:238`), `compile_operator_as_value` (`:263`): a zero-capture closure over a synthesized
  `Linkage::Local` wrapper (`__wrap_op_{prim}_{disc}{span}__`, `:309–327`) whose body is a
  GOT-indirect call (`:354–378`). §3.5's R2 wrapper is this pattern applied to user functions.
- **Auto-curry** (`src/compiler/control_flow/fn_as_value.rs`) — `compile_auto_curry` (`:514`),
  `compile_auto_curry_wrapper` (`:613`), `emit_curry_target_call` (`:443`). §3.5's
  composition ruling lands at `emit_curry_target_call`.
- **The GOT** — per-module slab (`__cranelisp_got_{M}`; JIT base-ptr registration
  `jit.rs:332`, object-mode relocations `lib.rs:421`); slot allocator `allocate_got_slot`
  (`cranelisp-types/src/module.rs:608–612`, monotone `next_got_slot` `:135`); redefinition
  today = in-place `store_slot` patch (`src/process_form.rs:681–691`), documented at
  `src/session_v4.rs:262–272` (Decision 31 Scenario 2 reclaim). §8's fresh-slot path rides the
  same allocator.
- **The runtime-error machinery** (`cranelisp-intrinsics/src/panic.rs`) — thread-local slot
  (`:38`), extern `runtime/panic` = `runtime_panic(msg_ptr, msg_len)` (`:78–80`, stores the
  message, returns sentinel 0), `take_runtime_error` (`:96`), `set_runtime_error` (`:108`);
  the host checks the slot after every JIT invocation (`cranelisp_run_program` `:261`). §8's
  trap stub is a ~5-instruction client of this machinery.
- **The cache** (`src/cache/`) — `CACHE_SCHEMA_VERSION = 10` (`cache/mod.rs:201`); manifest
  validity = own `source_hash` + `dependency_hashes` + the global dims (compiler fingerprint,
  target triple, cranelift version, format version — `cache/mod.rs:25`). §2.3 adds the toggle
  to the global dims; §7.4's parity rests on the `.meta.json`-is-the-SymbolTable fact
  (`module-caching.md` §14.1).
- **The session** (`src/session_v4.rs` + scheduler) — NOT this design's to specify beyond the
  §8.3 interface; the R3 transaction orchestration's design home is `design/int/` (a later
  fire, per spine §10 item 12).

**The functions between them:** typecheck's outputs (mode vectors on `MonoDefnVariant` +
site facts on `MonoExpr` nodes + the value-use mark, per the spine §3.3 carrier design and
FIXME 0467's extension) → *(this doc's five mechanisms)* → CLIF emission deltas, all
fact-gated, all reversible to the conservative path. No new pipeline stage, no new graph, no
new store (Principle 7); one new tiny compile entry (§8.3) and one new manifest key (§2.3).

---

## §2. The master analysis-off toggle (spine §10 item 13)

### 2.1 One switch

**`CRANELISP_NO_OWNERSHIP=1`** (sibling of `CRANELISP_NO_LENIENT`; read-once `LazyLock`,
same-env-read-in-both-crates pattern already proven by `CRANELISP_NONATOMIC_RC` —
`heap.rs:284` + `rc.rs:90` read one env so a whole run is consistent). Semantics: force the
conservative point everywhere. Enforcement is **producer-primary**: with the toggle set,
typecheck's `pass5_ownership` does not run — no summaries, no site facts, no value-use marks
are produced — and by the spine's absent-summary-⇒-Decision-24 rule every consumer is at the
conservative point with zero consumer-side branching. This is the "one master switch" the
typecheck proposal's §12 item 3 requires: `confined = None`, `escapes = None`,
`mode_summary = None` all follow from the pass not running.

Default polarity: the toggle ships **before** the analysis (spine §5.7 — with analysis off,
the dev session degenerates to today's sound behaviour, which is the interim guard until the
R3 machinery lands). Once machinery + increment I land, the default is analysis-on and the
toggle is the permanent oracle switch.

### 2.2 Byte-identical-off — the structural discipline (the proof obligation)

Producer-side gating alone does not *prove* byte-identity; the backend must also be shaped so
that absent facts select **the unmodified existing code**, not a rewritten equivalent. Four
binding disciplines:

1. **Else-arm-is-the-existing-helper.** Every mechanism is introduced as a guard of the form
   `if let Some(fact) = … { <new emission> } else { <the pre-S100 helper call, verbatim> }`.
   The conservative arm is never a copied/reflowed variant of the old code (Principle 7 — the
   recurring-mirror defect class); it is the same call the site made before the change-set.
2. **No unconditional new instructions.** No mechanism may emit even a dead instruction on
   the fact-absent path (a "harmless" extra `iconst` breaks byte-identity and therefore the
   oracle). The one deliberate exception class is §8's machinery (trap stubs, fresh slots) —
   which is redefinition-path-only and emits nothing in batch or in any compile of ordinary
   code.
3. **Derived artifacts are fact-conditional.** R2 wrappers (§3.5) are emitted only for
   value-used functions with non-Decision-24 summaries — with the toggle off, no such summary
   exists, so no wrapper is ever emitted and value-use compiles exactly as today. Sibling
   extern targeting (§9) requires summary ∧ toggle — off targets the consuming exports.
4. **The differential witness is /qa's.** Part 17 carries (a) a CLIF-text equality lane:
   toggle-off build vs the recorded pre-S100 baseline over the corpus
   (`CRANELISP_CODEGEN_DUMP` text is the comparand), and (b) the observable-output
   differential lane: analysis-on vs analysis-off, byte-identical program output, plus the
   ASan/UAF and starved-inc fences (spine §9). Routed in §12.

### 2.3 Cache and ABI coherence — the toggle joins the manifest global keys

The hazard producer-side gating cannot cover: a cache written analysis-ON persists moded
summaries in `.meta.json` and `.o` machine code compiled against moded conventions; a later
analysis-OFF session loading that cache would emit Decision-24 callers against borrowed-ABI
callees — the §3.1-spine leak/double-free, arriving through the cache instead of the REPL.
**Ruling: the ownership toggle joins the manifest's global invalidation dimensions**
(`cache/mod.rs:25` family: compiler fingerprint, target triple, cranelift version, format
version). Flipping the toggle invalidates the whole cache — a full recompile, exactly as a
compiler upgrade does. This makes mixed-ABI caches unrepresentable (Principle 18/20) at the
cost of a rebuild on flip, which is the correct price for an oracle switch. One new manifest
field, backend cache submodule work — landing in **S101 (stage M, the R3-machinery sprint),
with the toggle itself**, pulled forward from increment I by the `/arch` S101 Phase-2 ruling
(recorded in `sprints/SPRINT.md` §Architecture review): pre-analysis the key is inert — no
summaries exist, both toggle polarities are byte-identical — but landing it with the toggle
means increment I's differential oracle has its cache substrate in place before the first
moded emission exists.

### 2.4 Relation to the existing probes

`CRANELISP_NONATOMIC_RC` (documented-unsound blanket probe) and `CRANELISP_CAPTURE_BORROW`
(S99 opt-in, `ring2-rc.md` §5.5.2) remain independent, off-by-default measurement toggles.
§5 *reuses* the former's emission arms under sound gating (the probe env survives as a
measurement-ceiling override, still documented-unsound); §3 *subsumes* the latter (a joined
spark capture classified `Borrowed` by the analysis gets the same elision by inference —
when increment I lands and is default-on, the S99 opt-in flag is retired in favour of the
inferred classification; its UAF/exclusion guards carry forward unchanged as the regression
fence, spine §8.2).

---

## §3. Borrow-elision emission (spine §10 item 7)

### 3.1 Caller side — `compile_consuming_arg_list` keyed off the vector

At a statically-resolved call site whose callee carries a summary, the arg loop (`apply.rs:682`)
gains a per-position mode lookup:

- **Var arg, callee param `Owned`** — today's path verbatim: `emit_rc_inc[_guarded]`
  (`:700–713`). This is also the **adaptation path** (spine §4.3): a caller holding a
  borrowed/projection-covered Var and passing it to an `Owned` param emits this same inc —
  adaptation is the default, not a new idiom. (A member of `borrowed_vars` at a consuming
  position already gets the Var inc today — no special-casing.)
- **Var arg, callee param `Borrowed`** — **skip the inc**. The caller retains ownership; its
  scope-cleanup dec is the single accounting; the callee (compiled against the same vector)
  emits no param dec. This is the elision that makes the interprocedural read path rc-free.
- **Temporary arg, callee param `Owned`** — today's path verbatim (no inc; ownership
  transfers at rc=1).
- **Temporary arg, callee param `Borrowed`** — no inc, and the caller **emits a post-call
  rc_dec** on the temporary (the callee will not dec it). Net op count equals Decision 24
  (one alloc + one dec); nothing is lost, and the emission is scoped strictly to moded
  edges — with the toggle off no moded edge exists, so the retired `dec_temporary_args`
  shape never reappears on the conservative path.

Closure-valued call sites (`compile_closure_call`), constructors, externs, platform effects:
**untouched** — permanently Decision-24 per the spine's R2/§3.1 pins. `AutoCurry` sites are
Decision-24 at the closure protocol; §3.5 covers the adapter's interior.

### 3.2 Callee side — `Borrowed` params join `borrowed_vars`

When `compile_to_module` compiles a `MonoDefnVariant` carrying `mode_summary`, each param
with mode `Borrowed` is registered in the compiler's **`borrowed_vars`** set at function
entry. Everything then follows from the existing §5.5 discipline with zero new emission
logic: no dec at `pop_scope_with_cleanup` (the caller owns the reference), never eligible for
last-use ownership transfer (`is_last_use` gate, `compiler/mod.rs:1204`), passed onward to an
`Owned` position ⇒ the ordinary Var consuming inc fires (§3.1's adaptation). This is the
spine §8.2 subsumption made literal: the general analysis' `Borrowed` param is *implemented
as* the discipline `borrowed_vars` already enforces for match-arm field bindings.

**Invariant (assertable):** a `Borrowed` param never reaches the return path — the analysis
widens any returned/escaping param to `Owned`/`AliasOf` before the summary is emitted
(typecheck §3.3/§4.2 rule 5). The backend may `debug_assert!` this at
`return_var_in_scope`/`protect_return_value` time; it never needs an emission rule for it.

### 3.3 Result modes and provenance — the `compute_last_uses` extension

Consuming the typecheck proposal's §4.2 rule 4 + FIXME 0467's result mode:

- **`ResultMode::Fresh`** (and absent-summary default): today's handling verbatim — the
  result is an owned rc=1 temporary.
- **`ResultMode::AliasOf(i)`**: emission-neutral for the caller (the result is an owned
  reference flowing through); the value of the fact is analysis-side. No backend change.
- **`ResultMode::ProjectionOf(i)`**: the call's result is a **borrowed view rooted at the
  root of argument i**. The caller binds it into `borrowed_vars` with a provenance root read
  from the site facts (typecheck §2.3 — the backend never recomputes interprocedural
  provenance). No dec at scope exit; escape edges materialize (one `rc_inc` at the edge —
  the §4.2-rule-5 idiom, same shape as §3.1's adaptation inc).
- **Projection sites in-frame**: `compile_vec_get` (`vec_codegen.rs:145`) today
  unconditionally incs a heap-typed element read; under a `Borrowed`-rooted site fact the inc
  is skipped and the binding joins `borrowed_vars` with the vec's root. Match-arm field
  bindings already do exactly this (`borrowed_vars` as-built). Accessor calls are covered by
  the `ProjectionOf` result case above.

**The `compute_last_uses` extension (typecheck §12 item 2, the one owed analysis change):**
`collect_var_uses` (`heap.rs:729`) gains a provenance map (binding → frame-local root, from
the site facts): every use of a provenance-carrying binding **also records a use of its
root at that span**. Consequences, both load-bearing: (a) the root's last use — hence its
release and its inline-COW `is_vec_last_use` eligibility — orders after the last use of
every projection rooted in it (without this, §4.2-rule-2 projections recreate the Sprint-61
aliased-COW regression one level up); (b) borrowed projections themselves are never last-use
candidates (already guaranteed by `borrowed_vars` membership). The extension is one map
parameter + one extra append per use — `compute_last_uses` stays a single pre-order walk.

### 3.4 The adaptation algebra — one helper, three consumers

The per-edge delta between Decision-24 and a moded convention is mechanical (typecheck §8.3):
per param `Owned→Borrowed` ⇒ post-call dec of the received-owned arg; result
`ProjectionOf→Fresh` ⇒ materialization inc; everything else pass-through. This is factored
as **one emission helper** (illustrative name `emit_d24_adaptation(summary, args, result)`),
consumed by exactly three sites: the R2 value wrapper body (§3.5), the auto-curry target
call (§3.5), and — degenerately, as the single pre-call inc — extern adaptation sites
(§9.3 / typecheck §9.2). One algebra, three consumers, no per-site reinvention
(Principle 7).

### 3.5 The R2 wrapper — emission, caching, auto-curry composition (typecheck §8.4 owed items)

The typecheck proposal rules the mechanism (§8.2 there: moded native body on the GOT slot +
lazily-synthesized Decision-24 value wrapper; join-to-Owned rejected). The codegen half:

- **Emission site.** The fn-as-value paths (`fn_as_value.rs`; the zero-args-applied
  `compile_trait_method_as_value` family) and `compile_operator_as_value` (`literals.rs:263`)
  are the precedent and the location: when compiling a value-use of a callable whose entry
  carries a **non-trivial summary** (any param non-`Owned`, or result non-`Fresh`), the
  backend synthesizes a `Linkage::Local` adapter function and wraps it in a zero-capture
  closure exactly as the operator wrapper does. Adapter body: accept every param Owned
  (closure protocol), GOT-indirect call through **the function's own slot**
  (`emit_got_slot_load`, `apply.rs:920` — late binding for ABI-preserving redefinitions is
  preserved), then `emit_d24_adaptation` (§3.4), return. Summary-trivial functions synthesize
  the closure directly over the body as today — zero new artifacts (the lazy-emission
  condition, typecheck §8.2).
- **Naming/caching.** Wrapper name **`__d24wrap_{fq}_{slot}__`**. Keying on the GOT slot
  makes ABI-epoch handling automatic: slot identity IS ABI identity (spine §5.6), so an
  ABI-changing redefinition (fresh slot) yields a fresh wrapper name, while stale closures
  built over the old wrapper keep dispatching through the frozen old slot — old-world
  consistency with no epoch counter of its own. Within a compile unit, `declare_function`
  is idempotent by name (the operator-wrapper dedup model); across modules, duplicate
  wrappers are benign (stateless, byte-identical — same as duplicated elem fns and operator
  wrappers). Wrappers are emitted into the compiling module's object ⇒ deterministic,
  `.o`-cache-safe (slot numbers are persisted and load-bearing, spine §5.6).
- **Auto-curry composition — compose, don't stack.** `emit_curry_target_call`
  (`fn_as_value.rs:443`) emits the saturated call when a curried chain completes. When the
  target carries a summary, that call is statically resolved: the curry wrapper consumes the
  summary **directly** — GOT-indirect to the moded body + `emit_d24_adaptation` inline —
  rather than routing through the `__d24wrap_…` value wrapper (which would stack two
  adapters and pay the algebra twice). The curry wrapper *is* the Decision-24 adapter for
  its chain; the value wrapper is the Decision-24 adapter for direct closure use; both are
  emissions of the same §3.4 algebra.
- **The invariant this half makes true** (typecheck §8.3 item 3, for `/review`): *every code
  pointer reachable from a closure value targets a Decision-24-conformant entry; moded
  bodies are reachable only through statically-resolved call sites and adapters.* The
  emission discipline above is the entire enforcement — there is no other path that takes a
  moded body's address.

---

## §4. Stack/region mechanics for `NoEscape` (spine §10 item 8)

### 4.1 Increment I — Cranelift stack slots for the statically-sized, scalar-payload class

Today the backend stack-allocates nothing (sole `create_sized_stack_slot` use: the trace
scratch array, `trace_codegen.rs:1136`); every value lives in SSA or on the RC heap. The
increment-I mechanism: at a backend-emitted allocation site (`ConstrADT` constructor,
`Lambda` closure, `VecLit` struct+buffer) whose node carries `escapes = Some(false)`, replace
`emit_alloc` with `create_sized_stack_slot` + `stack_addr` + header init. Eligibility gates,
all backend-local and all conservative-by-default:

1. **Statically sized** — ADT nodes (`HeapAdt::payload_size(n_fields)`), closures
   (`HeapClosure::payload_size(n_captures)`), `VecLit` (struct 40B + `len*8` buffer). Nothing
   dynamically sized in I.
2. **All-scalar payload** — no heap-typed fields/captures/elements in the first landing. A
   stack aggregate holding heap-typed field references would owe a frame-exit field release
   (its drop glue never runs — §4.2); rather than design that release path now, increment I
   ships the zero-obligation class and the heap-field extension is staged behind
   measurement. (With §7's flattening, "scalar payload" grows to include `Value`-classified
   fields — the two mechanisms compound.)
3. **Not reachable by a TCO back-edge** — an allocation inside a TCO loop body whose value
   can flow into the loop-header params outlives its *iteration* while the escape fact is
   per-*frame*; the slot would be reused under a live reference. Backend-local gate: a
   stack-eligible site inside a TCO loop body is disqualified if its value flows into the
   recur args (a small local flow check on the loop body; when in doubt, heap). This is an
   emission-side sharpening of the fact, not a widening — always sound to decline.
4. **Extern-produced values are ineligible by construction** — Rust bodies allocate via
   `alloc_with_rc`; the backend cannot redirect them without an allocator seam. That seam is
   §4.4's region arena (increment II, the (a)-coupling).

### 4.2 The immortal header — why residual RC traffic is harmless by construction

Stack slots keep the standard 16-byte `HeapHeader`, with **`rc` initialized to an immortal
sentinel** (`IMMORTAL_RC`, e.g. `1<<62`). Rationale (Principle 20 — model the invariant by
representation): a `NoEscape` value still meets RC-emitting code — adaptation incs at
`Owned` handoffs to summarized callees, callee-side consuming decs, guarded ops on `Mixed`
positions, `emit_vec_drop_if_temporary`'s rc-checked dec (`vec_codegen.rs:588`), the inline
COW's rc==1 probe (`:472–473`). With the sentinel:

- inc/dec are harmless drifts on a frame-local cell (never contended — the frame is
  thread-local; joined-spark borrows read, they don't hold RC ops on it, else the cell
  wasn't `Confined`/`NoEscape` in the first place);
- the free path is unreachable (`old == 1` cannot fire under any bounded op count), so
  `dealloc` is never called on a stack pointer;
- the COW unique check (`rc == 1`) is never satisfied, so `vec-push-grow` (which frees the
  old buffer — lethal on a stack buffer) is unreachable; writes to a stack vec take the
  copy path to a fresh heap vec, which is correct and conservative.

No call-site anywhere changes for stack-ness; the entire existing RC/COW machinery composes
untouched. The one cost: stack vecs never mutate in place (the sentinel defeats the COW fast
path) — so the emission heuristic **declines stack allocation for vecs with `vec-set`/
`vec-push` uses in-frame** (they are better served heap-allocated + §6 reuse). Scalar-read
vecs (the lookup-table shape) stack-allocate cleanly.

Scope-exit: no dec is emitted for stack bindings (nothing to release; payload is scalar by
gate 2). `pop_scope_with_cleanup` skips them via a per-binding stack-ness mark — the same
mechanism that already skips consumed and borrowed bindings.

### 4.3 ParBind-arm and spark interaction

A joined spark reading a parent-frame stack slot through a borrowed capture is sound by the
same structural argument as capture-by-borrow (`ring2-rc.md` §5.5.2.3: the parent frame is
live across spark→join). The classification side is typecheck's (suspension crossings are
escape edges, spine R6 — a capture flowing into a deferred continuation or `LaunchContinue`
is `Escapes` and never stack-allocates); the backend consumes the per-site verdict and adds
no strand reasoning of its own. Allocations *inside* a spark thunk body are ordinary — the
thunk is a separately compiled fn whose frame lives on the worker's stack.

### 4.4 Increment II — the region arena (M7's shape, shared tier)

The aggregate mechanism (`release-llvm-backend.md` M7, encapsulated, landed on the shared
tier per spine §3.4): group `NoEscape` allocations of a common structurally-visible lifetime
— a `let` body, a `Match` arm, a `ParBind` arm — into one bump arena freed at the lifetime's
exit. This is where dynamically-sized allocations and (via a thread-region handoff the
allocator axis must co-design — the S99 (a)/(b) coupling) extern-reached allocations become
eligible. Design pins made now so increment I doesn't preclude it: (i) the arena consumes
the same per-site escape facts — no new boundary input (M7 is aggregation, backend-local);
(ii) arena'd values carry the same immortal header discipline as §4.2 (one sentinel, two
backing stores); (iii) a `ParBind`-arm arena is created by the spark thunk and freed by the
joining parent **after** the join (the arm's result, which escapes the arm by construction,
is heap-allocated as today). Detail deferred to the increment-II design pass with F-series
data.

---

## §5. Non-atomic RC for `Confined` (spine §10 item 9)

### 5.1 The mechanism is already written — re-gate it

The S99 probe left the backend with complete non-atomic emission arms in the SSOT:
`heap.rs:185–198` (inc), `:230–243` (inc_guarded), `:375–390` (dec_guarded) — plain
load/`iadd`(/`isub`)/store replacing `atomic_rmw`. Today they are selected by the
process-global `nonatomic_rc_codegen_enabled()` (`heap.rs:284`), documented unsound above
one worker. The increment-I change: the emit helpers gain an atomicity input —
`emit_rc_inc(…, atomicity: RcAtomicity)` (or sibling entry points; `/dev`'s call) — derived
**per site** from the node's `confined` fact: `Some(true)` ⇒ the existing non-atomic arm,
`Some(false) | None` ⇒ atomic, verbatim today. Soundness rests entirely on typecheck's
op-wise per-cell join (typecheck §5: a cell is `Confined` only if **every surviving RC op on
it, across all reachable frames**, runs on the owning strand — so mixed emission cannot race:
non-atomic ops only ever exist on cells with no concurrent ops). The backend consumes the
verdict; it performs no strand reasoning (the narrowness counterweight).

The `CRANELISP_NONATOMIC_RC` env survives as a measurement-ceiling override (what would we
gain if *everything* were confined), still documented-unsound, still excluded from the
canonical run. The sound mechanism and the probe share the same emission arms — one
non-atomic code path, two gates (Principle 7).

### 5.2 Increment-I scope: inline ops; the shared-helper inventory stays atomic

The per-site fact can gate only ops emitted **at a site**. Ops emitted inside shared
artifacts have no site identity and stay atomic in increment I — named exhaustively so the
scope is honest:

| Shared artifact | Where | Why it stays atomic in I |
|---|---|---|
| Vec element inc/dec fns | `build_elem_inc_fn`/`build_elem_dec_fn` (`vec_codegen.rs:723/:805`; cached per module by name `:735`) | one fn per (guardedness, elem type) serves every vec of that shape; per-cell atomicity would need per-atomicity variants passed per call site — an increment-II follow-up if data demands |
| The Rust-side copy loops | `vec-set-copy`/`vec-push-copy` retained-element incs (`vec_runtime.rs:337–347/:381–385`), `rc_inc`/`consume_shallow` (`rc.rs:267/:202`, `AtomicI64` fetch ops) | inside extern bodies; per-call atomicity would need dual extern variants (§9's sibling pattern could carry it in II). **This is the S99 170M term — and it is cured by Q4/Q5 (§6/§7), not by Q3**, exactly as the spine states |
| `emit_vec_rc_dec_with_drop` | `vec_codegen.rs:1214` — ungated `atomic_rmw` today | gains the same per-site atomicity input as the heap.rs helpers (it is emitted per site, so it CAN be gated — the one inventory item that moves in I) |
| Drop-glue bodies | closure drop glue, ADT drop glue fns | shared per type; same disposition as elem fns |

The increment-I win is therefore the **inline population**: consuming-arg incs, scope-cleanup
decs, capture incs, match-field incs, materialization incs — which is where the F2
shared-board read shape's surviving ops live (typecheck §5.3: the spark side is rc-op-free
under §3; the parent-side ops are exactly these inline ops).

### 5.3 The free path

The non-atomic dec keeps the `old == 1` → drop-glue → `runtime/dealloc` sequence, minus the
Acquire fence (single-strand cells need no publication ordering — the existing non-atomic
arm at `heap.rs:375–390` already embodies this). `Transferred` is collapsed to `Crossing` at
emission in increment I (typecheck §5.4 ruling) — no backend work; if promoted later, the
promotion arrives as more `Some(true)` verdicts through the same gate, zero emission change.

---

## §6. Reuse tokens / drop-guided reuse (spine §10 item 10 — increment II)

All of §6 is increment II. Binding constraint restated from spine §3.5: **reuse tokens are
function-local values, never params, never returns, never fields** — increment I's ABI is
unaffected by anything here.

### 6.1 The token mechanism

Perceus drop-guided reuse, generalising the inline-COW precedent. At a **drop site** — a
last-use consuming dec of a value whose concrete layout matches a **downstream allocation
site** in the same function (same `alloc_size` class; layout eligibility is static per
instantiation, decided from the mono types — typecheck §7.3's eligibility axis):

```
token = (load rc(ptr) == 1) ? ptr : 0     ; in place of the dec's free path
…
at the allocation site:
  brif token != 0, reuse_block(token), alloc_block
  reuse_block: reinit header/tag/fields in place   ; no alloc, no free
  alloc_block: emit_alloc as today                 ; plus the deferred dec of the
                                                   ; non-unique original
```

The token is an SSA `Value` threaded by the compiler between the two sites (both in-frame by
construction). The shared case pays one extra branch; the unique case saves a
dealloc+alloc pair and — for constructors — the field re-inc traffic. The pairing analysis
(which drop feeds which alloc) is intra-function, greedy, and conservative: no pair ⇒ today's
code, monotone-sound.

### 6.2 Bulk ops — the entry-check placement ruling

The typecheck proposal's §7.1 frames three mechanisms; the emission half ruled here:

- **Placement: per-call entry check, never per-write.** The as-built inline COW is already
  the correct shape: `compile_vec_push_cow`'s single rc==1 probe (`vec_codegen.rs:472–473`)
  selects in-place vs copy **once per call**. The adaptive loop property follows without any
  loop-level machinery: the first write on a shared vec copies (one COW), the fresh copy is
  rc==1 by construction, every subsequent write in the chain hits the in-place arm — copy
  once, then in-place, per uniqueness epoch. No hoisted per-loop check is emitted in the
  first landing; the measured cost of the per-call probe (one uncontended load+cmp against
  the 81-inc copy it replaces) does not fund one.
- **What increment II actually changes at the vec sites:** today the inline COW is gated on
  `is_vec_last_use` (compile-time) ∧ rc==1 (dynamic). Q4 widens the *static* gate — a
  `unique_static` site fact or a caller-chained proof (typecheck §7.2) admits the in-place
  arm where last-use alone was too weak, and elides the dynamic check where the proof is
  total. The dynamic check remains the general discriminator (R4); a failed check takes
  exactly today's copy path — no regression possible.
- **The static proof's emission value is check-elision + chaining**, not a second body:
  uniqueness-specialized duplicate bodies (mode-in-key) stay out per typecheck §7.3 pending
  increment-II data.

### 6.3 Cost model of the dynamic rc==1 check

Uncontended atomic load + compare + branch: single-digit cycles, in the shadow of the call
it guards. Against it: the in-place hit saves (for the S99 grid shape) one 81-slot buffer
alloc + 81 retained-element incs + one buffer free per write. The check is cheap enough that
the design point is *where it can be elided* (static proof), not *whether to emit it*. The
failure mode to fence (routed to `/qa`): a reuse fired on a non-unique value is heap
corruption of the S98-bug-#2 family — the differential + ASan lanes and a
starved-inc-style regression fence on the reuse emission are mandatory (spine §9).

---

## §7. R5 value-representation flattening (spine §10 item 11 / §6.3 — increment II, designed now)

Increment II ships it; increment I must not preclude it. The design, with the increment-I
compatibility checklist at the end.

### 7.1 The `HeapCategory` arm and the classification single-source

`HeapCategory` (`heap.rs:523`) gains a fourth arm: **`Value`** — the concrete type is
represented inline (no header, no refcount, no drop glue; RC treatment = none, same row as
`NeverHeap` but with constructor/field structure preserved for construction and match).
Eligibility per concrete type: **Copy-eligible** (scalar, or an ADT/Vec whose fields are all
transitively `Value`/scalar) **∧ within the size bound (§7.2) ∧ single-constructor** (a
multi-ctor ADT needs a tag word alongside the payload — excluded from the first landing;
`Mixed`-style tag-in-value is a designed extension, not a day-one case).

**The single-source obligation (FIXME 0468, filed with this doc, `target: /arch`).** Two
consumers must agree on this predicate or the system is unsound: typecheck's `Copy` mode
classifier (typecheck §2.2 — a `Copy`-moded param whose representation is *not* flattened
would be pointer-copied without an inc) and the backend's layout decision (`classify`).
Both are deterministic pure functions over the type defs, but two independently-maintained
implementations of a soundness-coupled predicate is exactly the Principle-7 mirror-defect
class. FIXME 0468 asks `/arch` to place one predicate where both crates consume it (natural
candidate: `cranelisp-types` beside `HeapHeader`, landing with the R5-increment carrier
change-set; until then the spine's rule stands — the `Copy` point is inhabited by scalars
only, and `classify` has no `Value` arm).

### 7.2 The ABI/size-bound ruling — one word first

**Ruling: the first landing bounds flattened values at one word (8 bytes).** Every ABI
surface in the system is uniformly i64 today — params, returns, Vec slots, ADT fields,
closure captures, GOT-dispatched signatures. A one-word `Value` type **is** its word: it
passes in registers, sits in Vec slots and ADT fields, and crosses every existing boundary
with **zero ABI change anywhere** — no boxing-at-edges machinery, no multi-slot parameter
lowering, no platform-ABI questions. What it covers: single-field single-constructor
wrappers over scalars — `(Cell Int)`, newtype indices, the FIXME-0416 bitmask-domain shape.
On the S99 workload this is the whole prize *if* the exemplar's `Cell` is (or is refactored
to) a scalar-payload wrapper: an 81-slot `Vec Cell` becomes physically an 81-slot `Vec Int`
— copies are `memcpy`, the ~170M `rc_inc` term is zero ops, independent of uniqueness.

**Multi-word flattening is the designed extension, deferred with a named trigger.** Shape:
Vec element stride becomes `size_of(T)` (vec runtime fns gain an `elem_size` param);
`vec-get` returns by-value multi-slot; params/returns box at word-sized edges (the
boxing-at-edges answer applies *only* here, where it buys multi-word aggregates in
registers-vs-heap trade). Trigger: an F-series fixture whose hot type is Copy-eligible but
>8 bytes after increment II's first landing. Until then, >1-word Copy-eligible types stay
heap + RC-share — sound, just unflattened.

**The Mixed-guard interaction, checked:** a flattened value is an arbitrary i64 and must
never meet a `<1024` nullary-tag guard as if it were tag-or-pointer. It cannot: post-mono
classification is total (no `Type::Var` reaches codegen — `ring2-rc.md` §1.6), a `Value`
type classifies as `Value` at every site, and a `Value` typed field inside a heap ADT is
skipped by drop glue exactly as `NeverHeap` fields are. The unsound-`Mixed` path R5 would
otherwise have to fear was already retired by S84/FIXME 0375.

### 7.3 Vec-of-values — the mechanism already exists

The element inc/dec fn pointers passed to the vec runtime are **nullable, and null already
means "no per-element RC"** (`call_elem_fn` skips null, `vec_runtime.rs:262`; `vec_drop`
skips null `:459`) — this is how `Vec Int` works today. A `Vec` of one-word `Value` elements
is emitted with null elem fns and behaves byte-for-byte like `Vec Int`: `vec-set-copy`'s
copy loop does no incs, `vec_drop` walks nothing. **Zero new runtime code** for the
one-word bound; the entire change is classification (§7.1) driving the existing null-elem-fn
emission plus constructor/match lowering of the wrapper type to bare-word moves.

### 7.4 `.o`-cache and `--link` parity

Layout is a function of (type defs, size bound, toggle) — all deterministic: type defs ride
the persisted `.meta.json` (the serialised `SymbolTable`, `module-caching.md` §14.1) and are
chain-followed to one defining module, so every importer classifies identically; the size
bound is a compiler constant; the toggle is a manifest global key (§2.3). Therefore two
compiles of the same cache-valid inputs make the same flattening decisions — the same
argument that already covers ADT tag/field layout (survey: `is_mixed_adt`/`ctor_field_count`
read the symbol tables; restoring the same `.meta.json` reproduces identical layouts).
Landing R5 is a representation change to compiled code ⇒ **`CACHE_SCHEMA_VERSION` bump in
the landing change-set** (the standard discipline, `cache/mod.rs:201`), which wholesale-
invalidates every pre-R5 `.o`. `--link` needs nothing further: closed-world, single compile,
one classifier.

### 7.5 Trace/display descriptors

`bake_descriptor_blob` (`trace_codegen.rs:596`) walks types into self-contained
`DisplayDescriptor` arenas. R5 adds a descriptor arm: *inline value with constructor name* —
render `(Cell 5)` from the raw word (payload formatted per its scalar kind) without a
dereference. The baker reads the same §7.1 classification; `/platform`'s schema generator
(which shares the descriptor closure-walk, `platform-interface.md`) inherits the arm when
platform-visible types ever flatten (none do in the first landing — platform ABI edges stay
Decision-24/boxed per the spine's boundary pins).

### 7.6 What increment I must not preclude (compatibility checklist)

- `HeapCategory` consumers must keep matching non-exhaustively-safe (a new arm compiles into
  every `match classify(…)` — `/dev` keeps these matches total-by-construction, no
  wildcard-`Mixed` collapses).
- §3's mode plumbing carries `Copy` as a no-op row from day one (a `Copy` param emits no
  inc, no dec, no borrowed_vars entry — for scalars this is already true structurally).
- §4's stack slots and §6's reuse tokens are layout-agnostic (they key on `alloc_size` and
  site facts, not on category identity) — flattening removes candidates from their input
  sets, never invalidates their emission.
- No increment-I code may assume "heap-typed ⇔ has header" for *fields read through match*
  beyond what `classify` says — which is already the discipline.

---

## §8. The R3 machinery's backend half (spine §10 item 12; §5.5–§5.6)

Sequenced per spine §5.7: lands **before or with** increment I's ABI-bearing modes. The
session-orchestration half (transaction, reverse index, cascade reporting, file-watcher
interplay) is `/int`'s, design home `design/int/` (a later fire); §8.3 states the interface
this crate exposes to it. FIXME 0466 (rejected slot reclamation) is respected — nothing here
reclaims holes; the persistence pins (spine §5.6: faithful `.meta` writes, load-bearing slot
numbers, holes persist, `next_got_slot` high-water = freeze boundary) are inherited, not
restated.

### 8.1 The trap-stub mechanism — RULING: per-symbol stub over the existing raise machinery, no new intrinsic

The §5.5-spine choice ("one intrinsic + baked message vs per-symbol stub emission") dissolves
on inspection of the as-built error machinery: JIT code already raises a clean runtime error
by calling the extern **`runtime/panic`** (`runtime_panic(msg_ptr, msg_len)`,
`panic.rs:78–80`) — it stores the message in the thread-local slot and returns the sentinel;
the host surfaces it via `take_runtime_error` (`:96`) after the invocation, in every mode.
A single shared intrinsic *cannot* carry per-symbol provenance (the GOT slot holds one bare
code pointer; callers pass ordinary args; there is no side channel to say *which* broken
symbol was hit). So:

**The trap stub is a per-symbol emitted function of ~5 instructions:**
`iconst msg_ptr; iconst msg_len; call runtime/panic; return sentinel(0)`.

- **Args untouched** — the stub never reads its argument registers, so one stub body is
  signature-safe for any arity/type vector, which is precisely what makes the **in-place
  slot patch** on the BROKEN symbol's existing slot sound (spine §5.5: existing unrecompiled
  callers must reach the trap through the slot they already embed). Concretely: the stub
  **compiles with signature `() -> i64`** (zero declared params, one I64 return). This is
  well-defined against a caller's imported N-arg signature under the uniform all-I64
  convention on both supported ABIs (SysV x86-64 / AAPCS64): register-passed args are
  caller-owned scratch the stub never touches, stack-passed args (arity > 8) are
  caller-cleaned in both conventions, and the sentinel comes back in the single return
  register.
- **The message** is the session-composed provenance string
  (`g is broken by the redefinition of f: <original error>`) — UTF-8 bytes, **no NUL
  terminator** (`runtime_panic` takes an explicit `(ptr, len)` pair) — session-owned memory,
  its address and length baked as `iconst`s. No JIT data section needed. **Lifetime
  contract on the caller (`/int`):** the string must live **exactly as long as the returned
  `Code` retention handle**, stored paired with it in the session pool ("until the symbol
  recompiles" understates it — a broken symbol later recovered with a *new* ABI freezes its
  old slot pointing at the stub permanently, so in that path string and handle live to
  session end). The pairing design is the `design/int/` fire's, checklist item (i) per the
  `/arch` S101 Phase-2 review; the backend's obligation is only that the baked pointer is
  never read after the `Code` handle drops.
- **RC-mid-panic caveat, carried:** the caller has already emitted consuming incs for its
  heap args when the trap fires; the raise path releases none of them — one leaked reference
  per trap invocation. This is the same caveat class as every runtime panic
  (`sprint19-panic-boundary.md`; the test-discovery design carries it identically) —
  dev-session-bounded, documented, acceptable. Not a new hazard: `runtime/panic` callers
  today leak identically.
- **Cost:** one tiny per-symbol JIT compile per cascade-broken symbol (per-symbol JIT
  cardinality is the Decision-41 norm), retained via the same `Code::Jit` handle discipline
  as any compiled symbol.

### 8.2 Fresh-slot allocation and frozen-slot retention

- **Fresh slots ride the existing allocator.** An ABI-changing redefinition allocates via
  `allocate_got_slot` (`module.rs:608–612`) — the same monotone path every new definition in
  a live session already takes; the rebuilt entry carries the new slot on its callable
  `DefKind`; recompiled callers embed it through the unchanged `emit_got_slot_load` path.
  **No backend emission change is needed for slot versioning**: the backend already compiles
  against whatever slot the entry carries. The ABI-preserving fast path stays the in-place
  `store_slot` patch (`process_form.rs:681–691`) as today.
- **Inherited invariant to verify at implementation (flag for `/dev`, not a design fork):**
  the per-module GOT slab's base address is baked into finalized machine code (via the
  `__cranelisp_got_{M}` data-symbol resolution), so the slab must not move for the session's
  lifetime while `next_got_slot` grows. Live sessions already grow `next_got_slot`
  continuously (every new REPL definition), so the as-built `GotTable` necessarily satisfies
  some form of this; the R3 change adds no new growth *kind*, only more growth *events*.
  `/dev` confirms the slab's growth/pre-sizing story before enabling fresh-slot churn, and
  the `GotObserver` (FIXME 0099) is the observability hook for slot-allocation events.
- **Frozen-slot retention extends Decision 31 Scenario 2.** Today the superseded entry's
  `Code::Jit(Arc<Jit>)` drops on replacement and `free_memory` fires
  (`session_v4.rs:262–272`). Under slot versioning, an ABI-changing replacement instead
  moves the superseded `Code` into a **session-held retention pool** — the `kept_dlls`
  precedent exactly (`session_v4.rs:290`: a `Mutex<Vec<…>>` never drained, session-lifetime,
  documented leak-by-design). Illustrative: `frozen_code: Mutex<Vec<Code>>`. The pool is
  `/int`-owned state (it lives on the session); the backend's contribution is nil beyond the
  `Code` type already being cloneable/retainable. Restart reclaims everything (spine §5.6:
  frozen-slot bindings die with the session; the persisted high-water mark keeps new
  sessions above every cache-referenced slot).

### 8.3 The interface exposed to `/int` (stated, not designed here)

Three calls, two of which exist:

1. **`compile_to_module`** — unchanged; the transaction's recompile executor calls it per
   affected symbol exactly as the priority workers do today.
2. **`compile_trap_stub(msg_ptr: *const u8, msg_len: usize) -> Result<(ptr, Code), CompilationError>`**
   — NEW, tiny: emits the §8.1 stub into a fresh per-symbol `Jit`, returns the code pointer
   (for the session to `store_slot` onto the broken symbol's existing slot) and the `Code::Jit`
   retention handle (for the session's entry/pool). Approved as shaped by `/arch` (S101
   Phase 2); implementation pins: the returned `ptr` is **`*const u8`** — exactly what
   `store_slot(slot, ptr: *const u8)` (`cranelisp-types/src/got.rs:135`) consumes;
   `CompilationError` is the crate's existing facade error type (the same one
   `compile_to_module` returns); the fresh `Jit` is constructed through the standard
   per-symbol path, so **`runtime/panic` resolves through the ordinary intrinsics
   registration** (`register_intrinsics` → `JITBuilder::symbol`, `jit.rs:93–97`) with no
   bespoke symbol wiring — per-symbol JIT cardinality is the Decision-41 norm. This is the
   one public-surface addition of the R3 backend half — a backend `public-api.txt` diff at
   the implementing change-set, flagged for `/arch` per the baseline-diff discipline.
3. **`got().store_slot` / `allocate_got_slot`** — existing; the session patches and allocates
   as today. Freeze semantics are session bookkeeping (never rebind a frozen slot), not a GOT
   mechanism.

Everything else the spine's §5.3–§5.5 names — the reverse index, the summary-diff gate, the
affected-set closure, reverse-topo ordering, cascade reporting, BROKEN-state bookkeeping,
`/info`//`sig` surfacing — is session/scheduler territory: `design/int/` + `repl/spec.md`
(the spine's §11 already routes the `/repl` normative half to that implementing sprint).

---

## §9. The dual-symbol extern convention (spine §10 item 14 / §3.1(b) — optional, increment I ships one instance)

### 9.1 The Rust-side authoring pattern

For a hand-audited extern whose declared fact table (spine §3.1(a); typecheck §9) marks a
param only-read, a **borrowed-convention sibling symbol** is published alongside the
untouched consuming export. Naming: **`<name>$borrowed`** (`$` is the established mangling
namespace — `add$Int+Int` — unreachable from the reader). Authoring shape — one core, two
exports, so the two bodies cannot drift (Principle 7):

```rust
fn str_len_core(s: i64) -> i64 { /* read length; no RC effect */ }

#[unsafe(export_name = "str-len")]           // consuming export — UNTOUCHED
pub(crate) extern "C" fn str_len(s: i64) -> i64 {
    let n = str_len_core(s);
    rc::consume_shallow(s);                  // the existing Decision-24 dec
    n
}

#[unsafe(export_name = "str-len$borrowed")]  // borrowed sibling — core only
pub(crate) extern "C" fn str_len_borrowed(s: i64) -> i64 { str_len_core(s) }
```

Registration differs by family, both mechanically trivial (survey-confirmed):

- **Primitives-crate shims** (the string family's home): the sibling registers as an
  additional slot in the static primitives table — `insert_primitive_entry`'s shape
  (`cranelisp-primitives/src/lib.rs:223–244`): allocate a slot, `store_slot` the sibling's
  shim pointer (harvested by `extern_shims()`, `:340`). The sibling entry is
  non-user-resolvable by its `$` name; the backend reaches it via the primitive entry
  carrying a `borrowed_sibling_slot` alongside its declared facts (a detail of the
  fact-table carrier, FIXME 0467's family — no separate design needed).
- **Intrinsics-table symbols**: one more catalog record in `intrinsics_table()`;
  `register_intrinsics` (`jit.rs:93–97`) binds it like every other name; the backend emits
  `Linkage::Import` calls against the sibling name.

### 9.2 Increment-I sibling list — RULING: the pattern plus exactly one template instance, `str-len`; `vec-len` is NOT a candidate

The spine assigns this item a when-worth-it data burden (the dominant S99 term is cured by
Q4/R5, not by convention). Applying the criteria — heap-typed param ∧ only-read ∧ an
adaptation inc/consuming dec **pair actually paid at statically-resolved sites**:

- **`vec-len` — NO, correcting the spine's illustrative example against source.** The spine
  names `vec-len` as the §3.1(b) example, but at statically-resolved sites `vec-len` is
  **inline-lowered** (`compile_vec_len`, `vec_codegen.rs:136` — a direct `LEN_OFFSET` load;
  named-`Var` args are skipped by `emit_vec_drop_if_temporary`, so a borrowed `xs` at
  `(vec-len xs)` pays **zero** RC ops today). Its extern shim (`vec::vec_len`, the one
  vec-query-family member with a populated GOT slot — `cranelisp-primitives/src/lib.rs:
  256–262`) serves only the Decision-24 **value path**, which R2 pins to the consuming
  convention permanently. There is no pair to elide; a sibling would be dead weight.
  `vec-len`'s increment-I role is entirely the §3.1(a) **fact-table** row (analysis input —
  keeping `xs` un-poisoned), which is typecheck §9's, not this section's. The spine-side
  example correction is filed as **FIXME 0469** (`target: /arch`).
- **`str-len` — YES, as the single template instance.** The simplest audited only-read
  consuming extern (one heap arg, `rc::consume_shallow` — ring2-rc §3.3): a borrowed `s`
  reaching `(str-len s)` today pays the §3.1-adaptation inc + the extern's consuming dec per
  call. Chosen to validate the pattern end-to-end (shared-core authoring, sibling
  registration, fact-table linkage, the §9.3 gate, byte-identity-off), not on a measured
  win — no current fixture makes string calls hot, and that is stated honestly.
- **The rest of the string family, `eq`, `display`/`trace` — DEFERRED, data-gated.** Each is
  one mechanical application of the §9.1 template when `CRANELISP_RC_STATS` attribution
  (extended per-extern — a `/qa` part-17 lane) shows an adaptation-pair population worth
  deleting. The pattern ships in increment I; the population grows by measurement.

### 9.3 The emission gate

At an extern call site the backend targets the sibling iff **(declared fact: param
only-read) ∧ (the arg is borrowed/projection-covered at this site) ∧ (a sibling is
registered) ∧ (toggle on)** — then: no adaptation inc, call `<name>$borrowed`. Any leg
false ⇒ the consuming export with today's emission (plus the §3.1 adaptation inc when the
arg is borrowed) — which is also, verbatim, the toggle-off path, preserving §2's
byte-identity (the consuming export is never edited, so even the *Rust* side is
byte-identical off). `ring2-rc.md` §3.3's audit table gains a "borrowed sibling?" column at
the landing change-set — the audit remains the single registry of extern RC behaviour.

---

## §10. What ships when — and what must not ship

**Increment I (with, or after, the §8 machinery per spine §5.7):**
§2 toggle + manifest key (pulled forward — land S101 stage M alongside §8, `/arch` Phase-2
ruling, §2.3); §3 borrow-elision (caller skip-inc, `borrowed_vars` params,
result-mode consumption, `compute_last_uses` provenance extension, adaptation algebra, R2
wrapper + curry composition); §4.1–§4.3 stack slots (immortal header, scalar-payload class);
§5 confined-gated non-atomic inline RC (+ gating `emit_vec_rc_dec_with_drop`); §9's authoring
pattern + the `str-len` template sibling.

**Increment II:** §6 reuse tokens + the widened vec write path; §7 value flattening
(one-word bound) + `CACHE_SCHEMA_VERSION` bump; §4.4 region arena; §5's shared-helper
atomicity variants and §9 sibling expansion **only if** F-series data funds them.

**Must not, ever, in this design's scope:** reuse tokens on any ABI surface (spine §3.5);
modes on closure/constructor/extern/platform ABI edges (R2 + spine §3.1 pins — adapters and
declared facts only); a backend-local escape/strand analysis duplicating typecheck's
(narrowness counterweight — the backend consumes verdicts); any emission change on a
fact-absent path (§2.2 discipline); GOT slot-hole reclamation (FIXME 0466 stands).

---

## §11. Quality attributes (per-crate stewardship)

- **Simplicity (P6):** every mechanism reuses an existing seam — the non-atomic arms exist
  (§5), the wrapper pattern exists (§3.5), the null-elem-fn path exists (§7.3), the raise
  machinery exists (§8.1), the slot allocator exists (§8.2). Net-new machinery: stack-slot
  emission + immortal sentinel, the adaptation-algebra helper, `compile_trap_stub`, one
  manifest key, one sibling export. Nothing else is invented.
- **Maintainability:** atomicity and slot-init changes are heap.rs-local (the containment
  rule); mode consumption concentrates in `compile_consuming_arg_list` + `compile_to_module`
  entry; the wrapper/curry adapters share one algebra helper. Blast radius per mechanism is
  one file plus its call sites.
- **Observability:** `CRANELISP_RC_STATS` counters attribute the elisions (the S99
  discipline); `CRANELISP_CODEGEN_DUMP`/`/clif` show the fact-gated emission deltas;
  the `GotObserver` (FIXME 0099) covers §8's slot events; the toggle gives every observation
  an A/B baseline. A per-mechanism stat counter set (stack-slot hits, reuse hits/misses,
  non-atomic op share) is the designed `/dev` extension of the existing stats hook
  (`heap.rs:294`/`rc.rs:117`).
- **Concurrency-safety:** the backend adds no strand reasoning and no shared state; every
  concurrency-sensitive decision (confinement, escape-across-suspension) arrives as a
  typecheck verdict whose soundness obligations live above the boundary. The immortal
  sentinel (§4.2) and the else-arm discipline (§2.2) are the two structural guards this
  crate owns.
- **Performance:** each mechanism's win is stated against the S99 measured terms (§5.2 table
  names what increment I does NOT cure); acceptance rides `/qa`'s per-increment F1–F4 bars
  (spine §9), never this doc's estimates.
- **Testability (P5):** every mechanism is unit-testable at its seam with the existing
  in-crate fixtures — `compute_last_uses` extension against hand-built `MonoExpr` bodies with
  provenance maps; stack-slot eligibility gates as pure predicates; the adaptation algebra
  as an emission golden-test; trap stubs by invoking the compiled stub and asserting the
  error slot. Byte-identity-off is CI-able as CLIF-text equality (§2.2). Coverage gaps
  routed to `/qa` (§12).

---

## §12. Open questions routed onward

**Filed now:**

- **FIXME 0468 (`target: /arch`)** — single-source home for the Copy/value-layout predicate
  when R5 lands (§7.1): typecheck's mode classifier and the backend's `HeapCategory::Value`
  arm must consume one definition (soundness-coupled — a `Copy` mode over an unflattened
  representation is a missing inc). Proposed: a `cranelisp-types`-hosted pure classifier in
  the R5-increment `/arch` change-set. Not S100-blocking; nothing is emitted from the `Copy`
  row until R5. `design/arch/fixmes/0468-copy-value-layout-predicate-single-source.md`.
- **FIXME 0469 (`target: /arch`)** — spine §3.1(b)/§10-item-14 illustrative-example
  correction: `vec-len` is inline-lowered at statically-resolved sites (no consuming pair to
  elide — §9.2); cite `str-len` instead.
  `design/arch/fixmes/0469-spine-sibling-example-vec-len-is-inline.md`.

**To `/qa` (parts 17–18):**

1. The §2.2 byte-identity lanes: CLIF-text equality (toggle-off vs pre-S100 baseline) +
   observable-output differential (on vs off) over the corpus.
2. Starved-inc regression fences on every "skip the inc" emission this doc adds (§3.1
   caller elision, §3.3 projection reads, §9.3 sibling targeting) — the S98-bug-#2 class
   guard the spine mandates; plus the §3.3 root-release-ordering shape (the Sprint-61
   regression one level up — shared with typecheck §12 item 7).
3. §4's stack-slot lanes: an ASan/UAF lane on the TCO back-edge gate and on
   spark-reads-parent-stack-slot; a negative lane asserting `vec-push-grow` is unreachable
   for stack vecs (the sentinel guard).
4. §6's reuse fence: reuse-on-non-unique is heap corruption — differential + ASan +
   heap-balance on the reuse emission when increment II lands.
5. §8's trap-stub behaviour: broken-symbol call raises with provenance in all dev-session
   shapes (direct call, closure-value call through an old wrapper, curried); the RC-mid-panic
   leak is bounded (heap-balance tolerance documented, not asserted to zero).
6. A per-extern `CRANELISP_RC_STATS` attribution lane funding (or burying) §9.2's deferred
   sibling candidates.
7. The vec-query-family NULL-GOT-slot value-use defect — **triage complete (S100: REAL
   DEFECT), fix scheduled S101** (`sprints/SPRINT.md` item 1), sequenced **before** increment
   I's §9 `str-len$borrowed` sibling and §3.5 R2-wrapper work, which land on the same seam
   (§9.1 also touches the same registration site). `/qa`'s repro guards exist and are
   failing-not-ignored: `tests/vec_query_value_use.rs` — 4 RED (`vec-get`/`vec-set`/
   `vec-push` as values through a HOF, REPL + `--run`) + the GREEN `vec-len` control pinning
   the working path. Fix brief for `/dev` (account verified against source, S101 Phase 3):
   - **Root cause.** `vec-get`/`vec-set`/`vec-push` sit in the static primitives table with
     allocated-but-NULL GOT slots (`insert_vec_query_entries` — name-resolution-only
     entries; no extern body can exist because a single monomorphic body cannot know the
     element's heap category). Statically-resolved sites are inline-lowered
     (`compile_vec_op`, `vec_codegen.rs:95`) and work. Value use routes `compile_var` →
     `is_known_function` (the slotted entry satisfies `resolve_got_target`) →
     `compile_fn_as_value` → `compile_fn_wrapper_body` → `emit_wrapper_call`
     (`fn_as_value.rs:361`), whose fallback is a GOT-indirect `call_indirect` through the
     NULL slot → jump to 0 → SIGSEGV.
   - **Fix location and shape.** `emit_wrapper_call` needs a vec-query arm before its
     GOT-indirect fallback — the in-file precedent is the primitive-constructor arm
     (`fn_as_value.rs:388`), which inline-emits instead of calling through a non-callable
     slot. Note two non-drop-ins: the vec family is **not** in `primitives_inline`
     (`is_known_builtin` has no vec entries — the curry path's inline fallback does not
     cover it), and `compile_vec_op` is not directly reusable in a wrapper body (it builds
     on `self.builder` and takes `MonoExpr` args for element-type/last-use analysis; the
     wrapper builds in a separate `FunctionBuilder` context). The fix wants borrowed-builder
     emission — the `emit_adt_construct_into` precedent in the same file.
   - **RC semantics inside the wrapper.** Every wrapper param arrives **owned** (consuming
     closure protocol), so the inline emission takes the owned-temporary polarity uniformly:
     `vec-get` → bounds check + element load + element inc (per element heap category) +
     vec-aware dec of the consumed vec; `vec-set`/`vec-push` → the element's reference
     transfers into the vec with **no** consuming inc (the temporary branch of
     `element_consuming_inc`), and the vec is trivially at last use, so the COW rc==1 path
     applies.
   - **Element heap category is available per-site.** `compile_var` receives the Var's
     concrete `inferred_type` (post-mono types are concrete — S84 ruling): `(Fn [(Vec t)
     Int] t)` etc. The fix plumbs it into `compile_fn_as_value` (today name + span only) and
     down to the wrapper-body emission. This per-site type knowledge is exactly what a
     primitives-crate extern body cannot have — why the wrapper is the right fix location
     and the alternative stays blocked on element-type erasure.
   - **Curry-shape coverage.** By inspection, a partial application (e.g. `(vec-get v)`)
     reaches the same NULL slot: `emit_curry_target_call` has no trait resolution for the
     vec family and the inline table misses it, so it falls through to `emit_wrapper_call`.
     Not covered by the S100 repro; `/dev` assesses during the fix (unit-test-per-fix
     discipline) — a fix at/below `emit_wrapper_call` covers it only if the element-type
     plumbing also reaches the auto-curry path.

**To the `/int` design fire (`design/int/`, later):** the §8.3 interface consumption — the
redefinition transaction, reverse index lifecycle, frozen-`Code` retention pool, cascade
diagnostics UX, file-watcher interplay; plus the toggle's session-facing surface (spine §5.7:
analysis-off is the interim guard until the machinery lands).

**Deferred by design:** multi-word flattening (§7.2 trigger); shared-helper atomicity
variants (§5.2); region arena detail (§4.4, with the (a)-allocator co-design); sibling
expansion (§9.2); the heap-field stack-slot extension (§4.1 gate 2). None block increment I.

## Next skills

- `/qa` — author the verification/acceptance plan (parts 17–18, `tests/plan/`) inheriting
  spine §9 + §12 items 1–7 here + typecheck §12 items 5–8.
- `/arch` — evaluate FIXME 0467 (summary shape) and FIXME 0468 (Copy-predicate home)
  alongside the §3.3 carrier design at the implementing sprint; no S100 action.
- `/sprint` — sequence at close per spine §5.7: R3 machinery (§8) → increment I → increment
  II; `--release` stays gated behind the settled memory model.
- `/design` (int, later fire) — consume §8.3 and design the session transaction in
  `design/int/`.
