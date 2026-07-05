# Ownership codegen — the backend-crate proposal (parts 12–16)

**Status:** DESIGN (S100 Phase 3, stage 2; amended S101 Phase 3 — §2.3 toggle-timing
reconciled to the `/arch` S101 Phase-2 ruling, §8.1/§8.3 implementation pins added, §12
item 7 upgraded from triage note to fix brief; **amended S102 Phase 3 — §13 added: the
increment-I implementation staging** — golden-CLIF capture backend half, the ordered
change-set ladder with per-change-set oracle/gate obligations, the `fn_as_value` seam
rework folding 0474/0483/0476, and the Principle-23 scenario matrices + `tests.rs` split
plan) — the per-crate codegen proposal for the five
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

> **AS-BUILT — B3.2 Wave 11 (partial, commit `d7b6a0f`).** The **first summary
> consumer** landed: §3.3's `ResultMode::Fresh` protect-elision. The compile-in-hand
> `ModeSummary` (`codegen_view.mode_summary`, `MonoDefnVariant`) is threaded into
> `FnCompiler.current_mode_summary` (`lib.rs` `compile_to_module_impl` →
> `compile_defn_in_module` → `compile_body`; the lenient JIT/REPL path passes
> `None`). At the function-return site (`fn_compiler.rs::compile_body`),
> `return_is_fresh_by_summary(summary)` elides `protect_return_value`'s inc
> when a PRESENT summary has `result == Fresh`. Byte-identical
> under `CRANELISP_NO_OWNERSHIP` (all 13 corpus entries); scoped ON re-baseline =
> `05_string_externs` + `f4_sudoku`. Flips the G2 (`vec_set_as_value_shared_source_neg`)
> and item-26 (`vec_returned_from_generic_fn…`) guards. Unit matrix:
> `fn_compiler::return_protect_tests`.
>
> **AS-BUILT UPDATE — B3.2 Wave 11 (Apply restriction DROPPED, this change-set).**
> FIXME 0520 (`8b0237f`) cured the typecheck-side result-mode collapse — `join_origin`
> no longer widens a partial control-flow param-return toward the dangerous `Fresh`
> (`build`'s base-case-returns-`v` body now reports `AliasOf(0)`, not `Fresh`). The
> `Apply`-body restriction that the partial slice carried is therefore **removed**:
> `return_is_fresh_by_summary` now elides the return protect for ANY body shape whose
> PRESENT summary has `result == Fresh`. Verified: `04_vec_cow_loop`'s `build`
> (`result=AliasOf(0)`) keeps its protect and runs correct (exit 220) under
> `MALLOC_PERTURB_`; the newly-unrestricted elision now fires on genuinely-`Fresh`
> if/match/let-bodied functions. Byte-identical-off proven (toggle-off HEAD ==
> toggle-off parent, f3+f4). Scoped ON re-baseline = `f3_inverted_search` +
> `f4_sudoku` (each = one protect inc elided on a `Fresh` non-`Apply` return; the
> param scope-dec retained). Unit matrix updated: `fresh_summary_elides_all_body_shapes`.
>
> **AS-BUILT — B3.2 borrow-elision core (S102 Wave 11b, this change-set).** The
> coupled caller/callee ABI change landed as ONE atomic unit (§3.1 + §3.2 + §3.4
> + §3.5). Seams:
> - **§3.1 caller** — `compile_consuming_arg_list_moded` (`apply.rs`) reads the
>   callee summary via `resolve_callee_summary` (new; `resolution.rs`, stops at
>   `is_callable_target`, ⊤-on-absence). Per-position emission is the pure
>   `moded_arg_rc(category, mode, owned_binding)` (matrix in
>   `apply/moded_arg_rc_tests.rs`). Threaded through the three user-fn arms —
>   `SigDispatch`, `TraitMethod`, `compile_var_apply` global — each emitting the
>   returned `post_call_decs` after `compile_direct_call`. **As-built
>   sharpening:** a `Var` naming a fn-as-value / bare constructor (NOT in
>   `variable_types`) is a fresh rc=1 **temporary**, not an owned binding — it
>   gets the temp+`Borrowed` post-call dec (the cell whose absence leaked a
>   fn-as-value closure in isolation testing). Constructors / closures / externs
>   / platform effects UNTOUCHED (Decision-24 permanent).
> - **§3.2 callee** — `bind_defn_params` (`fn_compiler.rs`) registers each
>   `Borrowed` heap param into `borrowed_vars` (via `mark_borrowed`); everything
>   follows from the existing §5.5 discipline (no scope dec, never last-use). The
>   Borrowed-never-returns `debug_assert!` fires at the `compile_body` return
>   site.
> - **§3.4 adaptation** — `emit_d24_adaptation(summary, args, result)`
>   (`fn_as_value.rs`): per `Borrowed` param a guarded post-call dec; a
>   `ProjectionOf` result a guarded materialization inc; else pass-through. ONE
>   helper.
> - **§3.5 R2 wrapper** — realized by injecting `emit_d24_adaptation` into the
>   EXISTING `emit_wrapper_call` moded-body arms (the func-id direct call and the
>   GOT-indirect call), gated on a non-ABI-conservative target summary. The
>   existing `__wrap_` / `__wrap_tmv_` / `__curry_` wrapper body IS the
>   Decision-24 adapter (its code pointer is the only closure-reachable pointer;
>   the moded body is reached ONLY through it and through §3.1 static sites) — so
>   no separate `__d24wrap_` artifact is minted (simpler, and satisfies THE
>   INVARIANT directly). Auto-curry composes through `emit_curry_target_call →
>   emit_wrapper_call`: ONE adapter, never stacked.
>
> **Proof (this change-set): byte-identical-OFF confirmed** (toggle-off HEAD ==
> toggle-off parent, all 13 corpus entries, manual capture since `clif_golden.sh`
> strips the toggle). **Analysis-ON re-baseline: 9 entries** (01/02/04/07/08 +
> f1/f2/f3/f4) — categories: §3.1 caller skip-inc (reduced incs), §3.2 callee
> dec-elide (reduced decs), §3.1/§3.5 adaptation post-call dec (added decs on 01,
> f3), FuncId/value renumber ripple (02, f2); `clif_golden.sh diff` EMPTY.
> **Behavioral (ON==OFF observable + RC-balanced under `MALLOC_PERTURB_` +
> `RC_DEC_CHECK`):** all 13 corpus ON==OFF; `04_vec_cow_loop` exit 220; the five
> elision classes a–e each pinned by a value-correct + balanced repro (borrowed
> pass-through; borrowed→Owned adaptation inc; temp+Borrowed post-call dec; moded
> fn as closure value; auto-curry of a moded target).
>
> **STILL DEFERRED (optional follow-on, §3.3):** in-frame `vec-get` projection
> elision + `ProjectionOf`/`AliasOf` in-frame consumption + the
> `compute_last_uses` provenance extension. Not required by the coupled core; the
> `ProjectionOf` **result-mode** materialization inc IS built (§3.4). The H2
> per-mechanism RC_STATS counter (`ownership_fences::h2_*`, RED) is owed and needs
> the `cranelisp-intrinsics` `print_rc_stats` surface (backend-paired runtime, out
> of this crate); h3 (per-extern adaptation pairs) rides B3.3/B3.5.

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

> **AS-BUILT — B3.4 Wave 11: mechanism LANDED, HELD OFF at the conservative
> point. Activation ATTEMPTED THREE times (2026-07-05) and each time held off.**
> B3.4 is the FIRST hard consumer of the `escapes` site fact. The complete
> mechanism is implemented and unit-tested; a single compile-time flag —
> `STACK_ALLOC_ESCAPE_FACT_SOUND = false` (`fn_compiler.rs`) — holds it at the
> all-heap conservative point (byte-identical to pre-B3.4).
>
> **The THIRD blocker (FIXME 0525, `target: /arch`) — NOT a classifier gap; a
> structural stack-alloc-vs-lenient-eval mismatch.** After FIXME 0523 (capture)
> and FIXME 0524 (the whole value-outflow edge space) cured the escape classifier
> comprehensively, the RE-ACTIVATION completeness check confirmed the two
> lambda/HOF-return regressions
> (`constructor_wrapped_in_lambda_applied_indirectly_works`,
> `polymorphic_higher_order_returning_adt`) PASS flag-ON under `MALLOC_PERTURB_` —
> the 0524 cure is genuine. **But the third regression
> (`nested_match_in_arm_body`) fails HARD flag-ON** (`runtime error: match
> failed`). Root cause: under LENIENT eval the backend sparks a call's arguments
> onto separate strands — a **codegen-internal transformation the strict
> `MonoExpr` `escapes` analysis cannot see** — so a stack slot built for a
> lenient-sparked arg lives in a thunk frame popped at the join; a call with two
> or more stack-allocated scalar-ADT args dangles (a single such arg passes by
> luck — the scalar is extracted before slot reuse, a false-green). Ablation:
> `NO_OWNERSHIP` → correct (stack-alloc causal); `NO_LENIENT` → correct
> (lenient-specific); one ADT arg → OK, two-to-one-call → UAF. **The escape fact
> is CORRECT** (this is not a 4th/5th classifier gap); it is simply insufficient
> as a stack-alloc precondition while the backend introduces strand crossings the
> strict analysis can't model. The confinement fact DOES flag these
> (`confined = Some(false)`, crossing) — but the confinement analysis
> over-approximates EVERY apply-arg / let-RHS to crossing (§5.2 / the B3.3 review),
> so gating stack-alloc on it (the §4.3 "decline crossing" rule) declines the
> whole win and makes the mechanism dead code (Principle 8 — the exact anti-pattern
> the B3.3 through-binding half was dropped for; measured: the golden diff goes
> EMPTY, nothing stack-allocates anywhere). **Neither "trust escape alone" (UAF)
> nor "also require confined" (dead win) is a sound activation.** B3.4 cannot
> activate until /arch rules on how stack-alloc interacts with lenient-eval
> arg-sparking (FIXME 0525: candidate directions = confinement precision so a
> genuinely-local constructor is `Some(true)`, OR fix lenient multi-arg codegen to
> copy stack args before crossing, OR mode-gate B3.4 to non-lenient compilation).
> The flag was reverted to `false`; the mechanism (four gates + `emit_stack_alloc`
> immortal header) is landed unchanged and activates the moment 0525 resolves and
> the flag flips (after re-verifying killer/win/adversarial + the FULL suite
> INCLUDING the multi-arg lenient shape).
>
> **The earlier two activation attempts (2026-07-05, both reverted).** FIXME 0523
> (`be6cff4`) cured the closure/spark-CAPTURE escape gap; a first activation then
> surfaced FIXME 0524 (lambda-body-return / HOF-flow classified `Some(false)`);
> after 0524 (`936404b`) cured the whole escape class, the re-activation surfaced
> the 0525 lenient blocker above. Historical detail of the 0524 signature:
>
> **The B3.4-ACTIVATION attempt (2026-07-05).** FIXME 0523 (`be6cff4`) cured the
> closure/spark-CAPTURE escape gap, so activation was attempted: the flag flipped
> `false → true`. Verification confirmed the FIRST escape gap was closed (both
> 0523 killer shapes classify `escapes = Some(true)`, stay heap, correct under
> `MALLOC_PERTURB_`; the win `(MkBox 5)` stack-allocates with the immortal header;
> monomorphic constructors RETURNED from NAMED `defn`s / heap-field / TCO-loop /
> extern shapes all correctly stay heap; full 13-entry corpus ON==OFF and
> byte-identical-OFF held). **But the full suite surfaced THREE hard-UAF
> regressions** (`regression::constructor_wrapped_in_lambda_applied_indirectly_works`,
> `spec_03_types::polymorphic_higher_order_returning_adt`,
> `spec_06_pattern_matching::nested_match_in_arm_body` — all `runtime panic: match
> failed`, all pass flag-off / fail flag-on): a constructor that is the RETURN
> VALUE of a **lambda**, or that flows out through a **higher-order call**, is
> classified `escapes = Some(false)` and stack-allocated, then dangles once the
> lambda/callee frame pops. This is a SECOND escape-soundness gap distinct from
> 0523 (capture): 0523 was capture-by-closure; this is lambda/HOF *return*. The
> backend cannot gate it (interprocedural/lambda-return reasoning is out of the
> narrowness budget). **Filed FIXME 0524 (`target: /typecheck`); the flag was
> reverted to `false`.** Re-attempt activation only after 0524 lands and the
> killer/win/adversarial + full-corpus behavioral suite is re-verified. Seams
> (the landed, held-off mechanism):
> - **Mechanism (`heap.rs`)** — `emit_stack_alloc(builder, payload_size)`:
>   `create_sized_stack_slot(HeapHeader::SIZE + payload_size, align 8)` +
>   `stack_addr` + header init (alloc_size @0, **`IMMORTAL_RC = 1<<62` @RC_OFFSET**,
>   §4.2). Byte-identical layout to `alloc_with_rc` except the sentinel, so every
>   downstream tag/field store and every RC/COW/drop path runs identically against
>   the stack address — no call-site changes for stack-ness. Plus a
>   `STACK_SLOT_HITS` codegen-time counter (`stack_slot_hits()`), the B3.4 h2 half.
> - **Consumption site** — the escape fact lives on the **use-site `Apply`** node
>   `(Rect n n)` (allocated in the caller's frame, inlined via `emit_adt_construct`
>   at `apply.rs`), NOT on the synthetic `ConstrADT` constructor-*body* (which
>   always returns to its caller and stays heap). So the verdict is computed at the
>   `Apply` dispatch (`FnCompiler::constructor_call_stack_eligible`) and threaded
>   `compile_apply → dispatch_apply → compile_var_apply →
>   emit_adt_construct_stackable`. This first-consumer wiring gap is exactly the
>   B3.2→0520 parallel (the fact is annotated one node away from where the naive
>   reading expects it).
> - **The four eligibility gates (`constructor_call_stack_eligible`), all
>   backend-local, all CONSERVATIVE (when in doubt, HEAP):** (1) statically sized
>   — always true for a constructor call; (2) all-scalar payload — every arg/field
>   classifies `NeverHeap` (`node_is_scalar`); (3) not reachable by a TCO
>   back-edge — declined for the WHOLE function when it self-calls
>   (`body_has_self_call` / `fn_has_self_call`, over-approximating the back-edge
>   set); (4) extern-produced ineligible — an inlined constructor is
>   backend-emitted, not an `alloc_with_rc` body.
> - **Scope of the first landing:** only scalar-payload **ADT constructor calls**.
>   `Lambda` closures and `VecLit` DECLINED (heap): `VecLit` allocates its
>   struct+buffer through the `runtime/vec_new` extern (gate-4-adjacent; needs
>   inline stack construction), closures need the scalar-capture gate + the §4.3
>   spark-escape audit. Declining is always sound. The vec-mutation heuristic
>   (§4.2 — decline vecs with in-frame `vec-set`/`vec-push`) and the §4.3
>   spark-capture handling ride the `VecLit`/`Lambda` enablement, deferred with them.
>
> **THE BLOCKER (FIXME 0524, `target: /typecheck`): the escape fact is UNSOUND
> for lambda-returned / HOF-returned constructors.** FIXME 0523 (`be6cff4`/
> `d0c7684`) cured the first gap (closure CAPTURE — pass5 now computes an escaping
> closure's capture set as the free vars of its body and classifies each as an
> escape edge, spine R6). The B3.4-ACTIVATION verification confirmed that fix (the
> 0523 killer shapes classify `escapes = Some(true)` and stay heap; a monomorphic
> constructor RETURNED from a NAMED `defn` is also `Some(true)`, per the
> adversarial re-confirm). But a constructor that is the RETURN VALUE of a
> **lambda** — `(fn [y] (Some y))` — or that flows out through a **higher-order
> call** — `(apply-it (fn [y] (Some y)) 7)` — is still classified `Some(false)`
> and stack-allocates, then dangles once the lambda/callee frame pops (`runtime
> panic: match failed`). The lambda does not appear in the ownership cluster
> summaries, so its body-return `(Some y)` node never receives the escape edge its
> named-`defn` sibling does. The backend cannot gate around this (interprocedural/
> lambda-return escape reasoning is out of the narrowness budget), so the
> mechanism stays OFF until the analysis treats a lambda's / HOF-returned
> constructor as an escape edge. Flip `STACK_ALLOC_ESCAPE_FACT_SOUND = true` in
> the change-set that resolves 0524 and the mechanism activates unchanged.
>
> **Proof (activation attempt, then reverted):** byte-identical-off HOLDS
> trivially (flag off ⇒ no site stack-allocates ⇒ pre-B3.4 emission). With the
> flag momentarily forced on during verification: the win fires (a NoEscape scalar
> ADT read locally emits `explicit_slot` + `stack_addr` + the `iconst
> 0x4000_0000_0000_0000` immortal header; value-correct under `MALLOC_PERTURB_`),
> the 0523 killer shapes and the adversarial non-eligible shapes (returned-from-
> `defn` ADT, heap-typed-field ADT, TCO-loop local, extern/VecLit-produced) all
> stay heap and correct, and the full 13-entry corpus is ON==OFF — EXCEPT the
> lambda/HOF-returned-constructor shapes, which is the 0524 finding above (three
> existing REPL tests fail flag-on / pass flag-off). Unit matrix:
> `heap::stack_slot_b34_tests` (emission + immortal header + counter) +
> `fn_compiler::b34_stack_eligibility_tests` (`node_escapes` total match;
> `body_has_self_call` gate-3 scenarios). The killer/win/adversarial + full-corpus
> behavioral suite is the re-verification checklist for the 0524-resolving
> change-set; the durable e2e guards are /qa's (the 0524 UAF repro).
>
> **h2 disposition — STAYS RED (coordination question, not crossed).** The h2 guard
> asserts the process-exit `[RC_STATS]` line contains `"stack_slot"`, printed by
> `cranelisp-intrinsics::rc::print_rc_stats`. The `STACK_SLOT_HITS` tally is a
> backend **codegen-time** counter; `cranelisp-intrinsics` does **not** depend on
> `cranelisp-backend` (the edge is backend→intrinsics only), so the print surface
> cannot read it without a reverse/cyclic dependency — and codegen-time vs runtime
> (and `--run` vs `--link`, which are different processes) makes it a genuine
> design decision on WHERE per-mechanism counters live and how they reach the
> runtime print surface (same coordination B3.3 flagged for the non-atomic-share
> counter). Backend counter wired; h2 left RED; the cross-crate/design question is
> reported to `/sprint` (likely an `/arch` + `cranelisp-intrinsics` touch).

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

> **AS-BUILT — B3.3 Wave 11 (this change-set).** The per-site re-gate landed.
> Seams:
> - **`heap.rs`** — a `RcAtomicity { Atomic, NonAtomic }` enum + a single
>   `use_nonatomic_arm(atomicity)` decision point (the per-site gate ∨ the
>   `CRANELISP_NONATOMIC_RC` probe — one code path, two gates, Principle 7).
>   The five gated helpers each gained an `_atomicity` sibling
>   (`emit_rc_inc_atomicity`, `emit_rc_inc_guarded_atomicity`,
>   `emit_rc_dec_guarded_atomicity` — the `emit_rc_dec` path routes through it —
>   and `emit_vec_rc_dec_with_drop_atomicity` in `vec_codegen.rs`); the plain
>   names are retained as `Atomic`-delegating wrappers, so all ~40 non-participating
>   call sites are UNTOUCHED (the §2.2 else-arm identity, byte-identical-off by
>   construction).
> - **Confinement carrier** — the `confined` fact reaches emission through
>   `node_confined(&MonoExpr)`, which reads the fact off the five allocation/
>   capture-producing variants directly, for materialization incs where the
>   producing node is in hand. The live consumer is `protect_return_value`
>   (`rc_emission.rs`) — the returned cell's own node carries `confined`, and a
>   Parent-strand return allocation is `Some(true)` ⇒ the non-atomic inc arm
>   (the dominant increment-I win). `Some(true) ⇒ NonAtomic`; `Some(false) |
>   None ⇒ Atomic`. As typecheck's confinement precision grows, more return
>   nodes become `Some(true)` and go non-atomic with ZERO backend change.
>
>   > **B3.3-R (Wave 11, /review): the through-binding carrier was DROPPED.**
>   > B3.3 originally added a second carrier — `confined_bindings: HashSet<Symbol>`
>   > on `FnCompiler`, add-on-`let`-bind + remove-on-`pop_scope`, plus
>   > `rc_atomicity_for_binding`/`rc_atomicity_for_arg` — for the through-binding
>   > sites whose SSA `Value` identity is lost across `use_var` (consuming-arg
>   > inc of a `Var` arg, the Vec scope-cleanup dec, the match auto-upgrade, the
>   > tail-flush protect). It was **dead code carrying a latent data race**
>   > (Principle 8): (i) the current confinement analysis over-approximates every
>   > `let`-RHS to `Strand::PotentialFork` (`confinement.rs` — `join_strand(_,
>   > PotentialFork)` always ranks ≥ 1 ⇒ `off_parent()` true ⇒ `Some(false)`),
>   > so no `let`-binding is ever `Some(true)` and `confined_bindings` is
>   > **provably always empty** — it delivered ZERO non-atomic ops; (ii) the
>   > `HashSet<Symbol>` keyed carrier had add/remove but **no shadow
>   > save/restore**, so on nested same-name shadowing (inner *crossing* `x`
>   > inside outer *confined* `x`) it errs toward `contains("x") == true` ⇒
>   > non-atomic on a crossing cell ⇒ a data race — the exact P7/P8 fragile
>   > pattern that `confinement.rs::ConfineFrame` (the 8c-R2/F4 cure) already
>   > solves correctly with save/restore. Dropping it removed a dead speculative
>   > mechanism that was one confinement-precision tightening away from a live
>   > heisenbug on the B3.4 seam. The four through-binding read-sites now pass
>   > `RcAtomicity::Atomic` literally (the value the helpers provably always
>   > returned), so emission is byte-identical — verified: golden diff EMPTY and
>   > OFF-parent vs OFF-mychanges = 0 mismatches over the full 13-entry corpus.
>   >
>   > **Re-add discipline (when a live consumer arrives).** Re-introduce the
>   > through-binding carrier ONLY once the analysis actually produces confined
>   > `let`-bindings, and NOT with the `Symbol`-keyed add/remove pattern. Use
>   > either (a) `ConfineFrame`-style save/restore mirroring
>   > `confinement.rs::ConfineFrame` — snapshot the shadowed name's prior verdict
>   > on bind, restore it on `pop_scope` — so nested shadowing cannot leak an
>   > outer-confined verdict onto an inner crossing binding; or (b) key the
>   > carrier on the Cranelift `Variable` identity, not the `Symbol` name — a
>   > shadowing `let` gets a fresh `Variable`, so there is no name aliasing to
>   > leak across. The `Symbol`-keyed `HashSet` (no save/restore) is retired —
>   > do not repeat it.
> - **Counter (h2 backend half)** — a codegen-time `(nonatomic, total)` RC-emit
>   tally at the `use_nonatomic_arm` seam, read via `rc_emit_counts()`.
>   **h2 stays RED**: flipping it needs the process-exit `[RC_STATS]` print
>   surface (`cranelisp-intrinsics::rc::print_rc_stats`, a SEPARATE
>   backend-paired crate) to read this tally — a cross-crate coordination
>   deferred to B3.4 (noted, not crossed here).
> - **Out of increment-I scope (conservative/atomic, noted):** ADT/closure
>   scope-cleanup decs route through `emit_rc_dec_with_inline_drop_glue` /
>   `emit_closure_dec_inline`, which open-code `atomic_rmw` and are NOT among
>   the five named helpers — they stay atomic (sound; a §5.2-consistent gap).
>   The vec COW consumed-source decs and static vec-op dec keep `Atomic` (their
>   sources are crossing in the corpus); only the Vec scope-cleanup dec is
>   binding-gated.
>
> **Proof (this change-set):**
> - **Byte-identical-OFF — empirically PROVEN**: OFF-HEAD vs OFF-parent over the
>   full 13-entry corpus = **0 mismatches** (manual capture, since
>   `clif_golden.sh` strips the toggle). Structural: with analysis off no
>   `Some(true)` fact exists ⇒ `confined_bindings` empty + all `node_confined`
>   `None` ⇒ every derived atomicity is `Atomic` ⇒ `use_nonatomic_arm` false.
> - **Golden re-baseline (analysis-ON): 6 entries** — 03_auto_curry,
>   04_vec_cow_loop, 05_string_externs, 08_adt_in_vec_projection, f1_machinery,
>   f2_contention. Each = one (or few) confined materialization inc(s) flipped
>   `atomic_rmw add → load/iadd/store`, plus SSA renumber ripple; the
>   surrounding `atomic_rmw sub` decs are UNCHANGED. `clif_golden.sh diff`
>   EMPTY after re-baseline.
> - **Concurrency correctness (the real gate):** *WIN* — a Confined cell's
>   materialization inc emits the plain arm (verified in CLIF: the
>   `keep-and-make` protect inc; f2's confined inc). *SAFETY / anti-race* — a
>   Crossing board that crosses a spark boundary (F2's `g` into sparked
>   `reduce-tree`) keeps ALL RC ops atomic (`reduce-tree`/`copy-work`/`leaf-work`
>   = **0 non-atomic arms**, CLIF-verified). `s99_*_parallel_equals_serial`
>   green; f1/f2/f3 parallel==serial over 15 runs.
> - Unit matrix: `heap::tests::rc_atomicity_b33_tests` (5 helpers × atomicity,
>   CLIF-text asserted, else-arm identity, counter) +
>   `fn_compiler::b33_node_confined_tests` (classifier). Suite 3872/3869/3/1
>   (the 3 REDs = display_exact + h2 + h3, unchanged by name).

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
| `emit_vec_rc_dec_with_drop` | `vec_codegen.rs` — `atomic_rmw`, plus an `_atomicity` sibling | gained the same per-site atomicity input as the heap.rs helpers (it is emitted per site, so it CAN be gated). **B3.3-R:** its one binding-gated caller (the Vec scope-cleanup dec) now feeds `Atomic` — the sibling stays only as the probe-reachable mechanism; no `confined` verdict reaches it in increment I |
| Drop-glue bodies | closure drop glue, ADT drop glue fns | shared per type; same disposition as elem fns |

The increment-I win is therefore the **inline population**: consuming-arg incs, scope-cleanup
decs, capture incs, match-field incs, materialization incs — which is where the F2
shared-board read shape's surviving ops live (typecheck §5.3: the spark side is rc-op-free
under §3; the parent-side ops are exactly these inline ops).

> **B3.3-R as-built (Wave 11):** of that inline population only the
> **materialization incs** actually go non-atomic today, via the
> `node_confined` node-path carrier (`protect_return_value`). The
> through-binding inline sites (consuming-arg inc of a `Var` arg, Vec
> scope-cleanup dec, match auto-upgrade, tail-flush protect) all emit `Atomic`:
> their `confined_bindings` carrier was dropped as dead + latent-race code (see
> the B3.3-R note in §5's AS-BUILT block) because the current analysis produces
> no confined `let`-bindings. They rejoin the non-atomic population — with the
> `ConfineFrame`-save/restore OR `Variable`-identity re-add discipline — when
> the analysis actually confines a `let`-binding.

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

## §13. Increment-I implementation staging (S102 Phase 3)

Authored by `/design` (backend, narrow) against `sprints/SPRINT.md` S102 Block B. Governing
rulings inherited: the spine §6.2 capture-then-scoped-rebaseline ruling (`/arch` S102
Phase 2), the FIXME-0476 `/arch` ruling (`PrimitiveBody::{Extern, Inline}` reshape,
consumed here), and the close-short seam after B2 (`sprints/SPRINT.md` §Sizing). `/qa`'s
concurrent Phase-3 plan (`tests/plan/s102-test-plan.md`) owns the corpus, MANIFEST,
EXCLUSIONS, capture/diff script, and the lane specs; this section owns the backend half —
dump determinism, the normalization contract, the change-set ladder, and the seam-rework
design.

### 13.1 Golden-CLIF capture — the backend half (Block B Wave 1; L-B1 substrate)

**Mechanism.** Capture = `CRANELISP_CODEGEN_DUMP=*` on a **cold-cache `--run`** of each
corpus module (cache hits do not re-codegen and dump nothing — cold cache is mandatory
for full coverage; fresh tmpdir per capture run). The dump machinery exists
(`lib.rs:203–253`: filter grammar, `; === CLIF <module>::<symbol> ===` framing,
`write_clif_dump`). `/qa`'s script harvests stderr; goldens live in
`tests/fixtures/clif_baseline/` per the qa plan.

**Hook H1 — dump frame atomicity (the one backend change in the capture change-set).**
`write_clif_dump` issues multiple writes per frame (header, body, footer) without holding
the stderr lock across them; under the concurrent scheduler two workers CAN interleave
mid-frame. Fix: compose the full framed dump into one `String` and emit it via a single
locked write (one `eprint!`-class call). Emission-neutral — CLIF *content* is untouched;
only the observability channel changes. This resolves qa-plan gap G-1's "then /backend"
arm pre-emptively; harness-side sorting (below) handles frame *order*.

**Normalization contract (harness-side, `/qa`'s script; pinned here so both sides agree):**

1. Split stderr on the CLIF frames; discard all non-frame lines.
2. Sort frames by `<module>::<symbol>` — compile *order* is scheduler-dependent and
   carries no signal; frame *content* does.
3. Frame content is **byte-verbatim — no canonicalization** of wrapper names, GOT slot
   immediates, or SSA numbering. Rationale: (a) span-derived wrapper names and slot
   immediates are deterministic for a fixed source + fixed capture configuration (slots
   are per-module, allocated in form order; the primitives table is static); (b) wrapper
   identity and slot identity are load-bearing semantics — 0483's defect class is
   precisely a wrapper-identity cell, and slot identity IS ABI identity (spine §5.6) —
   masking them would blind the oracle to the defect classes it exists to catch;
   (c) deliberate renaming (the §13.3 identity rework) surfaces as an attributed scoped
   re-baseline, which is the correct visibility, not noise.
4. **No runtime addresses may reach the corpus's CLIF.** Shapes that bake session
   addresses as immediates are excluded: `(trace …)` bodies (descriptor-blob pointers,
   `bake_descriptor_blob`) and platform-effect shapes (layout-hash bakes). If a future
   entry legitimately needs one, the masking rule is designed then, not pre-emptively
   (Principle 6).

**Capture-configuration pins (recorded in the corpus MANIFEST):** all emission-affecting
env unset — `CRANELISP_NO_LENIENT`, `CRANELISP_NONATOMIC_RC`, `CRANELISP_CAPTURE_BORROW`,
`CRANELISP_NO_OWNERSHIP` (pre-mechanism both polarities are byte-identical; the L-B1 lane
thereafter compares HEAD **toggle-off** against this golden). Lenient-spark emission is
deliberately part of the golden surface (the corpus's ParBind/spark shapes pin it).
Runtime-only knobs (`CRANELISP_SPARK_BUDGET`, `CRANELISP_SATURATION_GATE`) do not affect
CLIF and are unpinned.

**Determinism self-test at capture:** capture twice back-to-back; the normalized outputs
must be byte-identical before the golden commits. A mismatch is an H1-class finding
routed to `/backend` — never worked around by masking.

> **B0-be capture verdict (S102 Wave 3, goldens at commit `05818e9`): Hook H1 is a
> NO-OP — not implemented.** Zero mid-frame interleaving across 25 raw capture runs
> (every `; === CLIF` start/end pair balanced, strictly alternating); the multi-write
> frames never race in practice — only one dump-eligible module compiles at a time in
> this corpus. What the (repaired) selftest DID find was content variance, not framing:
> recompilation passes re-derive the JIT symbol set after scheduler-timing-dependent
> symbol registrations, so their `u0:N` FuncId immediates shuffle run-to-run (6/13
> entries, ~50% of runs). First-occurrence frames — the initial cold-cache compile —
> are byte-deterministic (20/20 single-entry, then 13/13 full-corpus selftest twice
> consecutively); the harness therefore dedups duplicate frames to FIRST occurrence,
> not last. Also repaired at capture: the harness parsed stdout while this section pins
> the dump channel as stderr — the pre-capture "selftest passes" was an empty-vs-empty
> false green. Fresh-capture diff after the golden commit: EMPTY (install witness).

**Corpus composition** is `/qa`-owned (green-only; EXCLUSIONS = 0483 two-instantiation
HOF, 0488 FQ-call/imported-value-use, 0484 shadow-order — qa plan §4). One backend pin:
the corpus SHOULD include the vec COW loop and the *green single-instantiation*
wrapper/curry shapes (the `vec_query_value_use.rs` green set), so the §13.3 seam rework's
CLIF delta is captured and attributed. Note 0474's leaking shapes are *green programs*
(leak-only — correct output); their CLIF is deterministic and they may join the corpus:
the 0474 fix then re-baselines them attributed, which is exactly the oracle's value.

**Scoped-rebaseline procedure (the developer protocol, binding on every backend
change-set from capture onward):**

1. **Before** an emission-affecting change-set (classifier: spine §6.2), run the capture
   script on the parent commit — confirm clean against the golden. A dirty start means a
   previous change-set skipped this discipline: stop and attribute that first.
2. Land the change; run the script; collect the per-entry diff.
3. **Attribute every changed entry to the change-set's seam.** Any diff that cannot be
   attributed is a defect finding — stop; do not re-baseline over it.
4. Re-dump ONLY the changed entries; golden diff + source change + attribution paragraph
   land in the **same commit**. Wholesale re-capture is forbidden.
5. If the change-set turns an EXCLUSIONS shape green: **extend** (new entry, fresh
   capture, EXCLUSIONS row struck) in the same change-set; existing entries untouched.
   Extension ≠ re-baseline.

### 13.2 The change-set ladder (ordered; each independently landable)

Every change-set below obeys the §2.2 else-arm discipline, so any suffix of the ladder
can carry to S103 without unsoundness (monotone soundness; the close-short seam sits
after B2). Per-change-set obligations: **[oracle]** = the differential-oracle duty
(`CRANELISP_NO_OWNERSHIP` byte-identical off — L-B1 golden diff expectation stated
per change-set; L-B2 both-polarity suite at wave gates) and **[gate]** = the I-G
acceptance gate(s) it makes gradeable.

| # | Change-set | Contents | Depends on | [oracle] | [gate] |
|---|---|---|---|---|---|
| **B0-be** | Capture substrate | Hook H1 dump-frame atomicity (§13.1); rides the same wave as `/qa`'s corpus + golden commit | nothing (Wave 1, not gated on Block A) | CLIF content byte-identical (channel-only change); golden commits here | installs L-B1 |
| **B1-be** | 0476 consumption + 0482 | Backend + primitives (paired) consumption of the `/arch` types change-set: `resolve_vec_query_primitive` name-list retires; the resolution stop-predicate flips `callable_got_slot().is_some()` → `is_callable_target()`; `emit_wrapper_call`/`emit_curry_target_call` exemption arms re-key off `PrimitiveBody::Inline`; **0482** `#[non_exhaustive]` on `CacheInvalidReason` + sibling-DTO audit; `public-api.txt` regens | `/arch` types change-set (ModeSummary + fact-table + `PrimitiveBody` reshape + `CACHE_SCHEMA_VERSION` v11→v12) | **golden diff EMPTY** — a representation cure, not an emission change; the empty diff is the change-set's own correctness witness | — |
| **B3.0** | 0495 relocation | `tests.rs` split: pure relocation of the 76 crate-root tests to their submodule homes per the 0495 bucket map; zero behaviour change. Scheduled with B1-be's wave (crate already open, pre-seam) so subsequent change-sets land their scenario tests in the right homes | B1-be (avoids relocating tests the 0476 edit touches twice) | no CLIF surface | — |
| — | *(B2 = typecheck/types: `pass5_ownership` + summaries. Not this crate. Backend expectation: summaries emitted, zero consumers ⇒ golden diff EMPTY. I-G5/I-G6 run here — mandatory at the seam if the sprint closes short)* | | | | |
| — | **CLOSE-SHORT SEAM** (`sprints/SPRINT.md` §Sizing; `/arch` Q3) | | | | |
| **B3.1** | `fn_as_value` seam rework — the defect half | §13.3: wrapper-identity scheme (0483 cure) + COW consumed-source polarity (0474 cure) + curry-path coverage; scenario-matrix unit tests per §13.5; 0488's fix rides here as a conditional rider iff `/qa`'s A3 isolation attributes it to this seam | B1-be (kinds), B3.0 (test homes) | emission-affecting: **scoped re-baseline** (wrapper names/COW branches) + **corpus extension** (newly-green 0483 shapes; EXCLUSIONS struck) | flips 0474×3 + 0483×3 guards; L-M1 matrix rides here |
| **B3.2** | Borrow-elision core (modes-live) | §3.1 caller skip-inc + temp post-call dec; §3.2 `Borrowed` params join `borrowed_vars`; §3.3 ResultMode consumption + provenance-rooted `compute_last_uses` extension; §3.4 adaptation algebra; §3.5 R2 `__d24wrap_{fq}_{slot}__` wrapper + curry composition. **One atomic change-set**: the callee-side moded compilation, the caller-side vector consumption, and the R2 wrapper flip together (a moded body reachable from a Decision-24 value use without its adapter is the §3.5 invariant violated) | B2 (summaries), B3.1 (the wrapper machinery base + a clean seam) | emission-affecting: the largest attributed re-baseline of the sprint (elided incs/decs across the corpus); H2 elision counters land here | **I-G1** (F1 ≥99% rc_inc drop), I-G2 attribution honesty; S1–S4+S6 fences discriminating |
| **B3.3** | Confined non-atomic RC | §5 re-gate of the existing `heap.rs` non-atomic arms on the per-site `confined` fact (`RcAtomicity` input on the emit helpers); `emit_vec_rc_dec_with_drop` gains the same input (§5.2's one moving inventory item); H2 non-atomic-op-share counter | B2 (facts); independent of B3.2 in soundness, sequenced after it because the surviving-op population I-G3 grades is post-elision | emission-affecting: scoped re-baseline (atomic→plain ops on Confined-classified corpus sites) | **I-G3** (F2 board classifies Confined; surviving parent-side ops non-atomic) |
| **B3.4** | Stack slots | §4.1–§4.3: `create_sized_stack_slot` + immortal-RC sentinel (`IMMORTAL_RC` header init) at `escapes = Some(false)` sites passing the four eligibility gates (statically sized, all-scalar payload, no TCO back-edge flow, backend-emitted); scope-exit skip mark; vec write-use decline heuristic; H2 stack-slot-hit counter | B2 (facts); independent of B3.2/B3.3 | emission-affecting: scoped re-baseline (alloc→stack_slot at eligible corpus sites) | **I-G7** (eligible-site heap allocs → 0); L-C2 ASan lanes |
| **B3.5** | `str-len$borrowed` sibling | §9.1 authoring template (shared core, two exports) + primitives-table sibling slot + `borrowed_sibling_slot` linkage + §9.3 four-leg emission gate; `ring2-rc.md` §3.3 audit table gains the "borrowed sibling?" column | B3.2 (site borrow-classification is a gate leg) | consuming export untouched ⇒ Rust side byte-identical off; sibling call sites re-baseline scoped | S5 fence; L-D5 attribution lane seeds |
| **B4** | 0459 density gate | The static allocation/RC-density admission axis on sparkability — designed in `lenient-eval.md` §2.7 (this sprint's doc edit); consumes the same per-site facts as B3.3/B3.4, active only when pass5 ran (facts-absent ⇒ axis inert ⇒ today's admission verbatim) | B2 (facts); most valuable after B3.2–B3.4 (density measures the *surviving* atomic/alloc population) | emission-affecting where it declines a spark (gate branch not emitted); toggle-off byte-identical by the axis-inert rule | **I-G4** (parallel non-regression) progress; lenient-eval §9 three-regime equivalence extended |

Ordering rationale: B3.1 immediately before B3.2 is the point of the fold — the R2
wrapper (B3.2) builds on the seam B3.1 just cured, one seam visit (Principle 8). B3.3/B3.4
are advisory-class consumers, mutually independent and independently droppable at a
capacity squeeze; they sit after B3.2 only because their *measured* value (I-G3's
surviving-op population, I-G7's candidate set) is defined post-elision. B3.5 needs B3.2's
borrow classification as an emission-gate leg. B4 is last: its signal is the residue the
other mechanisms leave.

### 13.3 The `fn_as_value` seam rework (B3.1) — folding 0474 / 0483 / 0476

**Actors (Principle 21).** The three wrapper families and their naming
(`__wrap_{name}_{disc}{span}__` at `fn_as_value.rs:135`, `__wrap_tmv_…` at `:246`,
`__curry_…` at `:715`); `emit_wrapper_call`'s dispatch ladder (`:361` family — the S101
NULL-slot fix's home); `emit_vec_query_into` + the shared COW cores
(`emit_vec_set_cow_core` / `emit_vec_push_cow_core`, `vec_codegen.rs`); the operator
wrapper precedent (`literals.rs:263`); post-0476 `PrimitiveBody::{Extern, Inline}` +
`is_callable_target()`; and the incoming R2 `__d24wrap_` adapter (§3.5). The functions
between them: value-use compilation → wrapper synthesis → wrapper-body emission →
(inline arm | GOT-indirect arm | adaptation arm).

**Ruling 1 — wrapper identity derives from (dispatch identity × concrete signature),
never (span × enclosing-fn discriminator).** The as-built naming keys on span + inner-fn
discriminator (the FIXME-0347 cure for enclosing-fn mono collisions); 0483 shows the
per-instantiation matrix still holds a fatal cell (≥2 wrapper-backed instantiations of
one HOF → SIGBUS). Target scheme, one identity rule for all families:

- slot-dispatched callables → `__d24wrap_{fq}_{slot}__` (§3.5 — slot identity is ABI
  identity; summary-trivial targets skip the adapter and close over the body directly,
  as today);
- `PrimitiveBody::Inline` targets (the vec trio; ctor family) →
  `__inlwrap_{bare}_{mangled concrete sig}__` — keyed by the *mono signature* (which
  determines the element heap category the wrapper body bakes), so two instantiations
  yield two names by construction, and identical instantiations share one symbol via
  `declare_function` name-idempotency (the body is a pure function of the key — dedup is
  sound);
- curry wrappers likewise re-key on (target identity × applied-prefix signature).

Properties: deterministic, deduplicable, collision-free across monomorphisations *by
representation* (Principle 20), and cache-safe (names are functions of persisted facts,
not compile-order accidents). **Investigation pin (binding on `/dev`, per
`memory/feedback_investigate_suspected_dual_path.md` discipline):** 0483's "wrapper-name
or slot collision" is a *hypothesis*; root-cause against the §13.5 instantiation matrix
FIRST (candidates: name collision, `vec_elem` type plumbed from the wrong instantiation,
shared-`ctx` clobber across the separate `FunctionBuilder`). The identity scheme lands as
the durable convention regardless; the fix must address the actual failing cell, and the
unit matrix is the arbiter.

> **CORRECTION — Ruling 1 root-cause was MIS-ATTRIBUTED (Wave 11 B3.1 investigation; the
> pin WORKED).** 0483's SIGBUS at ≥2 wrapper-backed instantiations was NOT a backend
> wrapper-identity collision at all — it was the **typecheck mono-mangler** (FIXME 0519:
> ADT-arg + home erasure in the monomorphisation name mangler, since cured by one unified
> lossless FQ mangler). The investigation pin above is exactly what surfaced this: forcing
> root-cause-before-fix against the instantiation matrix showed the crashing cell was a
> lossy-head *mono-name* mirror one layer UP in typecheck, not the backend wrapper name.
> 0483's three `vec_query_value_use` guards flipped GREEN on 0519, out of this change-set.
>
> Ruling 1's wrapper-identity scheme (`__d24wrap_{fq}_{slot}__` / `__inlwrap_{bare}_{sig}__`
> / re-keyed curry) **STANDS as a durable convention** (deterministic, dedup-safe,
> cache-safe) but does NOT itself fix 0483. **Crucial derived rule:** any signature
> embedded in a wrapper name MUST use the same TOTAL FQ grammar the mono-mangler now uses
> (recursive ADT args + home module + `Fn` shape) — a lossy-head wrapper key would re-open
> the exact same lossy-head mirror one level down in the backend. This is the same
> mis-attribution shape that recurs in Ruling 2 below (the design hypothesis named a
> plausible-but-wrong seam; investigation named the real one).

**Ruling 2 — one explicit RC-polarity contract on the COW cores.** The cores gain a
consumed-source polarity parameter (illustrative: `SourceOwnership::{Owned, Borrowed}`);
the **copy branch emits the source release iff `Owned`** (`emit_vec_rc_dec_with_drop`),
the mutate/grow branches are unchanged (ownership transfers into the returned pointer).
Every call site states its truth explicitly: wrapper and curry bodies pass `Owned`
(consuming closure protocol); static sites pass what their arg-compilation actually did —
and note the 0474 *widening* (guard 3: plain static `(vec-set v 0 9)` with `v` live also
leaks the protect-inc'd reference) means the static-site polarity is NOT uniformly
`Borrowed`; `/dev` derives each static call site's polarity from its actual inc emission,
with the §13.5 branch×polarity unit matrix pinning balance per cell. Leak-only class (no
UAF) — but the fix is a polarity *contract*, not a spot dec, so the next call-site shape
cannot re-introduce it (Principle 18).

> **CORRECTION — Ruling 2's COW-copy attribution is INCOMPLETE for the `vec_cow_value_use`
> ×3 guards (Wave 11 B3.1a investigation; RC_STATS + CLIF evidence).** The COW polarity
> contract IS landed and correct — `emit_vec_set_cow_core` / `emit_vec_push_cow_core` gain
> `SourceOwnership::{Owned, Borrowed}`; wrapper/curry pass `Owned` (copy branch releases via
> `emit_vec_rc_dec_with_drop`), static in-place sites pass `Borrowed` — and it cures a real
> wrapper/curry vec-set/push value-use leak (non-recursive HOF imbalance 2→1). But it is
> NOT the dominant cause of the three guards, which behaviourally decompose as:
>
> - **`vec_set_static_site_shared_source_neg` (G3):** a **TCO scope-cleanup leak**, not COW.
>   Non-recursive it is *balanced*; it leaks only in the tail-recursive loop. Root cause:
>   `compile_let_sequential`'s `pop_scope_with_cleanup` runs AFTER `compile_expr(body)`, but a
>   tail self-call emits its jump-to-loop-header first, so every heap-typed `let` binding that
>   survives to a tail-recursive scope exit has its dec emitted in the DEAD post-jump block and
>   never runs (leaks 1 alloc/iter/binding). Cured by `flush_let_scopes_before_tail_jump`
>   (`compile_tail_self_call`), which flushes the live let-scope decs before the jump, skipping
>   bindings that transfer into a tail argument. **FLIPPED GREEN.** (Golden re-baseline:
>   f2/f3/f4 — the corpus's TCO-loop-with-surviving-heap-binding fixtures.)
> - **`vec_set_curried_call_loop_neg` (G1):** an **auto-curry capture double-inc**, not COW.
>   The `ResolvedCall::AutoCurry` apply arm compiles applied args with `compile_consuming_arg_list`
>   (correct: inc Var / transfer temporary = the closure's one reference) AND `compile_auto_curry`
>   inc'd them AGAIN via `emit_capture_inc` (the lambda-capture precedent incs ONCE). Cured by
>   removing the redundant capture-store inc; curry now aligns with lambda. **FLIPPED GREEN.**
> - **`vec_set_as_value_shared_source_neg` (G2) + `ownership_fences::vec_returned_from_generic_fn…`
>   (item 26):** the SAME class — `protect_return_value` (rc_emission.rs) over-incs a return value
>   whenever the callee has heap cleanup targets, but the return is a **fresh Apply-body value**
>   (`(f v 0 9)` returning a vec-set copy; `(vec-push [] …)`) that scope cleanup can never free →
>   the protect leaks exactly 1/call. A SAFE narrowing needs to know whether the callee returns an
>   aliased argument (the `(idv v)` UAF class the protect guards) — i.e. **callee ownership
>   summaries (B2 / typecheck, `§13.6`)**. It is NOT the COW copy branch and NOT safely fixable in
>   the backend alone. **RED pending B2** (the failing tests are the record; owner /typecheck-half
>   of the ownership-inference summaries). Item 26's "fix in the vec-op caller handling / call-result
>   temp is Owned" framing was likewise mis-attributed: the caller does the correct single dec; the
>   surplus reference is minted in the callee's `protect_return_value`.
>
> Net Wave 11 B3.1a guard flips: item 25 (curry-glue idempotency) + G1 + G3 = **3**; G2 + item 26
> carry to B2. Same mis-attribution shape as Ruling 1: the design named a plausible seam (COW copy
> branch); investigation named the real ones (TCO cleanup, curry double-inc, `protect_return_value`).

> **B3.1a-R CORRECTION — the TCO scope-flush introduced a use-after-free (`f87b128`); F1 cure
> = the tail-flush skip-predicate correctness contract (Wave 11 B3.1a-R /review BLOCKER).** The
> G3 flush (`flush_let_scopes_before_tail_jump`) dec's every heap `let`-binding in scope frames
> `[1..]` before the tail-jump, skipping only those in `transfer_skip`. As first shipped,
> `transfer_skip` held only bindings passed as a **literal top-level `MonoExpr::Var`** tail
> argument. A binding **aliased into a tail argument through a control-flow form** — `(recur (if
> c a a))`, `(recur (match … a))` — reaches the arg value with NO owning inc (`compile_if` merges
> the raw branch value; a bare local `Var` is a plain `use_var`), is NOT in `transfer_skip`, so
> the flush frees it and the jump hands the freed pointer to the next iteration's loop param →
> **UAF**. The RC-balance stays near-balanced (`allocs≈201 deallocs≈200`) because the freed alloc
> *is* accounted — a leak-balance guard reads green over corrupt memory (`feedback_verify_fix_not
> _symptom_absence`); the repro asserts the computed RESULT, not balance.
>
> **The correctness contract (the skip-predicate invariant):** a tail-call argument transfers a
> live let-binding's reference forward in exactly one of three ways, each with a distinct RC
> treatment; the flush + protection must together net the binding to exactly one owner (the loop
> param):
> - **(a) bare top-level `Var`** `(recur v)` — a MOVE (no inc). `transfer_skip` excludes it; the
>   flush leaves it; the single reference passes to the loop param. Unchanged (byte-identical
>   golden — the corpus TCO fixtures f2/f3/f4 have no control-flow-aliased args, so the diff is
>   EMPTY).
> - **(b) control-flow-aliased** `(recur (if c v v))` / `(recur (if c lo hi))` / `(recur (match …
>   v))` — NOT a move (no inc on the merged value). Excluded from `transfer_skip` (flushed
>   uniformly) and instead protected by an explicit per-branch inc at the branch/arm tail
>   (`maybe_protect_tail_arg_alias`), gated on `tail_flush_will_dec(name)` — the exact predicate
>   the flush applies (in a `[1..]` frame, heap, not borrowed). Per-branch (not a single static
>   skip) is REQUIRED: for distinct-per-branch bindings `(if c lo hi)` the taken branch incs its
>   binding while the flush decs BOTH, so the moved one nets to the loop param and the dead one is
>   freed — "dec lo XOR dec hi" is impossible statically. The protection is CONDITIONAL on the
>   result being a will-be-flushed scope-binding `Var` (never an unconditional `protect_return
>   _value`-style inc): the tail flush is the balancing dec, not a caller, so incing a fresh branch
>   value `(if c (wrap v) v)`-then-arm would leak. A branch reaching the tail through a nested
>   scope exit `(if c (let [w …] v) …)` is already protected by that scope's own `protect_return
>   _value` (the tail flush being its balancing "caller" dec), so the per-branch helper only covers
>   the DIRECT bare-`Var` branch.
> - **(c) consumed into a fresh value** `(recur (wrap v))` — `compile_consuming_arg_list` inc's the
>   bare-`Var` heap arg, so the fresh value owns its own reference and the flush's dec of `v`'s now-
>   dead scope reference is balanced. No protection; NOT in `transfer_skip`.
>
> The flag `tail_arg_protect` is set only while compiling an `if`/`match` that is itself a direct
> tail-call argument, saved/restored per-arg, and CLEARED around the `if` condition / `match`
> scrutinee (consumed, not forwarded) so a heap binding aliased there is never spuriously
> protected; it propagates into nested control-flow branches (which correctly protect their own
> aliases). In `match`, tail-arg protection REPLACES `protect_return_value` for the arm value (the
> unconditional protect would leak a fresh arm value in the tail context); the borrowed-return
> auto-upgrade is retained (it produces an owned reference the flush does not touch). The dead
> `consumed_vars` skip arm (a `HashSet` initialised empty and never inserted into — it read as
> protection but was inert) is REMOVED from all three readers (`pop_scope_with_cleanup`, the flush,
> `protect_return_value`). Seam pins: `tail_transfer_skip` unit cells (bare-Var skipped;
> control-flow-aliased NOT skipped; distinct-branch both flushed) + the e2e value + `MALLOC
> _PERTURB_` UAF repros (`tests/tco_tail_arg_alias_uaf.rs`).

> **F2 — the auto-curry drop-glue identity (Wave 11 B3.1a-R /review Important; P7/P8).** The
> capture drop glue (`build_auto_curry_drop_glue`) was named `runtime/curry_drop_glue_{span}` —
> span-only, no `inner_fn_discriminator()` — while its paired wrapper `__curry_{target}_{disc}
> {span}__` folds the mono/gate-arm discriminator. The `get_name` idempotency skip (added for the
> item-25 lenient+sequential double-compile) then returns the first-defined glue for any later
> same-span build; two DISTINCT monomorphizations of one span with DIFFERENT capture
> `HeapCategory`s (distinct wrappers) would COLLIDE on the glue name → the 2nd mono silently gets
> the 1st's glue → wrong capture-drop (dec a non-heap / skip a heap capture → corruption or leak),
> replacing the earlier loud `Duplicate definition`. **Cure:** key the glue IDENTICALLY to its
> wrapper via `curry_drop_glue_name(disc, span)` folding `inner_fn_discriminator()` — a closure and
> its drop glue are one object with one identity. Distinct monos → distinct glue (each installs its
> own correct drop); the two arms of ONE create-gate (same disc + span, identical `arg_categories`
> by construction) still share one glue, preserving the item-25 idempotency. Pinned by the
> `curry_glue_name_tests` cells (distinct monos → distinct glue at a shared span; the name folds
> the disc; same-mono-same-span shares one name).

**Ruling 3 — the dispatch ladder becomes kind-driven.** Post-B1-be, `emit_wrapper_call`'s
arm selection reads the entry: `PrimitiveBody::Inline` → borrowed-builder inline emission
(the §12.7 mechanism, now kind-keyed — the S101 name-list is gone); slotted +
summary-trivial → GOT-indirect through the slot (today's path verbatim — the toggle-off
arm); slotted + non-trivial summary (B3.2 onward) → adapter body = GOT-indirect +
`emit_d24_adaptation` (§3.4). `emit_curry_target_call` consumes the summary directly
(compose-don't-stack, §3.5). One ladder, kinds not names, and the 0476 cure means no
consumer can route a value-use through a slot that cannot be stored.

**Guard-flip mapping (how the 6 guards go green as mechanisms land, not as patches):**
0483×3 flip on Ruling 1 (B3.1); 0474×3 flip on Ruling 2 (B3.1); the `vec_query_value_use`
green controls and shadowing pins stay green through Rulings 1/3 (regression fence); the
corpus extends with the newly-green two-instantiation shapes in the same change-set
(§13.1 step 5).

### 13.4 0459 — division between this doc and `lenient-eval.md`

The floor-scope doc half and the **static allocation/RC-density admission axis** are
designed in `lenient-eval.md` §2.7 (landed with this S102 amendment — the gate consumes
this doc's per-site facts and nothing else; zero new analysis, Principle 7). The
implementation is ladder entry **B4** (§13.2). This doc's obligation is only the fact
supply: the axis reads `escapes`/`confined` site facts and the borrow-elision outcomes
that B3.2–B3.4 make real; it is keyed off "pass5 ran" so the facts-absent path is
admission-identical to today (the §2.2 discipline applied to a *scheduling* emission).

### 13.5 Scenario matrices + `tests.rs` split (0495; Principle 23)

**The split (B3.0):** pure relocation of the crate-root `tests.rs` buckets to submodule
homes per the 0495 audit map (vec_codegen 20+, got 6–20, lib/module-assembly 6–20,
resolution/apply 6–20, fn_as_value ~5, trap stub 3, fn_compiler 3, extern_call 2,
lambda/launch 3, literals/match 2, jit ~3). No behaviour change; lands pre-seam so every
subsequent change-set's scenario tests have a home.

**Per-mechanism strategy scenario spaces** (per Principle 23 /
`memory/feedback_dev_strategy_derived_unit_scenarios.md` — `/dev` derives unit scenarios
at submodule × scenario-class grain, through the facade where expressible, and `/qa`
audits coverage against these matrices):

- **`compiler/rc_emission.rs` + `heap.rs` (B3.3):** {`emit_rc_inc`, `emit_rc_inc_guarded`,
  `emit_rc_dec`, `emit_rc_dec_guarded`, `emit_vec_rc_dec_with_drop`} ×
  {`confined = Some(true)`, `Some(false)`, `None`, toggle-off} → {non-atomic arm, atomic
  arm *verbatim*}. Negative class: fact-absent path emits the identical instruction
  sequence as pre-change (the else-arm identity, CLIF-text asserted); the probe env
  (`CRANELISP_NONATOMIC_RC`) still overrides as measurement ceiling.
- **`compiler/apply.rs` (B3.2):** {Var arg, temporary arg} × {callee param `Owned`,
  `Borrowed`, no summary} × {toggle on/off} → {consuming inc, skip-inc, skip-inc +
  post-call dec, verbatim today}; adaptation row (member of `borrowed_vars` at an `Owned`
  position ⇒ ordinary Var inc); result-mode consumption {`Fresh`, `AliasOf(i)`,
  `ProjectionOf(i)`, absent} × {result used / released / escapes}. Edge class: arity >8
  (stack-passed args), recursive callee mid-fixpoint summary.
- **`heap.rs::compute_last_uses` provenance extension (B3.2):** {projection chain depth
  1/2/n} × {root's textual last use before vs after the projection's last use} ×
  {projection escapes (rule-5 inc) vs frame-local} — the root's release must order after
  every rooted projection's last use (the Sprint-61-one-level-up shape). Negative:
  borrowed projections never appear as last-use candidates. **Shadowing row (typecheck
  §13.6(d))**: a `let x … let x …` rebind over a live provenance root arrives as
  `provenance: None` — the backend takes the Decision-24 materialization path (ordinary
  inc, no `borrowed_vars` entry); the row asserts that path fires and stays balanced.
- **`control_flow/fn_as_value.rs` (B3.1/B3.2):** dispatch-kind {UserFn slotted,
  `PrimitiveBody::Extern`, `PrimitiveBody::Inline` (vec trio), constructor, trait method,
  operator} × use-position {HOF arg, curried partial, returned from fn, stored in ADT
  field, direct value binding} × **instantiation count {1, 2-same-op-two-elem-types,
  2-different-ops-one-HOF, n}** × summary {trivial, non-trivial (B3.2)} × mode {REPL,
  `--run`}. Identity class: wrapper-name uniqueness/dedup per (target, mono sig) —
  asserted at the `declare_function` seam. The 0483 crashing cells and the green controls
  are rows of this matrix, not ad-hoc tests.
- **`compiler/vec_codegen.rs` COW cores (B3.1):** branch {mutate (rc==1), copy (rc>1),
  grow} × source polarity {`Owned`, `Borrowed`} × call-site kind {static, wrapper,
  curry} → exact RC balance per cell (allocs−deallocs = 0 over the cell's contract);
  COW value semantics asserted alongside (result correct, source unchanged on copy).
- **`control_flow/let_if.rs` + stack slots (B3.4):** eligibility gates {statically
  sized ±} × {all-scalar payload ±} × {TCO back-edge flow ±} × {`escapes` =
  `Some(false)`/`Some(true)`/`None`} × site kind {ADT ctor, closure, VecLit} → {stack
  slot, heap verbatim}; sentinel behaviour class: inc/dec drift on `IMMORTAL_RC` is
  value-preserving, free path unreachable, COW rc==1 never satisfied on a stack vec,
  write-use vecs decline stack.
- **`extern_call.rs` sibling gate (B3.5):** the four-leg truth table {declared only-read
  ±} × {arg borrowed at site ±} × {sibling registered ±} × {toggle ±} — exactly one
  TRUE-all cell targets `str-len$borrowed`; all 15 other cells target the consuming
  export with today's emission (byte-identity leg included).
- **`got.rs` (with B1-be/B3.0):** exhaustion / freeze semantics / trap-patch-in-place —
  the 0495-named unchecked-allocation cells.
- **`control_flow/sparkability.rs` density axis (B4):** {facts present, absent} ×
  {alloc-dense body, compute-dense body, mixed} × {threshold boundary −1/at/+1} →
  {admitted, declined, axis-inert}; negative: facts-absent admission set identical to
  pre-change for the full existing sparkability fixture set.

Every matrix's negative/else-arm class doubles as the unit-tier half of the L-B1
byte-identity obligation. `/qa`'s e2e lanes (fences S1–S6, L-C1/L-C2, L-M1) sit above
these; the matrices are the `/dev` unit tier `/qa` audits at seam × class grain.

### 13.6 Typecheck consumption contracts (S102 coordination pins)

Two producer-side pins from the typecheck staging plan
(`design/typecheck/ownership-inference.md` §13.6) that the backend consumers in this
ladder rely on — recorded here so `/dev` builds against them, not against §3.3's earlier
per-visit phrasing:

- **(b) Site facts are written in ONE post-convergence annotation walk**, never
  incrementally mid-fixpoint. Backend consequence: when codegen receives a `MonoDefn`,
  its facts and provenance are **complete and final** — there is no partially-annotated
  state. `fact-absent` therefore always means "the analysis concluded conservative (or
  did not run)", never "not yet written", which is exactly the reading the §2.2
  else-arm discipline assumes. No backend staleness handling, no re-read, no ordering
  dependence on fixpoint internals.
- **(d) Projection provenance is `Symbol`-keyed, with a shadowing guard.** The
  provenance root arrives as the root binding's `Symbol` — matching the as-built keying
  of `borrowed_vars` and the last-use machinery, so the §3.3 provenance-map parameter to
  `collect_var_uses` plumbs without a new key type. Where a body rebinds a name that is
  (or roots) a live provenance root, typecheck emits `provenance: None` for projections
  whose root would be ambiguous under that name — the backend performs **no
  disambiguation of its own** (the §3.3 narrowness counterweight): `None` selects the
  ordinary Decision-24 materialization path. The shadowing shape is a pinned scenario
  row on both sides (typecheck §13.7 transfer matrix; the §13.5 `compute_last_uses`
  matrix here).

---

## Next skills

- `/dev` (backend, narrow) — execute the §13.2 ladder in order: B0-be (H1) with the
  capture wave; B1-be + B3.0 once the `/arch` types change-set lands; B3.1–B3.5 + B4
  after the seam, each with its scenario matrix (§13.5) and scoped re-baseline (§13.1).
- `/qa` — corpus + capture script + goldens per `tests/plan/s102-test-plan.md` §1.5/§4,
  consuming the §13.1 normalization contract; observe guard flips per their §5 map.
- `/arch` — author the types change-set (ModeSummary carrier + fact tables +
  `PrimitiveBody::{Extern, Inline}` + `is_callable_target()` + `CACHE_SCHEMA_VERSION`
  v11→v12) — B1-be and B2 consume it; approve the B1-be/0482 `public-api.txt` diffs.
- `/sprint` — wave the ladder per §13.2's dependency column; hold the close-short
  protocol (I-G5/I-G6 at the seam; 0474/0483 guards stay RED if B3.1 carries).
- `/design` (int) — the T1 full-cure sizing is Block A's; no backend seam changes
  needed beyond §8.3 (unchanged).
