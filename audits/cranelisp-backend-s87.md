# cranelisp-backend — S87 Stage-B Deep Audit

> **Predecessor.** This pass refreshes `audits/backend-20260423.md` (+ its
> `-current-state.mmd` / `-target-state.mmd`). The 04-23 audit is the named
> baseline; this is a **delta + currency** pass, not a from-zero re-audit. The
> 04-23 files are *superseded* but per the never-delete-archived rule stay in
> place. Companion diagram: `audits/cranelisp-backend-s87-current-state.mmd`.
>
> **Method.** 7-lens checklist per `sprints/SPRINT.md` Stage B (i duplication;
> ii dead paths; iii function budget; iv RC-symmetry/consuming-inc; v
> resolution-seam; vi interim-arch residue; vii cross-crate/host-callback).
> LOC pre-pass: `audits/loc-s87.md`. **Read-only on code** — findings route as
> FIXMEs to `/dev` (backend) / `/arch` (cross-crate) / `/design`.
>
> **Date.** 2026-06-20 (S87 Wave 1b). Corrected prod LOC 9,487 (#2 surface).
> Deep-scrutiny modules: `compiler/{control_flow.rs 1463, mod.rs 1279,
> vec_codegen.rs 1026, trace_codegen.rs 702}`; `lib.rs` is 87% inline-test
> (corrected 647) — **not** a god module, not size-weighted.

---

## 1. Baseline reconciliation (every 04-23 finding)

| 04-23 finding | Then | Now | Status |
|---|---|---|---|
| **HIGH-1** overlapping compile entrypoints + duplicated "single source of truth" | two public per-fn compile entries; `compile_to_object` phantom stub; two `build_isa`; two `CompileContext` builders | `compile_to_object` stub **deleted** (S75 W2); `compile_to_module` is the sole **production** CLIF entry; `Jit::compile_defn`/`build_compile_context` now `pub(crate)` and **test-only callers**; `jit.rs::build_isa()` still a **separate production helper** hardcoding `is_pic=false` (used by `Jit::new`) parallel to `cache::object::build_isa(bool)` | **PARTLY RESOLVED** — entrypoint convergence largely landed; **ISA duplication persists** (F1) and the `Jit::compile_defn` family is now dead-in-prod (F2) |
| **HIGH-2** mini-monoliths + 100+-line functions | control_flow 1948 / mod 1560 / vec_codegen 1315; 6 fns >100 lines | control_flow 1463 / mod 1279 / vec_codegen 1026 (all shrank); but `compile_par_bind_continuation` 233, `compile_resolved_call` 271, `build_adt_drop_glue_fn` 180, `compile_trace` 215, `compile_lambda_body` 153, `build_closure_drop_glue` 150 still over budget | **PARTLY RESOLVED** — files smaller, **largest functions unchanged or worse** (`compile_resolved_call` grew 153→271) (F4) |
| **HIGH-3** helper duplication (lookup walkers, `emit_extern_call_1..4`, COW skeletons) | `resolve_got_target`/`resolve_func_arity` twin walkers; arity-ladder externs; vec-set/push COW clones | `emit_extern_call_1..4` arity ladder **still present** (control_flow has `_1`, vec_codegen has `_2/_3/_4`); `compile_vec_set_cow`/`compile_vec_push_cow` still clone the COW skeleton; the lookup walkers persist as `resolve_in_module`/`arity_in_module` | **STILL OPEN** (F5, F6) |
| **MED-1** cache migration residue (~30 markers; `CacheMetadata`; `got.rs`/`codegen_types.rs` re-exports; "Wave 2b" comments) | ~30 deprecated/back-compat markers | `cache/mod.rs` 17 + `serialize.rs` 16 + `object.rs` 12 markers (≈45 now, not fewer); `CacheMetadata` "Wave 2b parallel migration" comment + `#[allow(deprecated)] build_cache_packet` **still live**; `got.rs` + `codegen_types.rs` re-export shims **still present** | **STILL OPEN / slightly regressed in count** (F7) |
| **MED-2** test mis-location (3,932 test lines in lib.rs; compiler/*.rs 0 local tests) | 0 local compiler tests | compiler/*.rs now carry local tests: control_flow 10, vec_codegen 8, mod 7, apply 6, trace 10 (`literals.rs`, `match_codegen.rs` still 0); lib.rs still ~6,138 test lines | **SUBSTANTIALLY IMPROVED** — narrow tests landed next to code; lib.rs still a large warehouse but no longer the *only* home (F12, low) |

**Counts:** of 5 baseline findings — **0 fully resolved**, **3 partly resolved**
(HIGH-1, HIGH-2, MED-2), **2 still open** (HIGH-3, MED-1). Net direction:
positive on structure (files shrank, tests localized, phantom entry deleted),
but the **duplication families HIGH-3 named are intact**, and the convergence
HIGH-1 promised left two dead-in-prod artifacts behind.

**Sketch-audit HIGH patterns (`sketch/audits/codegen.md`) — vigilance check:**
- *Duplicate heap classification* → **NOT reintroduced.** `HeapCategory::classify`
  (`heap.rs:438`) is the single source; `signature_heap_category`
  (`compiler/mod.rs:2032`) is a thin `ConcreteType::from_type` → `classify`
  wrapper. All `AlwaysHeap`/`NeverHeap`/`Mixed` consumers route through it. Good.
- *ISA built separately from JIT path* → **STILL PRESENT** (F1).
- *Panics in non-test code* → spot-checked; codegen errors flow through
  `CranelispError::CodegenError` / `CompilationError`, not `panic!`. No new
  panic-in-prod introduced.

---

## 2. Findings (severity-ranked)

### F1 — [Important] Two `build_isa` helpers persist; JIT path constructs ISA ad-hoc (HIGH-1 residue + sketch HIGH pattern)
`crates/cranelisp-backend/src/jit.rs:49` (`build_isa()`, hardcoded `is_pic=false`)
vs `crates/cranelisp-backend/src/cache/object.rs:144` (`build_isa(is_pic: bool)`).
The two bodies are **byte-identical** except `jit.rs` hardcodes
`set("is_pic","false")` where `object.rs` parameterizes it. `Jit::new`
(`jit.rs:321`) + `new_with_symbols` (`jit.rs:357`) call the local one; every
object/exe/linker site already calls `cache::object::build_isa`. This is exactly
the `sketch/audits/codegen.md` HIGH "ISA constructed separately from the JIT
path" pattern, and the 04-23 audit's #1 recommendation (Phase 1) that did not
land. **Consolidation:** delete `jit.rs::build_isa()`; have `Jit::new` /
`new_with_symbols` call `crate::cache::object::build_isa(false)`. Pure deletion,
no behavior change, no public-surface change (`jit.rs::build_isa` is `pub(crate)`).
→ FIXME `target: /dev`. Cite Principle 7 (single source of truth).

### F2 — [Important] `Jit::compile_defn` + `build_compile_context` + `CompileArtifacts` are dead in production (called only from tests) — dead-path class (lens ii)
`crates/cranelisp-backend/src/jit.rs:587` (`compile_defn`), `jit.rs:709`
(`build_compile_context`), `jit.rs:36`–`42` (`CompileArtifacts` incl. its
`disasm` field). **Every** caller is `#[cfg(test)]`: `jit.rs:1091`, `jit.rs:1282`,
`compiler/control_flow.rs:2341`, `lib.rs:4432`. The production CLIF path is
`compile_to_module` → `compile_to_module_impl` → `compile_defn_in_module`
(`lib.rs:1341`). This is the same zero-production-call-site class as the
`produce_disasm` dead-field just cleaned in Wave 0 (FIXME 0418). Of particular
note: `CompileArtifacts.disasm` is **still populated** (`jit.rs:647`
`set_disasm(true)`, `jit.rs:687`) — the eager-disasm machinery the D1b
introspection-repl-only ruling + FIXME 0325 retired survives **here**, on a
test-only path, even though `0418` removed the int-side `Introspection.disasm`
field. **Consolidation:** either (a) collapse `Jit::compile_defn` into a thin
test-helper that delegates to the production `compile_defn_in_module` path (so
tests exercise the real code), or (b) if it must stay as an independent test
harness, drop the `disasm`/`set_disasm` capture (eager disasm is retired;
on-demand `produce_disasm` is the live path). HIGH-1's "decide whether
`Jit::compile_defn` remains public or becomes a thin wrapper" is now answerable:
it is private and test-only — make it a wrapper or delete it. → FIXME `target: /dev`.
Cite Principle 8 (no interim implementations), Principle 5 (tests exercise the
real seam).

### F3 — [Important] vec-set vs vec-push consuming-inc convention is NON-uniform (RC-symmetry, lens iv; S86 DEF-2/DEF-3 + `vec_set_copy` seed)
This is the headline S86 seed. The **decision** is uniform — both `vec-push`
(`vec_codegen.rs:481`) and `vec-set` (`vec_codegen.rs:254`) and the generic
`compile_consuming_arg_list` (`apply.rs:483`) share the single
`element_consuming_inc` predicate (`vec_codegen.rs:1467`) and the inc-iff-heap-
typed-Var rule. But the **emission strategy diverges**:

- **vec-push & generic args:** emit the consuming inc **in codegen, up-front**,
  then store without inc on every (fast/grow/copy) path. `vec_push_copy`
  (intrinsics `vec_runtime.rs:238`) does **NOT** inc `val`.
- **vec-set:** the COW mutate path emits a gated inc in codegen
  (`vec_codegen.rs:371`), but the **copy path** relies on `vec_set_copy`
  (intrinsics `vec_runtime.rs:188`,`:220`) inc'ing `val` **unconditionally** at
  runtime, then **compensates** a temporary's over-inc with a codegen dec
  (`emit_vec_set_copy_temp_compensation`, `vec_codegen.rs:418`).

So one conceptual operation ("store a heap element into a Vec, gaining a ref iff
it is a live Var") is implemented with **opposite divisions of labor**:
vec-push = codegen-inc / runtime-never-inc; vec-set = runtime-always-inc /
codegen-compensate. Both are *correct* (the test suite is green), but it is a
Decision-24 uniformity gap and a textbook divergence point — a future change to
the vec-push model (or to `vec_push_copy`/`vec_set_copy`) has to remember the
mirror does the opposite. The `emit_vec_set_copy_temp_compensation` helper +
the unconditional runtime inc exist **only** to paper over this asymmetry.

**Consuming-inc-symmetry verdict:** the predicate is unified; the **emission
convention is not**. vec-set is the sole outlier. **Consolidation (the
fully-symmetric design):** make vec-set match vec-push — hoist the consuming inc
to up-front in `compile_vec_set` (gated by `element_consuming_inc`, like
vec-push), **stop** `vec_set_copy` inc'ing `val` (drop the
`call_elem_fn(elem_inc_fn, val)` at `vec_runtime.rs:220`), and **delete**
`emit_vec_set_copy_temp_compensation`. This removes a runtime branch, a codegen
helper, and the only labor-split divergence in the RC convention.
**Cross-crate coupling (lens vii):** the `vec_set_copy` change is a
`cranelisp-intrinsics` edit — `vec_set_copy`'s ABI (`elem_inc_fn` still passed
for *retained* elements) is unchanged, only the new-`val` inc is dropped, but
the two crates must land together with a unit test on each side (intrinsics:
`vec_set_copy` no longer inc's `val`; backend: vec-set copy path inc's a Var,
transfers a temporary, with no compensation). → FIXME `target: /arch`
(cross-crate RC-model alignment; `/arch` dispatches the paired `/dev backend` +
`/dev intrinsics` change). Cite Principle 7 + Decision 24.

### F4 — [Important] Largest codegen functions still over the ~100-line budget; `compile_resolved_call` grew (HIGH-2 residue, lens iii)
`compiler/apply.rs:~118` `compile_resolved_call` **271 lines** (was 153 at
04-23 — grew with the platform-effect fault-guard funnel);
`compiler/control_flow.rs` `compile_par_bind_continuation` **233**,
`compile_lambda_body` **153**, `build_closure_drop_glue` **150**, `compile_lambda`
**146**; `compiler/vec_codegen.rs` `build_adt_drop_glue_fn` **180**,
`compile_vec_set_cow` **130**; `compiler/trace_codegen.rs` `compile_trace` **215**,
`compile_trace_wrapper_fn` **209**. Each braids multiple protocols (builder setup
+ ownership + capture loading + branching + cleanup) in one body, per the 04-23
diagnosis — unchanged. `compile_resolved_call` is now the worst offender and the
one most actively edited (S81 fault-guard). **Consolidation:** the 04-23
protocol-boundary splits still apply — `compile_resolved_call` → builtin /
trait-method / sig-dispatch / auto-curry arms; `compile_par_bind_continuation` →
fn-decl / inner-body / result-buffer / closure-materialize. → FIXME `target: /dev`.
Cite Principle 6 (complexity budget) + `src/CLAUDE.md` ~100-line guidance.

### F5 — [Important] `emit_extern_call_1..4` arity ladder still present (HIGH-3 residue, lens i)
`compiler/control_flow.rs:209` (`emit_extern_call_1`),
`compiler/vec_codegen.rs:1211/1238/1267` (`_2`/`_3`/`_4`), plus a separate
`emit_extern_call_in_wrapper` (`control_flow.rs:2023`). Same
signature-building + call-emission pattern cloned by arity — the exact HIGH-3
"do not add `emit_extern_call_5`" trap the 04-23 agent-guidance flagged. The
ladder is also **split across two modules** (`_1` in control_flow, `_2/_3/_4` in
vec_codegen) so a contributor reaching for arity-1 in vec_codegen would clone a
fifth. **Consolidation:** one slice-based helper `emit_extern_call(name, &[Value],
span)` that builds the signature from `args.len()`, placed in `compiler/mod.rs`
(or a small `extern_call.rs`) so all modules share it. → FIXME `target: /dev`.
Cite Principle 7.

### F6 — [Suggestion] vec-set / vec-push COW skeletons still clone the branch structure (HIGH-3 residue, lens i)
`compile_vec_set_cow` (`vec_codegen.rs:288`) and `compile_vec_push_cow`
(`vec_codegen.rs:505`) share the identical COW skeleton: load rc → `icmp ==1` →
`brif` to unique/mutate vs copy → merge block with one I64 param. Only the
mutate-block body differs (set: dec-old + store-at-idx; push: cap-check +
store-at-len or grow). This is the 04-23 HIGH-3 "extract a shared COW branch
skeleton with fast/slow callbacks" item. Two sites only (not the 3-site
extraction threshold), so **Suggestion** not Important — but it is the natural
companion to F3 (if vec-set's copy path is reworked to match vec-push, the two
COW bodies converge further and the skeleton extraction becomes cheap). Revisit
together with F3. → FIXME `target: /dev` (or fold into F3's change-set). Cite
Principle 7.

### F7 — [Important] Cache-layer migration residue persists and has not shrunk (MED-1 residue, lens vi)
`cache/mod.rs` 17 markers, `cache/serialize.rs` 16, `cache/object.rs` 12 (~45
total — the 04-23 "~30" did not decrease). Specifics still live:
`CacheMetadata` "Wave 2b parallel migration" envelope + `#[allow(deprecated)]
build_cache_packet` (`cache/object.rs:188`); the deliberate "no `#[deprecated]`
attribute because it would surface warnings" shims (`cache/serialize.rs:25,336`,
`cache/mod.rs:211`); the `got.rs` + `codegen_types.rs` 9-line re-export shims
(both still say "Later sprints remove the re-export"). The "Wave 2b parallel
migration" / "remove later" comments are interim-architecture residue
(Principle 8) with no scheduled deletion sprint — the MED-1 risk ("temporary
compatibility layers become permanent") is materializing. **Consolidation:** a
deletion pass whose success criterion is removal of `CacheMetadata`,
`build_cache_packet`'s deprecated envelope param, and the `got.rs`/
`codegen_types.rs` shims (verify no external `cranelisp_backend::got::GotTable` /
`codegen_types::*` consumers first — both re-export from `cranelisp-types`, so
callers should import from there directly). → FIXME `target: /dev`. Cite
Principle 8 + Principle 7.

### F8 — [Suggestion] `exe.rs::generate_startup_object` carries stale `#[allow(dead_code)]` + "currently red, re-wires S77" comment but is now LIVE (lens vi)
`crates/cranelisp-backend/src/exe.rs:72-77`. The comment says "the only non-test
caller is int (currently red post-W2/W3; re-wires S77)" and applies
`#[allow(dead_code)]`. As of now the function **is** wired —
`src/session_v4.rs:2098` calls it via the int re-export (`src/exe.rs:50`). The
`allow` is suppressing a warning that would no longer fire, and the comment
documents a transient state two+ sprints stale. **Consolidation:** remove the
`#[allow(dead_code)]` and the stale comment block (and on `generate_startup_object_checked`
at `:120`, `:396` if likewise live). Confirm `cargo check -p cranelisp-backend`
stays warning-clean after removal. → FIXME `target: /dev`. Cite Principle 8.

### F9 — [Suggestion] `FunctionArtifacts` survives as a `pub(crate)` internal helper though S75 §2.6 scheduled its deletion (lens vi)
`crates/cranelisp-backend/src/lib.rs:262` (`struct FunctionArtifacts`),
returned by `compile_defn_in_module` (`lib.rs:1349`,`:1403`) and aggregated into
the boundary `CompilationArtifacts` (`lib.rs:1105`). The S75 §2.6 deviations
table (in `design/backend/backend.md`) lists `FunctionArtifacts` among the types
"deleted" by the W2 rotation. It is **not** the boundary type (that is correctly
`CompilationArtifacts`, `lib.rs:292`, matching `public-api.txt:535`), so this is
cosmetic — but the design doc claims a deletion that did not occur, a
design/as-built drift. **Consolidation:** either inline the two fields
(`clif_ir`, `code_size`) `compile_defn_in_module` actually returns into a tuple
or directly into the aggregation, deleting the struct; or update
`design/backend/backend.md` §2.6 to record that `FunctionArtifacts` survives as
an internal per-symbol helper (not a boundary type). → FIXME `target: /design`
(reconcile the doc) — the as-built is correct, the doc overclaims.

### F10 — [Suggestion] `produce_disasm` host-disasm path (lens vii — host-callback hygiene)
`crates/cranelisp-backend/src/lib.rs:1216` (`produce_disasm`), `:1261`
(`disasm_host`), `:1306` (`disasm_all`). The on-demand disasm entry was correctly
wired in S87 Wave 0 (FIXME 0418 closeout) and reads `got().load_slot` +
`code_size` per D41 — verified live and matching the facade §2.1. No defect here;
recorded for completeness as the **one** REPL-only host-callback surface in the
crate. The JIT-vs-`--link` host-callback divergence the S86 seed names (lens vii,
FIXME 0407) is **NOT in backend** — backend emits identical CLIF for both modes
(BC §3 invariant 6; the `Module` impl at finalize decides resolution). The
divergence lives at the platform/intrinsics ABI boundary (FIXME 0407 targets
`/arch` + `/platform` + `/intrinsics`). Backend's contribution to that family is
the single GOT-indirect dispatch chokepoint (`apply.rs:521`
`compile_direct_call`) where the platform-effect fault-guard stamp lands — this
is correctly unified across the `BuiltinFn` arm and the bare-import
`compile_var_apply` path (S81/FIXME 0337 residual close). **No finding** — the
crate is clean on lens vii; the divergence is a sibling-crate concern. (This
entry exists so the synthesis can cite "backend confirmed clean on host-callback
divergence" rather than silence.)

### F11 — [Suggestion] Resolution-seam: twin symbol-table walkers persist (HIGH-3 residue, lens v)
`compiler/mod.rs` carries `resolve_in_module` (110 lines), `arity_in_module`
(173 lines), and the public `resolve_got_target` / `resolve_func_arity` /
`resolve_platform_effect_target` that all walk import chains + qualified names +
global fallback, differing only in the payload read from the resolved
`ModuleEntry`. The 04-23 HIGH-3 recommendation ("one symbol-table walker
parameterized by what to read from the resolved entry") is unaddressed. These
are the resolution seam; consolidating them is the lens-v item. Lower priority
than F1/F3/F5 because the walkers are correct and individually readable, but the
parameterized-walker extraction would also shrink `mod.rs` (F4). → FIXME
`target: /dev` (fold with F4/F5 as a `compiler/mod.rs` resolution-helper pass).
Cite Principle 7.

### F12 — [Suggestion] `lib.rs` remains a large test warehouse; `literals.rs` / `match_codegen.rs` have no local tests (MED-2 residue, lens i)
`lib.rs` is 6,785 lines, ~6,138 of them test (87% — the LOC pre-pass
correction). MED-2 has **substantially improved** — compiler modules now carry
local tests (control_flow 10, vec_codegen 8, mod 7, apply 6, trace 10) — but
`compiler/literals.rs` and `compiler/match_codegen.rs` still have **zero** local
tests, and lib.rs is still the default home for new behavior tests. **Not a
blocker** — the structural improvement is real and the suite is green. Continue
the MED-2 trajectory: new compiler-behavior tests land in the owning module;
add narrow tests for `literals.rs` (literal lowering) and `match_codegen.rs`
(pattern lowering) when those modules are next touched. → FIXME `target: /qa`
(coverage trajectory) — low priority.

---

## 3. Synthesis input (for /arch Wave 2a)

**Top cross-cutting items for the backlog:**
- **F3 (vec-set/push RC-convention non-uniformity)** is the S86-seed headline and
  the one genuine cross-crate item — routes to `/arch` for paired backend +
  intrinsics RC-model alignment. The fully-symmetric design removes a runtime
  branch and a codegen compensation helper.
- **F1 (ISA duplication)** is the cleanest single-deletion win and closes a
  long-standing sketch-HIGH pattern + the 04-23 #1 recommendation.
- **F2 (dead-in-prod `Jit::compile_defn`/`CompileArtifacts.disasm`)** is the same
  dead-path class S87 Wave 0 just cleaned for `produce_disasm` — and it harbors
  the last eager-disasm capture the D1b ruling retired.
- **F5/F11 (duplication families HIGH-3 named)** are intact 14 months later — the
  recurring-duplication signal `memory/feedback_review_root_cause_and_duplication`
  warns about; worth a single consolidation change-set rather than another
  copy-paste.
- **F7 (cache migration residue)** has not shrunk and is the Principle-8
  "temporary becomes permanent" risk materializing — needs a scheduled deletion
  pass with a removal success-criterion.

**Lens vii verdict for backend:** clean. The JIT-vs-`--link` host-callback
divergence (FIXME 0407) is NOT a backend pattern — backend emits identical CLIF
for both modes; the divergence is the platform/intrinsics ABI boundary. Backend's
dispatch chokepoint (`compile_direct_call`) is correctly unified.
