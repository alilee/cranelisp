# Backend audit-drain — S111 (R4/R5/R6/R7 design)

> **Owner**: `/design` (backend). Subordinate to `backend.md` §"S111 audit-drain".
> Authored S111 Phase 3 against `audits/cranelisp-backend-s110.md` R2/R4/R5/R6/R7
> and `audits/cranelisp-backend-s107.md` R1/R2/R3/R4/R5/R7 (user ruled SHIP ALL,
> 2026-07-17). This doc is the `/dev` implementation spec for the four
> behaviour-invariant drains and the GOT-exhaustion consumption. R2 (pin the
> three hard-miss `CodegenError` families) is `/qa`-plan + test-tier, out of this
> doc; R8 (doc truth pass) landed in `backend.md` + `ownership-codegen.md`.
>
> **Binding wave-order (SPRINT.md §1 constraint 1).** R2 negatives pin the
> keyed-miss families FIRST → **R4 (hygiene) + R5 (funnel splits) land
> byte-identical** → the emission-affecting schema-20 ownership wave last, with
> its own scoped re-baseline. R6 (drop-glue) and R7 (GOT) are schema-independent
> and ride the backend-drain track at any point before the ownership wave. **Do
> not interleave R4/R5 with the ownership wave** — it muddies golden-CLIF
> attribution.

---

## 0. The byte-identity gate — the invariant every R4/R5 change is measured against

R4 and R5 are **behaviour-invariant refactors**. The acceptance is not "tests
still pass" but **CLIF byte-identity**: the emitted Cranelift IR for every
function is textually unchanged before vs after. Mechanism (already in-tree —
reuse it, do not reinvent):

- **The scoped gate**: `tests/golden_clif_w0b.rs` (`capture_frames` →
  `CRANELISP_CODEGEN_DUMP='*'` cold-cache `--run --no-cache`, sorted framed
  dumps, byte-compared to a committed golden). It already asserts REPL/`--run`
  parity of the dump before comparing to the golden.
- **The dump hook**: `CRANELISP_CODEGEN_DUMP` (grammar `*` | `module::symbol` |
  bare-module; `lib.rs::clif_dump_matches`, unit-pinned) writes per-symbol CLIF
  to stderr. This is the codegen-layer inspection contract; it is
  **byte-identical-off** and reads the same rendered `art.clif_ir`
  `compile_to_module_impl` aggregates.

**`/dev` byte-identity protocol for each R4/R5 change-set:**

1. BEFORE the change, capture a corpus dump: run a representative program set
   (the `golden_clif_w0b` corpus + a fuller sweep — the exemplar Sudoku, the
   `tests/` e2e programs that reach backend) under `CRANELISP_CODEGEN_DUMP='*'
   --run --no-cache` and save the sorted framed output.
2. Apply the refactor (pure extraction — see §2/§3 for what "pure" means here).
3. Re-capture. `diff` must be **empty**. A non-empty diff means the extraction
   was not behaviour-preserving — the refactor is wrong, not the golden.
4. `cargo nextest run --no-fail-fast` green (the golden gate + the unit tier).

**Why byte-identity is achievable here**: every R4/R5 move below is a *pure
lexical extraction* — code moves verbatim into a named callee, argument order
and side-effect order preserved, no predicate re-evaluation reordered, no new
allocation on the emitted path. Pure extraction cannot change emitted IR. The
one non-lexical R4 item (`module_aliases` drop) is byte-identical for a
different reason: the field is **UNREAD** (§1.4), so removing it removes no
emitted instruction.

---

## 1. R4 — the hygiene batch (one change-set, `/dev` backend)

Four sub-items, landed together (S107 R1+R2+R3 + the W3 `module_aliases` member).
`public-api.txt` regenerated in the SAME change-set; `cargo check -p
cranelisp-backend` warning-clean is the completion bar.

### 1.1 Delete `jit.rs::build_isa`; single ISA construction point

`jit.rs::build_isa` (`jit.rs:49`, `pub(crate)`, hardcodes `is_pic=false`) and
`cache::object::build_isa(is_pic: bool)` (`cache/object.rs:144`) have identical
bodies modulo the parameter. Both carry "single construction point" rustdoc
(`jit.rs:46-48` "for the entire backend" vs `cache/object.rs:10-18` "single ISA
construction point (architecture decision 7)") — at most one is true. **4th
consecutive audit.**

- **Delete** `jit.rs::build_isa` (lines 46-76).
- **Route** the two production callers `jit.rs:321` and `jit.rs:357` (inside
  `Jit::new*` / `new_with_isa`) through `crate::cache::object::build_isa(false)`.
  `is_pic=false` is the JIT-mode value (JIT patches relocations in-process; PIC
  is the object/`--link` path, `exe.rs:127` passes `true`).
- **Test callers**: `jit/tests.rs:6-7` (`test_build_isa`) and
  `primitives_inline.rs:428/434` switch to `crate::cache::object::build_isa(false)`
  (or the crate-root re-export `crate::build_isa`, which already points at
  `cache::object::build_isa`, `lib.rs:144`). Delete `jit/tests.rs::test_build_isa`
  if it purely tested the deleted fn (the object-side `cache/object/tests.rs`
  `test_build_isa_{pic,non_pic}` already cover both flags).
- **Rustdoc collapse**: the surviving `cache/object.rs:10-18` claim is the true
  one; delete the contradictory `jit.rs:46-48` claim. `lib.rs:32-33` (crate-root
  re-export doc) is already correct — leave it.
- **Public API**: `jit::build_isa` is `pub(crate)` — no public-surface change;
  the crate-root `pub use cache::object::build_isa` is unchanged. `public-api.txt`
  byte-identical.

### 1.2 Wave-2b shim / marker deletion

The stated justification is vacuous — the markers say the shims exist for
external "pre-Phase-5 callers", and a workspace grep finds **zero** consumers of
`CacheMetadata`, `cranelisp_backend::got::*`, or `cranelisp_backend::codegen_types::*`
outside the crate. **4th audit for the cache half.**

- `#[allow(deprecated)]` ×8 under `cache/` (`cache/mod.rs:412/:429/:476/:538/:589`,
  `cache/object.rs:37/:188/:333`) — delete the attributes and the deprecated
  items they cover.
- `CacheMetadata` envelope re-wrap (`cache/mod.rs:502-506`) + the deprecated
  `build_cache_packet` envelope parameter (`cache/object.rs`) — remove the
  envelope; `CachedModule.metadata` collapses to the live shape.
- `got.rs` (104 ln) + `codegen_types.rs` (13 ln) re-export shims — **delete**.
  The S101 slab-invariant test module inside `got.rs` (`got.rs::slab_growth_tests`
  / `slab_growth_tests`, ~`got.rs:37-104`) is **rehomed, not deleted** — move it
  next to its real subject (`cranelisp-types`'s GOT, or a backend
  `got/tests.rs` sibling if the assertions are backend-side). `GOT_TABLE_SIZE` /
  `NULLARY_TAG_THRESHOLD` consumers import from `cranelisp-types` directly.
- `exe.rs:54` (`generate_startup_object`, + `generate_startup_object_checked`
  `:121` / `define_cstr_data`) — **premise corrected (FIXME 0635 I3, S113):** this
  backend copy is **DEAD in production, exercised only by `exe/tests.rs`**. The
  original bullet's "LIVE … called via `src/exe.rs:50`, production-live" claim
  conflated it with int's OWN independent copy. The production `--link` startup-`.o`
  emission was RELOCATED to int at **S76 §4.4** (BC §3 invariant 7 — int owns the
  `_main`/`start` alias); int's `src/exe.rs::generate_startup_object` (called from
  `session_v4/lifecycle.rs`) is the live one and has **already drifted**: it takes
  five params (adding `stub_entry_symbol` + a `platform_layout_checks` slice for
  layout-hash baking) where this backend copy takes three — a strictly less-capable
  predecessor, not a synced reference. CS-1 already fixed the source rustdoc marker
  (`exe.rs:72-77` now honestly says "Dead in production"); this bullet's premise is
  the residue.
  - **Disposition ruling (`/design`(backend), S113, P7/P8):** **DELETE** the orphaned
    backend copy — `generate_startup_object`, `generate_startup_object_checked`,
    `define_cstr_data`, and `exe/tests.rs` — mirroring the §1.3 `compile_defn`
    deletion exactly (a parallel front door production never runs → delete, do not
    gate). Rationale: it is a superseded interim (Principle 8) that has already
    diverged from int's production copy (Principle 7 — a drifted "reference" misleads
    worse than none), and the seam categorically belongs to int (S75 W3 `pub(crate)`
    narrow + S76 §4.4 relocation + BC §3 invariant 7). Startup-`.o` emission is
    validated where it is owned — int's copy via the `--link` e2e suite
    (`tests/link.rs`). Testability rider for `/qa`/int: if byte-level assertions on
    the startup `.o` (Export `start`, import relocations, layout-check baking) are
    judged worth retaining, re-home them at int (`src/exe.rs:50` is `pub`, unit-testable
    there) — do NOT keep them at backend to justify the dead code.
  - `/dev` action (in-wave): delete the three fns + `exe/tests.rs`, drop the
    `#[allow(dead_code)]`; regenerate `crates/cranelisp-backend/public-api.txt` in the
    same change-set if `generate_startup_object`/`_checked` are on the surface (they
    are `pub(crate)` per the S75 W3 narrow — expect no baseline delta; confirm).
- **Public API**: `CacheMetadata` / `build_cache_packet` / `got` / `codegen_types`
  are on the public surface (`public-api.txt`). Regenerate the baseline in the
  same change-set per the baseline-diff discipline; with zero external consumers
  the risk is nil.

### 1.3 `compile_defn` test-harness disposition (S107 R3-revised — the required bar)

`Jit::compile_defn` (`jit.rs:587`), `compile_defn_with_targets` (`:610`),
`build_compile_context` (`:749`), and `CompileArtifacts` (`jit.rs:35`) are all
production-compiled (`pub(crate)`, not `#[cfg(test)]`) but have **exclusively
test callers** — a parallel compilation front door production never runs. The
A.4-revised done-bar (cure-the-risk, not just gate it):

- **Delete** `compile_defn`, `compile_defn_with_targets`, `build_compile_context`,
  `CompileArtifacts`, `IntrinsicIds`/`IntrinsicFuncIds` if they fall dead with
  them, and the unconditional `set_disasm(true)` (`jit.rs:687`).
- **Re-seam the CLIF-probe tests** through the production
  `compile_to_module`/`compile_defn_in_module` seam. A thin `#[cfg(test)]`
  wrapper in `test_support.rs` that only *delegates* (no context assembly of its
  own) is acceptable — it must build its `CompileContext` the way
  `compile_to_module_impl` does, so the probe tier stops drifting from
  production (S110 §2.6 risk / S107 A.2 risk 6). The execution-tier helpers
  (`test_compile_and_run` etc.) already ride `compile_to_module` — only the
  CLIF-text probe tier moves (`module_assembly_tests.rs`,
  `{par,poll,select}_codegen_tests.rs`, `temp_drop_rc_tests.rs`, `jit/tests.rs`,
  the `launch.rs`/`resolution` test mods).
- Disasm needs served by the production `produce_disasm` or local per-test
  opt-in (the only consumer is `jit/disasm_tests.rs`).
- **Removes the W4/S77 `FIXME(W4)` + retired-facade citation** at `jit.rs:26-33`
  (the `CompileArtifacts` rustdoc cites `facades/backend.md` §"jit shape DTOs",
  retired S75) — it goes with the struct.
- **Public API**: all `pub(crate)` — `public-api.txt` unchanged.
- **Doc consequence**: `implementation-slice-s66.md` row 1(d) ("`Jit::compile_defn`
  deletion observed in source") finally becomes TRUE — that one-shot is now cleanly
  archived at `design/backend/archive/implementation-slice-s66.md` (FIXME 0635 I4,
  S113; `archive/README.md` carries its row).

### 1.4 Drop `module_aliases` off `CompileContext`

`CompileContext.module_aliases` (`context.rs:88`, cloned at `:123`) is **threaded
but UNREAD since W3** — the `resolve_*` resolvers that consumed it for
qualified-name alias substitution are deleted; the backend keyed-reads
typecheck's `resolved_target` (no name resolution → no alias substitution). A
5th audit carrying it is a Principle-8 failure (no interim implementations).

- **Remove** the field from `CompileContext` (`context.rs:79-88`) and its clone
  arm (`:123`).
- **Remove** the `module_aliases` parameter from the `compile_to_module_impl`
  free fn (`lib.rs:637`), its call site in `compile_to_module` (`lib.rs:607/:626`),
  the per-body `CompileContext { module_aliases, .. }` construction (`lib.rs:856`),
  and the public `compile_to_module` signature.
- **This moves the `pub compile_to_module` signature** — the one public-surface
  change in the batch. Coordinate the int call-site with `/arch`'s Phase-2
  impact-table row ("`pub compile_to_module` signature moves"; int is a binary →
  e2e gate, no baseline). Backend `public-api.txt` regenerated in the same
  change-set.
- **Test callers** that pass `&module_aliases` (`jit/tests.rs`, the
  `*_codegen_tests.rs` family, `trace_codegen/tests.rs`, `fn_compiler.rs:1655`,
  `utilization.rs`, `temp_drop_rc_tests.rs`, `cache/object.rs:280-287`) drop the
  argument. Most are `dashmap::DashMap::new()` locals that simply delete.
- **Byte-identity**: an UNREAD field emits no IR. Removing it changes no emitted
  instruction — the golden corpus is byte-identical. (This is the reason the
  public-surface move is safe to land in the same byte-identical wave as R5.)

### 1.5 R4 landing order within the change-set

Do 1.3 (delete `compile_defn`) and 1.4 (drop `module_aliases`) together — both
touch the `CompileContext`/`compile_to_module` surface and the test harness; a
single re-seam of the probe tier handles both. 1.1 and 1.2 are independent and
can land in the same commit or adjacent. The whole batch is ONE change-set per
the audit R4 done-bar.

---

## 2. R5 — split `compile_resolved_call` (`apply.rs:430`, ~325 ln)

**4th audit; grew 153 → 271 → 323 → ~325.** The body is a `match resolved
{ BuiltinFn | TraitMethod | SigDispatch | AutoCurry | other }`. Post-W1 the
resolver noise is out; the split is a clean protocol-boundary extraction — one
named `FnCompiler` method per `ResolvedCall` variant, with the oversized
`BuiltinFn` arm further decomposed by dispatch class. **Pure extraction →
byte-identical.**

### 2.1 The dedup that also shrinks — `apply_target_has_got_slot`

Lines `585-591` (extern-primitive GOT-vs-extern decision) and `630-645`
(platform GOT-vs-extern decision) contain the **identical** predicate:

```
apply_target.and_then(|fq| self.ctx.entry_at(fq)).is_some_and(|(_, e)| e.callable_got_slot().is_some())
```

Extract once:

```
fn apply_target_has_got_slot(&self, apply_target: Option<&FQSymbol>) -> bool
```

Pure predicate, no side effects — both call sites become
`self.apply_target_has_got_slot(apply_target)`. Byte-identical (a pure predicate
evaluated at the same point yields the same branch). Principle 7 (single source
of truth): the "does the keyed entry carry a GOT slot" decision now has one home,
shared by the two GOT-dispatch arms.

### 2.2 The variant-arm extraction

Extract each `match` arm into a named `FnCompiler` method. Signatures take the
same locals the arm reads (`args: &[MonoExpr]`, `span`, `saved_tail`,
`apply_target`), preserving the `self.in_tail_position = saved_tail` assignment
*inside* the extracted body at its current position:

| New method | Source lines | Notes |
|---|---|---|
| `compile_builtin_fn_call(&mut self, op_name: &Symbol, args, span, saved_tail, apply_target)` | 443-679 (BuiltinFn arm) | Further split — §2.3 |
| `compile_moded_user_call(&mut self, sym: &Symbol, args, span, saved_tail, apply_target)` | 705-711 **and** 715-721 | **P7 dedup** — TraitMethod and SigDispatch arms are IDENTICAL below the `sym` bind (`compile_consuming_arg_list_moded` → set tail → `compile_direct_call` → `emit_post_call_decs` → `Ok`). Both arms become: bind `sym`, then `self.compile_moded_user_call(&sym, …)` |
| `compile_auto_curry_call(&mut self, target_name, args, applied_count, total_count, trait_resolution, span, saved_tail, apply_target)` | 723-747 (AutoCurry arm) | Short; extraction optional but keeps the match uniform |

After extraction `compile_resolved_call` is a ~35-line dispatch: the `match` with
each arm a one-or-two-line delegation, plus the unchanged `other =>` error arm
(752-755). The doc-comment (428-429) stays on the dispatcher.

### 2.3 Decomposing the `BuiltinFn` arm

`compile_builtin_fn_call` (the 443-679 body, ~235 ln) is a linear guard chain.
Extract the three heavy dispatch classes so the guard chain drops under budget;
the four inline-effect interceptors (bind/select/race/sleep) stay as short early
returns in the guard chain (they are 3-5 lines each):

| New method | Source lines | Dispatch class |
|---|---|---|
| `compile_extern_primitive_call(&mut self, op_name, args, span, saved_tail, apply_target)` | 530-592 | extern primitive: `string-identity` arg-list branch, `str-len` H3 RC-stat gate, then `apply_target_has_got_slot` → `compile_direct_call` else `compile_extern_call` |
| `compile_platform_or_direct_extern_call(&mut self, op_name, args, span, saved_tail, apply_target)` | 598-652 | unrecognized builtin: platform GOT-adopt arm (`apply_target_has_got_slot` → `compile_direct_call`) else as-built direct-extern fallback |
| `compile_inline_ring0_call(&mut self, op_name, args, span, saved_tail, apply_target)` | 654-679 | `try_emit_inline_primitive` with the drift fall-through to `compile_direct_call` |

`compile_builtin_fn_call` then reads: `bind`/`select`/`race`/`sleep` early
returns (453-487) → `is_vec_primitive` (493-501) → `trace_accessor_intrinsic`
(524-528) → `is_extern_primitive` → `compile_extern_primitive_call` → `!is_known_builtin`
→ `compile_platform_or_direct_extern_call` → `compile_inline_ring0_call`. ~60
lines of guard chain, each guard delegating. All the load-bearing rustdoc (the
S110 W1 keyed-read narratives, Decision 24, the platform TRANSITIONAL-MECHANICS
block) travels **with its arm** into the extracted method — do not summarize or
drop it; move it verbatim.

### 2.4 Byte-identity for R5-`compile_resolved_call`

Every extraction is lexical: the guard order is preserved, each arm's
`self.in_tail_position = saved_tail` assignment moves inside its extracted body
at the same relative position, the `apply_target_has_got_slot` predicate is pure.
`compile_moded_user_call` emits the identical instruction sequence for both the
TraitMethod and SigDispatch call sites (same three calls in the same order). No
`?`-propagation semantics change (all callees return `Result<Value,
CranelispError>`, propagated identically). Verify with the §0 protocol: the
corpus dump diff is empty.

---

## 3. R5 — split `compile_to_module_impl` (`lib.rs:633`, ~395 ln)

**4th audit; grew 373 → 395.** This is a **free function** generic over
`<M: Module + CodeFinalizer, C: CodeStore, L: LinkerStore>`, not a method — the
extracted phase helpers are free functions with the same generic bounds. The
body is already `Step 1 … Step 5`-commented; the split follows those seams. **Pure
phase extraction → byte-identical.** Land AFTER the R4 `module_aliases` drop
(§1.4) so the extracted signatures never carry the dead param.

### 3.1 The phase extraction

| New free fn | Source lines (Step) | Returns |
|---|---|---|
| `collect_compile_targets<C, L>(module_path, names, symbol_tables) -> Result<(Vec<Defn>, Vec<MonoExpr>, Vec<Option<ModeSummary>>), CranelispError>` | 650-781 (Step 1) | the three lockstep vectors; owns the symbol-table lookup loop + the hard `codegen_view`-None producer-gap error (§5 W0.b) |
| `declare_module_functions<M>(module, defns: &[Defn], func_ids: &mut HashMap<Symbol, FuncId>) -> Result<(), CranelispError>` | 796-821 (Step 2) | mutates `func_ids`; the `Linkage::Local` bare-name declaration loop |
| `compile_module_bodies<M, C, L>(module, module_path, defns, bodies, summaries, func_ids, func_arities, intrinsic_ids, capture_clif) -> Result<(String, usize), CranelispError>` | 834-908 (Step 3) | `(clif_ir_agg, code_size_agg)`; owns the per-body `CompileContext` build + `compile_defn_in_module` call + CLIF dump/aggregate |
| `emit_module_got_data<M, C, L>(module, module_path, symbol_tables, defns, func_ids) -> Result<(), CranelispError>` | 910-952 (Step 4a) | the `__cranelisp_got_{M}` data-symbol emission |
| `write_finalized_got_slots<M, C, L>(module, module_path, symbol_tables, defns, func_ids)` | 959-1020 (Step 5) | the per-symbol finalized-ptr → GOT-slot store + `GotEvent` emit |

`compile_to_module_impl` becomes the ~40-line orchestrator: `compile_start`
timer, `declare_intrinsics_generic`, `let (defns, bodies, summaries) =
collect_compile_targets(...)`, the `defns.is_empty()` guard (789-794),
`declare_module_functions`, the `func_arities` map (829-832, trivial — keep
inline), `let (clif_ir, code_size) = compile_module_bodies(...)`,
`emit_module_got_data`, `module.finalize_for_code_read()` (954-957, inline),
`write_finalized_got_slots`, and the `Ok(CompilationArtifacts { … })` return.

### 3.2 Extraction notes that preserve byte-identity

- **`func_arities`** (829-832) is derived once and read only inside Step 3;
  either pass it into `compile_module_bodies` or rebuild it there — it is a pure
  `defns.iter().map(...).collect()`, so either is byte-identical. Passing it in
  keeps the derivation at its current point.
- **The `clif_dump_filter`** env read (849) is once-per-invocation; it moves
  into `compile_module_bodies` (read once at the top of that fn). Byte-identical
  — the env value is process-stable.
- **The GOT-data read guard** (`symbol_tables.get(&module_path)` at 917, dropped
  at 948) is self-contained within Step 4a; it moves whole into
  `emit_module_got_data`. Same lock scope, same drop point.
- **`intrinsic_ids`** is consumed by both Step 2 (`by_name`) and Step 3
  (`alloc`/`dealloc`/… into each `CompileContext`). Pass the needed fields (or
  the whole `IntrinsicFuncIds`) into `compile_module_bodies`; Step 2 already
  seeds `func_ids` from `intrinsic_ids.by_name` before the split boundary.
- No reordering across phase boundaries: Step 1→2→3→4a→4→5 is a hard data
  dependency chain (declare before compile before finalize before slot-write),
  and the extraction keeps that exact order.

### 3.3 Interaction with R4 §1.4

R5-`compile_to_module_impl` and R4-`module_aliases`-drop both edit this function.
Land R4 §1.4 first (remove the param), then R5 (extract phases) — the extracted
helpers never see `module_aliases`. If landed as one change-set, the helper
signatures simply never include it. Either way the golden corpus is
byte-identical (unread field + pure extraction).

---

## 4. R6 — one drop-glue emission discipline (`/design` shape, then `/dev`)

Three builders re-implement one skeleton, and the identity half has produced two
historical defects (FIXME 0350 closure-glue collision; ledger item 25
curry-glue collision) — past the recurring-defect consolidation threshold since
S102. The three:

- `build_closure_drop_glue` (`lambda.rs:187`, 125 ln) — span+disc-keyed;
  **lacks the `get_name` idempotency skip** the other two have.
- `build_auto_curry_drop_glue` (`fn_as_value.rs:1011`) — span+disc-keyed via
  `curry_drop_glue_name`; has the `get_name` skip.
- `build_adt_drop_glue_fn` (`vec_codegen.rs:803`, 167 ln) — fqtn-keyed (no
  span/disc, so the span×mono collision class does not apply); has the `get_name`
  skip; body is a **multi-constructor tag-branch dispatch**, structurally richer
  than the flat capture-dec loop.

### 4.1 What is genuinely shared vs genuinely caller-specific

The skeleton has two layers. Only the **envelope** is common to all three; the
**body** differs (flat capture-dec loop for closure/curry vs multi-ctor
tag-branch for ADT). The consolidation extracts the envelope, not the body — per
the R6 done-bar "one glue-emission helper owns naming identity + idempotency; the
three builders supply only capture/layout specifics."

**The shared envelope** (`emit_drop_glue_fn`):

```
fn emit_drop_glue_fn<F>(&mut self, glue_name: &str, span: Span, build_body: F)
    -> Result<Option<cranelift_module::FuncId>, CranelispError>
where
    F: FnOnce(&mut FunctionBuilder, Value /* the (i64) glue param = the object ptr */)
        -> Result<(), CranelispError>,
```

Envelope responsibilities (owns identity + idempotency + FunctionBuilder
boilerplate, one home):

1. **Idempotency skip** — `if let Some(FuncOrDataId::Func(id)) =
   self.module.get_name(glue_name) { return Ok(Some(id)); }`. This is the
   single home for the declare-idempotent/define-once discipline. **Adding it to
   the closure mirror is deliberate hardening** (the closure builder lacks it
   today): the closure glue name folds `inner_fn_discriminator()` + span, unique
   per mono instance, so `get_name` never fires in practice → byte-identical;
   but the skip makes the closure path robust to a genuine re-entry the way the
   other two already are. This closes the last asymmetry in the family.
2. **Declare** `Linkage::Local`, one `i64` param (the object ptr), no return.
3. **FunctionBuilder boilerplate**: `make_context`, entry block,
   `append_block_params_for_function_params`, `switch_to_block`, `seal_block`,
   extract `ptr = builder.block_params(entry)[0]`.
4. **Invoke** `build_body(&mut builder, ptr)` — the caller emits its dec logic.
5. **Finish**: `builder.ins().return_(&[])`, `seal_all_blocks`, `finalize`,
   `define_function`, map declare/define errors to `CodegenError` with the
   caller's `span`.

**Naming is a function, never an inline `format!`** (the A.4 caveat — the
identity test must call the PRODUCTION naming function, not re-compose the
format). Three named functions, one per glue kind, co-located with
`got_data_symbol_name`/`inner_fn_discriminator_for` in `resolution.rs` (the
sanctioned name-composition home) or a `drop_glue` naming module:

- `closure_drop_glue_name(disc: &str, span: Span) -> String` — replaces the
  inline `format!("runtime/closure_drop_glue_{}{}_{}", disc, start, end)` at
  `lambda.rs:238`.
- `curry_drop_glue_name(disc: &str, span: Span) -> String` — **already exists**;
  keep it as the exemplar.
- `adt_drop_glue_name(fqtn: &FQTypeName) -> String` — replaces the inline
  `format!("runtime/drop_glue_{}", fqtn.name)` at `vec_codegen.rs:866`.

### 4.2 What each caller keeps (the layout/body specifics)

- **`build_closure_drop_glue`**: keeps the `spark_capture_borrow` early-return
  (the S99 borrow-join `None`, `lambda.rs:201-203`), the heap-capture collection
  (filter `variable_types` by `signature_heap_category` → AlwaysHeap|Mixed,
  early-`None` if empty), computes `closure_drop_glue_name(&disc, span)`, then
  calls `emit_drop_glue_fn(&name, span, |b, ptr| { for each capture: heap_load at
  HeapClosure::capture_offset(i) + emit_rc_dec / emit_rc_dec_guarded })`.
- **`build_auto_curry_drop_glue`**: keeps the `arg_categories` heap-index
  collection, computes `curry_drop_glue_name(&disc, span)`, same closure body
  shape.
- **`build_adt_drop_glue_fn`**: keeps ALL of its ctor-metadata reconstruction
  (`constructor_metas`, Var-id substitution, `has_heap_fields` gate), computes
  `adt_drop_glue_name(&fqtn)`, and supplies the multi-ctor body (single-ctor
  `emit_standalone_field_decs` vs tag-load-and-branch) as the `build_body`
  closure.

### 4.3 The borrow subtlety (the design's load-bearing constraint)

`emit_drop_glue_fn` holds `&mut self.module` while the `FunctionBuilder` borrows
`ctx.func`. The `build_body` closure must not re-borrow `&mut self` — but the
ADT body calls `emit_standalone_field_decs(&mut self, …)`. Two resolutions,
`/dev`'s choice:

- **(preferred)** `build_body: FnOnce(&mut FunctionBuilder, Value, &M, FuncId
  /*dealloc*/) -> Result<()>` — pass the module ref + `dealloc_id` the body
  needs; the closure/curry bodies call only free helpers (`heap::heap_load`,
  `heap::emit_rc_dec*` — all `&mut FunctionBuilder` + `&M`), and
  `emit_standalone_field_decs` is refactored to a free fn / associated fn taking
  the same pieces rather than `&mut self`. This is the clean end-state (the ADT
  body already clones `data_ctors` to dodge the self-borrow, `vec_codegen.rs:920`
  — the refactor removes that workaround).
- **(fallback)** the ADT caller keeps its own envelope (does not route through
  `emit_drop_glue_fn`) and only the closure+curry pair consolidate + all three
  share the naming functions. This still delivers the naming-identity home and
  the idempotency home for the two span-keyed mirrors (the ones with the defect
  history) and cuts the format-inline caveat everywhere, but leaves the ADT
  boilerplate un-deduped. Acceptable if the borrow refactor proves costly — the
  identity defects were on the span-keyed mirrors, not the ADT.

### 4.4 The identity test (the A.4 requirement)

One consolidated identity test, calling the **production naming functions**
(`closure_drop_glue_name` / `curry_drop_glue_name` / `adt_drop_glue_name`) — not
an inline `format!` re-composition (the current
`resolution/tests.rs:79`/`curry_glue_name_tests.rs:21` re-compose the format, so
a `format!` drift escapes them). The test pins: **distinct monos ⇒ distinct
glue** (different `inner_fn_discriminator` ⇒ different name), and **one
create-gate's two arms ⇒ one glue** (same disc+span ⇒ `get_name` idempotency skip
returns the same FuncId). This is the durable guard for the 0350 / ledger-25
defect class. `/dev` writes it; the three per-site restatements of the discipline
(`lambda.rs:228-237`, `fn_as_value.rs:1032-1058`, the vec_codegen idempotency
comment) collapse to pointers at the shared envelope.

### 4.5 Byte-identity for R6

R6 is a behaviour-preserving refactor but is **not** on the R4/R5 byte-identity
gate (it is a separate medium item). The guards are the consolidated identity
test (§4.4) + the existing golden corpus + the RC-leak e2e fences
(`tests/ownership_reuse.rs`, `tests/spec_12_runtime.rs`). The one intentional
behaviour delta — the closure mirror gaining the `get_name` skip — is
byte-identical in practice (unique names) and is the correct hardening; verify
the golden corpus is unchanged.

---

## 5. R7 — GOT slot exhaustion consumption (backend side)

`/arch` makes `cranelisp-types::SymbolTable::allocate_got_slot(&mut self)` →
`Result<usize, GotExhausted>` (fallible; the 1023→1024 boundary is the release-
mode UB today — `module.rs` unchecked monotone `+= 1`, `got.rs` `debug_assert!`
only). The **primary surfacing point is the typecheck allocation seam** (9
production sites per `/arch`'s impact table); the backend's side is deliberately
narrow.

### 5.1 The backend has NO production `allocate_got_slot` caller — corrected finding

**Verified (grep, S111 Phase 3):** every `allocate_got_slot` call in
`cranelisp-backend` is **test-only** — `compiler/apply/dispatch_tests.rs` (×3),
`compiler/extern_call.rs:151` (inside the `#[cfg(test)] mod tests`, the
`sconcat` fixture), `got.rs` tests, `module_assembly_tests.rs`,
`compiler/trace_codegen/tests.rs`, `test_support.rs:938`, `jit/tests.rs`. The
production backend **reads and writes** slots (`callable_got_slot()`,
`store_slot` at `lib.rs:994`, `load_slot` in `produce_disasm`/dispatch) but never
**allocates** one — allocation is entirely typecheck's job.

> **Coordination flag for `/arch` + `/sprint`** (surfaced in the Phase-3 report,
> not silently patched): the SPRINT.md §2 impact-table row lists "backend
> `extern_call.rs:151`" as a production caller that "maps exhaustion into
> `CodegenError`". That line is a **`#[cfg(test)]` fixture**, not a production
> caller — the backend has zero production `allocate_got_slot` sites. The
> impact table's caller enumeration should read "9 typecheck production sites +
> backend TEST fixtures (adapt to `Result`)", and the backend-side R7 done-bar
> is test-adaptation + (optionally) the `store_slot` backstop below, not a
> production `CodegenError` map at `extern_call.rs:151`.

### 5.2 The backend-side consumption contract

Two obligations, both small:

1. **Test-caller adaptation (mechanical).** Every backend test that calls
   `allocate_got_slot` handles the new `Result`: `.expect("fresh table cannot
   exhaust")` (the convention `/arch` uses for the bootstrap `builtins.rs:694`
   `unreachable!` site — a fresh table has 1024 free slots) or `?` where the test
   returns `Result`. This is the whole backend surface if `/arch` keeps the
   exhaustion diagnosis at the allocation seam only.

2. **The `store_slot` backstop (if `/arch` hard-checks the write).** The R7
   done-bar offers "fallible `allocate_got_slot` **or** hard-checked `store_slot`
   as the backstop." The backend's one production slot **write** is
   `lib.rs:994` (`table.got.store_slot(slot, ptr)` in `write_finalized_got_slots`
   after the R5 split, §3.1). If `/arch` makes `store_slot` return
   `Result<(), GotOutOfBounds>` (replacing the release-compiled-out
   `debug_assert!`), the backend maps it into `CodegenError` at that call site,
   naming module + symbol + slot:

   ```
   table.got.store_slot(slot, ptr).map_err(|_| CranelispError::CodegenError {
       message: format!("GOT slot {slot} out of bounds for symbol '{}' in module \
                         '{module_path}' — GOT exhausted (1024-slot slab); …"),
       location: ErrorLocation::from_span(defn.span),
   })?;
   ```

   This turns the release-mode OOB write into a diagnosed compile error at the
   backend seam that actually writes the slab. Whether this is needed depends on
   `/arch`'s chosen surfacing point — if the allocation seam already refuses to
   hand out slot ≥ 1024, `store_slot` can never receive an out-of-bounds slot on
   the production path and the backstop is defensive only. **Design
   recommendation**: take the allocation-seam surface as primary (the natural,
   earliest point — a session error at allocation, not deep in codegen), and add
   the `store_slot` hard-check as a cheap always-on backstop (converting the
   `debug_assert!` to a real check is the "wrong final state in Phase H"
   correction the audit names). The backend's `lib.rs:994` map is then the
   backstop's one production consumer.

### 5.3 The boundary test

The 1023→1024 boundary unit test is `/arch`'s (in
`cranelisp-types/src/module/tests.rs` per the impact table). The backend adds no
boundary test of its own — its exposure is the mechanical test-caller adaptation.
The `got.rs::slab_growth_tests` being rehomed in R4 §1.2 is the natural place for
any backend-side slab-bound assertion if one is wanted.

### 5.4 Doc consequence

The crate `CLAUDE.md` §"GOT slab" GOTCHA ("`allocate_got_slot` is UNCHECKED …
Slot exhaustion is an unresolved surfaced-error question") and the in-source
`got.rs:26-33` residual-risk note both update to point at the cure once R7 lands
(the `CLAUDE.md` edit is `/dev`-narrow; the `got.rs` comment travels with the
R4 shim deletion or the R7 change). This doc records the design; the `CLAUDE.md`
currency is `/dev`'s at landing.

---

## 6. Testability + observability notes (Principle 5, 23)

- **R4/R5 need no new behavioural test** — they are byte-identical; the golden
  corpus + the existing unit tier ARE the acceptance. The one new test surface
  is R4 §1.3's re-seamed probe tier (same assertions, production front door).
- **R6** needs the one consolidated identity test (§4.4) calling production
  naming functions — this is the durable guard the two historical defects
  lacked.
- **R2** (out of this doc, `/qa` + test tier) pins the three hard-miss
  `CodegenError` families — the negative side of the keyed-consumer invariant.
  It should land BEFORE R4/R5 (SPRINT.md §1 constraint 1) so the keyed-miss
  discipline is guarded while the funnels are restructured.
- **Observability**: `CRANELISP_CODEGEN_DUMP` (the byte-identity oracle) and the
  hard-miss `CodegenError` messages (each naming reference + missing carrier +
  design section) are the two debug surfaces these drains preserve — none of
  R4/R5/R6/R7 removes an observability seam; R7 *adds* one (the diagnosed
  exhaustion error).

## 7. Principle citations

- **Principle 6 (complexity has a budget)** — R5 funnel splits: the two funnels
  are the crate's two largest functions, re-accreting at the most-edited seam.
- **Principle 7 (single source of truth)** — R4 §1.1 (one `build_isa`), R5 §2.1
  (`apply_target_has_got_slot` dedup) + §2.2 (`compile_moded_user_call` dedup),
  R6 (one glue-naming/idempotency home).
- **Principle 8 (no interim implementations)** — R4 §1.2 (Wave-2b shims), §1.3
  (dead front door), §1.4 (`module_aliases` UNREAD field). The audit's headline
  finding: everything left as prose lapses; these are the lapsed stratum.
- **Principle 18 (enforce invariants structurally)** — R7 (exhaustion → diagnosed
  error, not release-mode UB) and the retained hard-miss error posture.
- **Principle 24 (resolve once)** — the keyed-consumer end-state R5 preserves;
  the splits must not reintroduce any scan/precedence walk (the grep gate holds).
