# Backend Module Decomposition — Sprint 87 (Wave 5 design)

> **What this is.** A `/design` decomposition plan for the two oversized
> `cranelisp-backend` codegen modules called out in `audits/s87-maintainability.md`
> Part 2 (§2.5 `control_flow.rs`, §2.7 `compiler/mod.rs`) and reinforced by
> `audits/cranelisp-backend-s87.md` (F5 extern-call ladder, F8/F11 resolution-seam
> twin walkers, F2-adjacent heap-class duplication). It is **design only** — `/dev`
> executes; this doc names the sub-module set, the dedups, the over-budget splits,
> and the migration order with the behaviour-preserving invariant.
>
> **Goal (user):** coherent and cohesive modules of manageable size. Tests were
> already extracted to siblings this sprint, so the figures below are pure
> production LOC. Suite is green (2846/0/0); the whole exercise MUST leave it so.
>
> **Authored by** `/design` (deployed narrow to `cranelisp-backend`), Sprint 87 Wave 5.
> Cites `design/arch/principles.md`: **P6** (complexity has a budget), **P7**
> (single source of truth), **P19** (no module privileged by name), **P1**
> (decoupling over convenience).

---

## 0. Invariants that bound this whole change-set

These hold for **both** decompositions and are the acceptance frame for `/review`:

1. **Behaviour-preserving.** No logic change. Every moved function keeps its body
   byte-for-byte except for `use`/path adjustments. The dedups (§1.2, §2.2) are the
   *only* places where bodies change, and each is a mechanical collapse of
   already-identical code — provably equivalent, not a re-derivation.
2. **Public surface unchanged.** `crates/cranelisp-backend/public-api.txt` is
   **byte-identical** after the change. This is structurally guaranteed: every item
   in `control_flow.rs` is `pub(crate)` or private, and the only `pub`-to-boundary
   items in `compiler/mod.rs` are `CompileContext` (struct + `lookup_type_def` +
   `Clone`) and the `pub mod cranelisp_backend::compiler` line itself (verified
   against `public-api.txt`). Those stay in their current home or are re-exported
   under the same path (§2.1). Everything else (`FnCompiler`, `MatchContext`, the
   `resolve_*` free fns, `signature_heap_category`, `got_data_symbol_name`) is
   `pub(crate)` and invisible to the boundary — it may move freely as long as
   `pub(crate) use` re-exports preserve the **in-crate** paths the sibling modules
   (`apply.rs`, `vec_codegen.rs`, `trace_codegen.rs`, `literals.rs`,
   `match_codegen.rs`, `lib.rs`, and the `*/tests.rs` siblings) already import.
3. **Suite green throughout.** Run after every migration step, not just at the end.
   The two crates already carry sibling unit tests
   (`compiler/tests.rs`, `compiler/control_flow/{sparkability_tests,par_codegen_tests}.rs`)
   — these are the per-step regression guard (P5 — testability is structural).
4. **`mod`/dir coexistence is already proven.** `control_flow.rs` already has a
   sibling `control_flow/` directory (holding the two test files), and
   `compiler/mod.rs` already has a `compiler/tests.rs` sibling. Rust resolves
   `mod foo;` inside `control_flow.rs` to `control_flow/foo.rs` when the dir exists
   — so **the decomposition adds sub-modules to the existing dirs**; it does not
   need a file rename or an `inline-mod → file-mod` conversion. This removes the
   single largest migration hazard.

### Why a re-export hub, not a flat split

`FnCompiler` is one struct with ~30 fields and its `impl` blocks are spread across
`mod.rs`, `control_flow.rs`, `apply.rs`, `vec_codegen.rs`, etc. Rust lets a single
`impl` type carry methods defined in **multiple files** — each file just writes
`impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L> where …`. So the decomposition is
**"move cohesive `impl` method clusters into sibling files on the same struct,"**
not a responsibility carve that would require splitting the struct. This is the
established pattern in the crate already (six `compiler/*.rs` files all `impl
FnCompiler`). The split is therefore mechanical, not a re-architecture — consistent
with P19 (no file is privileged; the methods live where their concern lives, the
struct stays one type).

---

## Part 5a — `compiler/control_flow.rs` (1463 prod LOC → `control_flow/` submodules)

### 5a.1 Current cohesive clusters (with line ranges, raw file lines)

Surveyed against the source (2129 raw lines incl. doc-comments; ~1463 tokei prod):

| Cluster | Functions | Lines | Concern |
|---|---|---|---|
| **Let / If** | `compile_let` (25), `compile_let_sequential` (63), `compile_let_lenient` (121), `compile_if` (634) | 25–206, 632–674 | Sequential + lenient-IVar binding; conditional branch merge |
| **IVar plumbing** | `emit_extern_call_1` (209), `emit_rc_dec_for_ivar` (242) | 208–285 | Lenient-eval IVar create/spark/force/dealloc support |
| **Par-bind** | `compile_par_bind` (306), `compile_par_bind_continuation` (401, **~230L over budget**) | 287–630 | IO Par/Bind node emission + continuation closure |
| **Lambda / closure** | `compile_lambda` (686, ~140L), `build_closure_drop_glue` (832, ~112L), `emit_capture_return_inc` (982), `compile_lambda_body` (1011, ~149L) | 676–1159 | Closure allocation, inner-fn body, capture-return inc, drop glue |
| **Fn-as-value** | `is_known_function` (1164), `compile_fn_as_value` (1180), `compile_trait_method_as_value` (1289, ~117L), `compile_fn_wrapper_body` (1410), `emit_wrapper_call` (1461), `emit_curry_target_call` (1514) | 1161–1574 | Named-fn / trait-method value-position wrappers + wrapper call emission |
| **Auto-curry** | `compile_auto_curry` (1585, ~199L), `compile_auto_curry_wrapper` (1692), `build_auto_curry_drop_glue` (1794) | 1576–1887 | Partial-application closure + wrapper + drop glue |
| **Free-fn analysis** | `find_free_vars` (1890), `collect_free_vars` (1899), `is_extern_primitive_in_wrapper` (1988), `emit_extern_call_in_wrapper` (2023), sparkability (`LENIENT_DISABLED`, `CHEAP_BUILTINS`, `find_sparkable_bindings` 2074, `is_worth_sparking` 2107) | 1889–2122 | Module-level (non-`impl`) free-var collection + sparkability + wrapper-context extern call |
| **Test siblings (exist)** | `mod sparkability_tests;`, `mod par_codegen_tests;` | 2124–2128 | already in `control_flow/` |

### 5a.2 Target sub-module set (`control_flow/` directory)

`control_flow.rs` becomes a **slim re-export + module-declaration hub** (keeps the
top-of-file `use` set and the two `#[cfg(test)] mod …_tests;` lines, plus the new
`mod` declarations). Each sub-module is an `impl FnCompiler` block plus its private
helpers.

| New file | Moves in (by cluster) | Cohesion rationale |
|---|---|---|
| `control_flow/let_if.rs` | `compile_let`, `compile_let_sequential`, `compile_let_lenient`, `compile_if`, `emit_rc_dec_for_ivar` | The binding-and-branch core. `let`/`if` are the two simplest control forms; the lenient path and its IVar-dec helper belong with `compile_let` (its only caller). **`emit_extern_call_1` does NOT live here** — it becomes the shared extern-call helper (§5a.3 dedup). |
| `control_flow/par_bind.rs` | `compile_par_bind`, `compile_par_bind_continuation` (after §5a.4 split) | IO scheduling node emission. One self-contained concern (`io-scheduling.md §4`); the continuation closure is only built here. |
| `control_flow/lambda.rs` | `compile_lambda`, `compile_lambda_body`, `build_closure_drop_glue`, `emit_capture_return_inc` | Closure compilation: site allocation, inner-fn body, drop glue, capture-return inc. The capture-return-inc rule (`ring2-rc.md`) is a lambda-body concern; `build_closure_drop_glue` is called only by `compile_lambda` and `compile_par_bind_continuation` — keep it here, `par_bind.rs` calls it cross-module via the shared `impl` (no visibility change: both are `impl FnCompiler` methods, already `self.`-reachable). |
| `control_flow/fn_as_value.rs` | `is_known_function`, `compile_fn_as_value`, `compile_trait_method_as_value`, `compile_fn_wrapper_body`, `emit_wrapper_call`, `emit_curry_target_call`, **+ auto-curry** (`compile_auto_curry`, `compile_auto_curry_wrapper`, `build_auto_curry_drop_glue`) | First-class-function lowering: every path that turns a *name* or *partial application* into a heap closure with a generated wrapper. Auto-curry is the "some-args-applied" sibling of fn-as-value's "zero-args-applied" case (the rustdoc on `compile_trait_method_as_value` already states this), and both route through `emit_curry_target_call` → `emit_wrapper_call`. Keeping them together keeps the wrapper-call helpers private to their only callers. |
| `control_flow/free_vars.rs` | `find_free_vars`, `collect_free_vars` (module-level free fns) | Pure AST traversal — no `FnCompiler`, no codegen. Consumed by `lambda.rs`, `par_bind.rs`, and `find_sparkable_bindings`. A leaf utility; isolating it makes the three consumers' dependency explicit (P1). `pub(crate)` so `lambda.rs`/`par_bind.rs` reach it. |
| `control_flow/sparkability.rs` | `LENIENT_DISABLED`, `CHEAP_BUILTINS`, `find_sparkable_bindings` (already `pub(crate)`), `is_worth_sparking` | The lenient-eval *decision* pass (`lenient-eval.md §2`), distinct from the lenient *emission* in `let_if.rs`. `find_sparkable_bindings` is the only `pub(crate)` free fn here and its existing test sibling (`sparkability_tests.rs`) imports it via `super::find_sparkable_bindings` — **the test sibling must move to `control_flow/sparkability/tests.rs` OR its `use super::` must be retargeted**; see migration note 5a.5(e). |

**Disposition of the wrapper-context extern helpers** (`is_extern_primitive_in_wrapper`,
`emit_extern_call_in_wrapper`): these are free fns (not `impl FnCompiler`) used only by
`emit_curry_target_call`. Move them into `fn_as_value.rs` alongside their sole caller
(keep them `fn`-private to that module). They are **distinct** from the F5 extern-call
ladder dedup (§5a.3) — `emit_extern_call_in_wrapper` already takes `&[Value]` (slice-based,
arity-generic) and operates on a *borrowed* `builder`/`module` inside a wrapper context,
whereas `emit_extern_call_1` is an `&mut self` method. They do not merge with each other;
the F5 dedup is about the arity ladder, not the wrapper variant. (Audit F5 lists
`emit_extern_call_in_wrapper` as a *separate* helper, not a ladder rung.)

Resulting `control_flow.rs` hub (≈40 lines): the file header comment, the shared
`use` block, the six `mod` declarations + two `#[cfg(test)] mod` lines, and any
`pub(crate) use` needed so existing importers (`apply.rs` etc.) keep their paths
(see 5a.5(d)).

### 5a.3 Dedup — the 4-site capture-RC-inc → one `emit_capture_inc` (audit Part 2 §2.5; backlog item 8)

**The duplicated logic** is the heap-category match that, given a `HeapCategory`
and a `Value`, emits `emit_rc_inc` / `emit_rc_inc_guarded` / nothing. It appears as
an inline 3-arm `match` at these sites (file:line, current `control_flow.rs`):

| # | Site | Lines | Shape |
|---|---|---|---|
| 1 | `compile_par_bind_continuation` (capture store loop) | 615–625 | `signature_heap_category(ty,…)` → match → `emit_rc_inc[_guarded](self.builder, cap_val)` |
| 2 | `compile_lambda` (capture store loop) | 810–820 | identical to #1 (`cap_val`) |
| 3 | `emit_capture_return_inc` | 996–1004 | match → `emit_rc_inc[_guarded](self.builder, body_val)` (single value, category already computed) |
| 4 | `compile_auto_curry` (capture store loop) | 1674–1682 | match on **precomputed** `arg_categories[i]` → `emit_rc_inc[_guarded](self.builder, val)` |
| 4b | `compile_auto_curry_wrapper` (capture load loop) | 1751–1759 | match on `arg_categories[i]` → `emit_rc_inc[_guarded](&mut builder, cap_val)` — note: **borrowed `builder`**, not `self.builder` |

**Proposed single helper.** Two forms are needed because the value-emission target
differs (`self.builder` for the `&mut self` sites vs a borrowed `&mut FunctionBuilder`
in the wrapper at 4b). Keep it minimal — one method on `FnCompiler`, plus one free
fn for the borrowed-builder wrapper case:

```rust
// home: control_flow/capture_rc.rs  (new), declared `mod capture_rc;` in the hub.
impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where C: CodeStore, L: LinkerStore {
    /// Emit the capture-inc for a heap category onto `self.builder`.
    /// Single source for the "closure env gains its own reference" rule
    /// (sketch/audits/codegen.md heap-classification HIGH pattern; P7).
    pub(crate) fn emit_capture_inc(&mut self, category: HeapCategory, val: Value) {
        match category {
            HeapCategory::AlwaysHeap => heap::emit_rc_inc(&mut self.builder, val),
            HeapCategory::Mixed      => heap::emit_rc_inc_guarded(&mut self.builder, val),
            HeapCategory::NeverHeap  => {}
        }
    }
}

/// Borrowed-builder form for wrapper-context emission (auto-curry wrapper body,
/// which builds in a separate Cranelift context, not `self.builder`).
pub(crate) fn emit_capture_inc_into(
    builder: &mut FunctionBuilder, category: HeapCategory, val: Value,
) {
    match category {
        HeapCategory::AlwaysHeap => heap::emit_rc_inc(builder, val),
        HeapCategory::Mixed      => heap::emit_rc_inc_guarded(builder, val),
        HeapCategory::NeverHeap  => {}
    }
}
```

**Call-site collapse:**
- Sites #1, #2 (par_bind continuation, lambda): the surrounding loop computes
  `category = signature_heap_category(ty, …)` then matches — replace the match with
  `self.emit_capture_inc(category, cap_val);`. The `signature_heap_category` call
  stays at the call site (it reads `self.ctx.symbol_tables`).
- Site #3 (`emit_capture_return_inc`): replace the match with
  `self.emit_capture_inc(category, body_val);`.
- Site #4 (auto-curry store loop): `self.emit_capture_inc(arg_categories[i], val);`.
- Site #4b (auto-curry wrapper, borrowed builder): `emit_capture_inc_into(&mut builder, *category, cap_val);`.

Net: ~40 LOC removed; the heap-class→inc decision lives in **one** place. This is the
exact "duplicate heap classification" HIGH pattern the sketch audits warn about, now
single-sourced (P7). `capture_rc.rs` is the natural home (it is *about* the capture-inc
rule); `lambda.rs`/`par_bind.rs`/`fn_as_value.rs` call it cross-module via the shared
`impl` with no visibility change.

> **Scope note.** This dedup unifies the **inc** decision. The **dec** counterparts
> (`build_closure_drop_glue` 907–928, `build_auto_curry_drop_glue` 1850–1871) have the
> symmetric `AlwaysHeap → emit_rc_dec / Mixed → emit_rc_dec_guarded / NeverHeap → {}`
> shape and could grow a sibling `emit_capture_dec_into(builder, category, val, dealloc)`
> helper. That is a **stretch goal, not required** for 5a — it touches the drop-glue
> bodies (more state: `dealloc_id`, the `true` guard flag) and the audit only charters
> the 4-site *inc*. If `/dev` finds the dec collapse trivially clean while in the file,
> take it; otherwise leave a one-line note and defer. Do not let it expand the blast radius.

### 5a.4 Over-budget split — `compile_par_bind_continuation` (~230L, audit F4 / backlog)

Current shape (401–630): one method that (a) computes captures, (b) declares the
continuation fn signature, (c) compiles the continuation **body** in a separate
Cranelift context (the big inner block, 447–561 — captures load, results-buffer
load + bind, body compile, results-buffer dec, return), then (d) allocates the
continuation **closure** at the call site (563–629 — code_ptr store, drop-glue store,
capture store+inc loop).

**Proposed extraction** (all land in `par_bind.rs`, all `impl FnCompiler` methods):

1. `compile_par_bind_continuation` (the spine, ≤~60L) — computes captures, declares
   the fn, calls (2), then calls (3). Returns the closure ptr.
2. `define_par_cont_body(&mut self, cont_func_id, &captures, bindings, body, sig, span)`
   (~110L) — the inner-context block (447–561): the actual continuation function
   definition. This is the cohesive "compile the continuation's body" unit.
3. `alloc_par_cont_closure(&mut self, cont_func_id, &captures, span) -> Result<Value>`
   (~65L) — the call-site closure allocation + capture store/inc loop (563–629). The
   capture-inc loop here uses the §5a.3 `emit_capture_inc` helper.

This mirrors `compile_lambda`'s existing shape (site alloc in `compile_lambda`, body
in `compile_lambda_body`, drop glue in `build_closure_drop_glue`) — so the split makes
par-bind **structurally parallel** to lambda, which is the right cohesion signal:
they are the same closure-emission protocol with different bodies. Each resulting
function is under the ~100-line `src/CLAUDE.md` ceiling (P6).

> `compile_auto_curry` (~199L) and `compile_lambda_body` (~149L) are also over budget
> (audit F4). They are **out of charter for 5a's required scope** (the brief names only
> `compile_par_bind_continuation`), but the §5a.2 cut already moves them into
> `fn_as_value.rs` / `lambda.rs` respectively. `compile_auto_curry` already delegates
> to `compile_auto_curry_wrapper` + `build_auto_curry_drop_glue`; its ~199L is mostly
> the store loop + the two delegations, so it is *legible* despite the count. Leave both
> as-is this wave unless trivially splittable; record as a follow-on if not taken.

### 5a.5 Migration order + risk notes (5a)

Do these **in order**, running the suite after each numbered step:

(a) **Create `control_flow/free_vars.rs` first** (leaf, zero `FnCompiler` coupling).
   Move `find_free_vars` + `collect_free_vars`, mark `pub(crate)`. Add `mod free_vars;
   pub(crate) use free_vars::find_free_vars;` to the hub (or just `mod free_vars;` and
   have callers use `super::free_vars::find_free_vars` — pick the form that minimises
   churn; `find_free_vars` has 3 callers: `compile_par_bind_continuation`,
   `compile_lambda`, `find_sparkable_bindings`). **Hazard:** none — pure fns.

(b) **Create `control_flow/capture_rc.rs`** with `emit_capture_inc` +
   `emit_capture_inc_into` (§5a.3). Collapse the 5 call sites. Run suite — this is the
   one *behavioural-equivalence* step; if it's green, the collapse is correct.
   Do this **before** moving the cluster files so the collapse diff is reviewed against
   the original line numbers (smaller, legible diff).

(c) **Split `compile_par_bind_continuation`** (§5a.4) while it is still in
   `control_flow.rs` — extract (2) and (3) as new `impl` methods. Run suite. Doing the
   split *before* the file move keeps the extraction diff separate from the move diff.

(d) **Move clusters into sibling files**, one file per step, in dependency order:
   `sparkability.rs` → `let_if.rs` → `par_bind.rs` → `lambda.rs` → `fn_as_value.rs`.
   Each move: cut the `impl FnCompiler { … }` block (or free fns) into the new file,
   add the file's own `use` header (copy the needed imports from the hub; Rust will
   error on unused/missing — let the compiler drive the `use` list), add `mod <name>;`
   to the hub. **Hazard — visibility:** all the methods are `pub(crate)` or private
   *methods on `FnCompiler`*; method privacy is per-`impl`-item and is unaffected by
   which file the `impl` block lives in (a `pub(crate) fn` method is reachable
   crate-wide regardless of file). The only items needing attention are the **free
   fns** and **the module-level statics** (`LENIENT_DISABLED`, `CHEAP_BUILTINS`):
   these are file-scoped, so anything referencing them must be in the same file or
   reach them via `super::`/`pub(crate) use`. `find_sparkable_bindings` is `pub(crate)`
   and referenced by `compile_let` (in `let_if.rs`, via `super::sparkability::find_sparkable_bindings`)
   and by `sparkability_tests.rs`.

(e) **Retarget the test siblings.** Two existing test files sit in `control_flow/`:
   - `sparkability_tests.rs` does `use super::find_sparkable_bindings;`. After the move,
     `find_sparkable_bindings` lives in `control_flow/sparkability.rs`, so `super::` (=
     `control_flow`, the hub) still reaches it **iff** the hub re-exports it
     (`pub(crate) use sparkability::find_sparkable_bindings;`). **Add that re-export** —
     it is the lowest-churn fix and keeps the test file's `use super::` valid. Declare
     the test as `#[cfg(test)] mod sparkability_tests;` in the hub (unchanged).
   - `par_codegen_tests.rs` does `use crate::jit::Jit;` (absolute path) — **unaffected**
     by the move; leave it. Keep `#[cfg(test)] mod par_codegen_tests;` in the hub.

(f) **Final hub check.** `control_flow.rs` now contains only: header comment, shared
   `use`, the `mod` declarations, the `pub(crate) use` re-exports (e.g.
   `find_sparkable_bindings`, `find_free_vars` if callers use the hub path), and the two
   `#[cfg(test)] mod …_tests;` lines. Confirm `cargo check -p cranelisp-backend` is
   warning-clean (no unused `use` left in the hub). Confirm `public-api.txt` unchanged.

**Things that MUST stay together (do not split across files):**
- `compile_let` + `compile_let_sequential` + `compile_let_lenient` (the lenient
  dispatch reads `find_sparkable_bindings`; all three are one binding protocol).
- The par-bind continuation body + closure alloc (they were one fn; even after the
  §5a.4 split they are one protocol — keep all three par-bind methods in `par_bind.rs`).
- `emit_curry_target_call` + `emit_wrapper_call` + the wrapper-context extern helpers
  — the call-emission tail shared by fn-as-value and auto-curry; one file.

---

## Part 5b — `compiler/mod.rs` (1279 prod LOC → slim hub + submodules)

### 5b.1 Current cohesive clusters (with line ranges, raw file lines)

`compiler/mod.rs` (2050 raw lines) is the module root: it declares the six codegen
sub-modules, defines the shared types, the resolver free fns, and the `FnCompiler`
core impl. Clusters:

| Cluster | Items | Lines | Concern |
|---|---|---|---|
| **Module decls + naming** | `mod apply/control_flow/literals/match_codegen/trace_codegen/vec_codegen;`, `got_data_symbol_name` (100), `inner_fn_discriminator_for` (116) | 22–128 | Sub-module wiring + GOT/inner-fn symbol naming (pure) |
| **Resolvers** | `resolve_got_target` (146, ~107L), `resolve_platform_effect_target` (268, ~89L), `resolve_extern_target` (373, ~88L), `resolve_func_arity` (469, ~87L) | 130–555 | Symbol-table import-chain walkers, 4 near-identical (the F11 twin-walker seam) |
| **DTOs** | `CtorField` (56), `CtorMeta` (69), `TracedFnInfo` (565), `MatchContext` (823) | 47–73, 557–585, 818–834 | Backend-internal metadata structs |
| **CompileContext** | struct (607) + manual `Clone` (649) + `impl` (`lookup_constructor` 687, `extract_constructor` 752, `constructor_metas` 782, `lookup_type_def` 805) | 587–816 | Shared immutable ctx + constructor/type-def lookups |
| **FnCompiler core** | struct (849, ~88L) + `inner` (949) + `inner_fn_discriminator` (996) + `compile_body` (1005, ~116L) + `compile_expr` dispatch (1132) + `fresh_variable` + scope mgmt (`push_scope`, `pop_scope`, `pop_scope_with_cleanup` 1249) | 836–1328 | The per-fn emitter struct, construction, dispatch, scope lifecycle |
| **RC / drop-glue emission** | `emit_inline_drop_glue` (1339), `emit_mixed_adt_heap_guard` (1409), `emit_drop_glue_field_decs` (1436), `emit_field_decs` (1498), `return_var_in_scope` (1578), `protect_return_value` (1596), `is_heap_type` (1641), `derive_param_type_from_body` (1654), `is_last_use` (1659), `emit_closure_dec_inline` (1694), `emit_rc_dec_with_inline_drop_glue` (1789) | 1330–1890 | The RC/drop-glue emission helpers on `FnCompiler` |
| **Free type helpers** | `build_adt_type_substitution` (1897), `collect_var_ids_from_type` (1922), `substitute_type_inline` (1944), `find_var_type_in_expr` (1970), `signature_heap_category` (2032) | 1892–2046 | Pure type-substitution + heap classification helpers |
| **Test sibling (exists)** | `#[cfg(test)] mod tests;` | 2048–2049 | already `compiler/tests.rs` |

### 5b.2 Target sub-module set

`compiler/mod.rs` stays the module root (it MUST — it owns the `pub mod
cranelisp_backend::compiler` boundary and the six existing `pub(crate) mod`
declarations). It becomes a **slim hub**: module decls, the shared `use`, the DTOs
that are too small to relocate, and `pub(crate) use` re-exports so the in-crate paths
(`crate::compiler::resolve_got_target`, `crate::compiler::signature_heap_category`,
`crate::compiler::got_data_symbol_name`, `super::FnCompiler`, `super::signature_heap_category`,
`super::CompileContext`, etc., as used by `control_flow.rs`, `apply.rs`, `vec_codegen.rs`,
`literals.rs`, `match_codegen.rs`, `trace_codegen.rs`, `lib.rs`) keep resolving.

| New file | Moves in | Cohesion rationale |
|---|---|---|
| `compiler/resolution.rs` | `resolve_got_target`, `resolve_platform_effect_target`, `resolve_extern_target`, `resolve_func_arity`, `got_data_symbol_name`, `inner_fn_discriminator_for`, **+ one new `resolve_chain` walker** (§5b.2 dedup) | The symbol-table resolution seam (F11). All four resolvers walk the same import chain; co-locating them with the shared `resolve_chain` makes the dedup local and the seam one file. Naming helpers (`got_data_symbol_name`, `inner_fn_discriminator_for`) are the resolution-adjacent symbol-naming primitives — they belong with GOT-target resolution. |
| `compiler/context.rs` | `CompileContext` struct + manual `Clone` impl + the `impl` (`lookup_constructor`, `extract_constructor`, `constructor_metas`, `lookup_type_def`) + `CtorField`, `CtorMeta` (the ctor DTOs `CompileContext` produces) | The shared immutable compilation context and the constructor/type-def lookups that read from it. `CtorField`/`CtorMeta` are the *output* of `lookup_constructor`/`extract_constructor`, so they belong with their producer. **`CompileContext` + `lookup_type_def` stay `pub` (boundary items) — they re-export at the same path via the hub.** |
| `compiler/fn_compiler.rs` | `FnCompiler` struct def + `inner` + `inner_fn_discriminator` + `compile_body` (after §5b.3 split) + `compile_expr` dispatch + `fresh_variable` + `push_scope`/`pop_scope`/`pop_scope_with_cleanup` + `return_var_in_scope` + `is_heap_type` + `derive_param_type_from_body` + `is_last_use` + `MatchContext` | The per-fn emitter: the struct, its construction, the dispatch entry, scope lifecycle, and the small per-fn predicates. `MatchContext` is per-arm `FnCompiler` state — keep it adjacent to the struct it threads through. |
| `compiler/rc_emission.rs` | `emit_inline_drop_glue`, `emit_mixed_adt_heap_guard`, `emit_drop_glue_field_decs`, `emit_field_decs`, `protect_return_value`, `emit_closure_dec_inline`, `emit_rc_dec_with_inline_drop_glue`, **`signature_heap_category`** (the single heap-class entry), + the pure type helpers `build_adt_type_substitution`, `collect_var_ids_from_type`, `substitute_type_inline`, `find_var_type_in_expr` | All RC/drop-glue emission + the heap classification it keys on. Putting `signature_heap_category` here makes `rc_emission.rs` the **single home for the heap-class match** (audit Part 2 §2.7 "single home for heap-class match"), which the drop-glue field-dec sites and `pop_scope_with_cleanup`'s guard read. The type-substitution helpers are used only by the drop-glue field-dec path (`build_adt_type_substitution` + `substitute_type_inline` feed `emit_field_decs`), so they belong here too. |

> **Note on `pop_scope_with_cleanup`.** It lives in `fn_compiler.rs` (scope lifecycle)
> but *calls* `signature_heap_category` (1282) and `emit_rc_dec_with_inline_drop_glue` /
> `emit_vec_aware_rc_dec` / `emit_closure_dec_inline` (in `rc_emission.rs` / `vec_codegen.rs`).
> All are `pub(crate)` methods on the same `FnCompiler` — cross-file calls need **no**
> visibility change. The only cross-file *free-fn* reach is `signature_heap_category`,
> which `fn_compiler.rs` reaches via `super::signature_heap_category` (re-exported by the
> hub) or `super::rc_emission::signature_heap_category`. Pick one and use it consistently.

Resulting `compiler/mod.rs` hub (≈90 lines): the doc-comment header, the six
`pub(crate) mod` codegen decls + the four new `mod resolution/context/fn_compiler/rc_emission;`,
the shared `use`, the `TracedFnInfo` DTO (small, trace-specific — could move to
`trace_codegen.rs` as a stretch, but leave in the hub to keep blast radius small),
the `pub(crate) use` re-exports, and `#[cfg(test)] mod tests;`.

### 5b.2-dedup — 4-site import-chain walk → one `resolve_chain` (audit Part 2 §2.7 / F11; backlog item 6)

**The duplicated logic.** Each of the four resolvers contains a nested fn that walks
the import chain identically (`resolve_in_module`, `resolve_in_module`, `probe`,
`arity_in_module`), differing **only** in what it reads from the terminal
`ModuleEntry` and the qualified-name/alias/global-fallback driver that wraps it. The
chain-walk skeleton (file:line in current `mod.rs`):

| Resolver | Nested walker | Lines | Terminal read |
|---|---|---|---|
| `resolve_got_target` | `resolve_in_module` | 158–198 | `entry.callable_got_slot()` → `(module, slot)` |
| `resolve_platform_effect_target` | `resolve_in_module` | 280–314 | `DefKind::PlatformEffect { got_slot }` → `(module, slot, bare)` |
| `resolve_extern_target` | `probe` | 385–415 | `DefKind::PrimitiveExtern` → `bare.to_string()` |
| `resolve_func_arity` | `arity_in_module` | 481–506 | `param_names.len()` → `usize` |

Each walker body is: `depth > MAX → None; st = tables.get(module)?; entry = st.get(bare)?;
{terminal read}; ModuleEntry::Import { source } => recurse(source.module, source.symbol, depth+1)`.
**And** the surrounding driver (current-module → qualified `module/name` with alias
substitution → child-of-current → absolute → global fallback) is copy-pasted across all
four (e.g. 200–251, 316–355, 417–459, 508–554) — that's the larger duplication.

**Proposed single helper** (home: `compiler/resolution.rs`):

```rust
const MAX_IMPORT_DEPTH: usize = 10;

/// Walk the import chain from `module`/`bare`, applying `read` to the terminal
/// non-Import entry. `read` returns `Some(T)` to stop with a result, `None` to
/// either keep following an `Import` edge (handled here) or give up. Single
/// source for the four resolver walkers (P7; audit F11).
fn resolve_chain<C, L, T>(
    tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module: &ModuleFullPath,
    bare: &str,
    depth: usize,
    read: &impl Fn(&ModuleFullPath, &ModuleEntry<C>) -> Option<T>,
) -> Option<T>
where C: CodeStore, L: LinkerStore {
    if depth > MAX_IMPORT_DEPTH { return None; }
    let st = tables.get(module)?;
    let entry = st.get(bare)?;
    if let Some(found) = read(module, entry) { return Some(found); }
    if let ModuleEntry::Import { source, .. } = entry {
        let (m, s) = (source.module.clone(), source.symbol.clone());
        drop(st);
        return resolve_chain(tables, &m, s.as_ref(), depth + 1, read);
    }
    None
}

/// The shared current → qualified(alias/child/absolute) → global driver.
/// Each resolver supplies only its terminal `read` closure.
fn resolve_driven<C, L, T>(
    tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_aliases: &ModuleAliases,
    current_module: &ModuleFullPath,
    name: &Symbol,
    read: impl Fn(&ModuleFullPath, &ModuleEntry<C>) -> Option<T>,
) -> Option<T>
where C: CodeStore, L: LinkerStore { /* the 3-step driver, once */ }
```

Then each public resolver shrinks to a thin call supplying its `read` closure, e.g.:

```rust
pub(crate) fn resolve_func_arity<C, L>(…) -> Option<usize> {
    resolve_driven(symbol_tables, module_aliases, current_module, name,
        |_m, entry| match entry {
            ModuleEntry::Def { param_names, .. } => Some(param_names.len()),
            _ => None,
        })
}
```

**Call-site collapse:** all four `resolve_*` public fns lose their nested walker AND
their copy-pasted driver; each becomes ~8–15 lines (signature + one `resolve_driven`
call with a `read` closure). `resolve_got_target` and `resolve_platform_effect_target`
need the `module` in their result tuple — `read` already receives `module: &ModuleFullPath`
so the closure can build `(module.clone(), slot[, bare])`. Net: ~120 LOC removed
(F11/backlog item 6 estimate), the resolution seam single-sourced (P7).

> **Risk — this is the one genuine untangle in 5b.** The four drivers are *near*-identical
> but **not byte-identical**: `resolve_got_target` and `resolve_func_arity` have the alias
> branch (2a); `resolve_platform_effect_target` and `resolve_extern_target` also have it;
> confirm all four drivers are truly equivalent before collapsing (read each `// 2a/2b/3`
> block side by side). The terminal reads differ in arity of the return tuple — the generic
> `T` covers that. **`/dev` must diff the four drivers in-place first** and only then
> introduce `resolve_driven`. Land the dedup as its own step with the suite green before
> moving files. This is effort **M** (the audit rates the whole 5b at M; this helper is its
> hardest piece) — do not rush it.

### 5b.2-note — the `emit_extern_call_*` ladder (audit F5) is **NOT** a `mod.rs` item

The brief asks to locate the 3-site `emit_extern_call_*` ladder. **Located:** the rungs
are in **`vec_codegen.rs`** (`emit_extern_call_2` :1211, `_3` :1238, `_4` :1267), plus
`emit_extern_call_1` in **`control_flow.rs`** (:209) and the separate
`emit_extern_call_in_wrapper` free fn in `control_flow.rs` (:2023). **None are in
`mod.rs`.** Therefore the F5 dedup is **out of scope for the 5b `mod.rs` decomposition**
as briefed — but the audit (F5) and backlog (item 7) charter a single slice-based
`emit_extern_call(name, &[Value], span)` helper to replace the ladder. Its natural home,
per audit F5, is `compiler/mod.rs` (or a small `compiler/extern_call.rs`) **so all
modules share it** — i.e. it would become a new hub-level (or new-file) `impl FnCompiler`
method, and `_1`/`_2`/`_3`/`_4` collapse to call it.

**Recommendation for /sprint:** treat F5 as a **separate `/dev` dedup task** (backlog
item 7, effort S), landed either before or after the 5a/5b decompositions, NOT folded
into them — it spans `control_flow.rs` + `vec_codegen.rs` and would entangle two
file-move diffs. If `/dev` does it in the same wave, do it as its own commit: introduce
`compiler/extern_call.rs` with `emit_extern_call(&mut self, name, &[Value], span)`,
collapse `_1`/`_2`/`_3`/`_4` (5 sites: control_flow IVar create/spark/force/dealloc all
use `_1`; vec_codegen uses `_2`/`_3`/`_4`), and leave `emit_extern_call_in_wrapper` alone
(borrowed-builder wrapper variant, already slice-based — §5a.2). This doc records the
location and the design; the change itself is a sibling task, not part of the two
decompositions.

### 5b.3 Over-budget split — `compile_body` (~116L)

`compile_body` (1005–1120) is the worst named offender in `mod.rs` (audit F4 lists it
at ~116L). It: creates entry + loop-header blocks (TCO), constructs the `FnCompiler`,
looks up authoritative param types from the symbol table, binds params into scope, then
compiles + finalizes. **Proposed extraction** (both land in `fn_compiler.rs`):

1. `compile_body` (the spine, ≤~55L) — block setup, `FnCompiler` construction, call
   (2), compile body, protect/cleanup, return + seal.
2. `bind_defn_params(&mut self, defn, body, loop_header)` (~50L) — the param-type
   lookup (1067–1076) + the param-bind loop (1081–1101). This is the cohesive "seed
   the function's parameters into scope + variable_types" unit, and it mirrors the
   identical param-bind loop in `compile_lambda_body` (control_flow) — extracting it
   names the shared shape (a future dedup candidate across the two, but **not** this
   wave: they thread different sources — `defn` scheme vs `lambda_type` — so leave them
   as parallel-but-separate).

`resolve_got_target` (~107L) drops below budget automatically once §5b.2-dedup removes
its nested walker + driver, so no separate split is needed for it.

### 5b.4 Migration order + risk notes (5b)

Order (suite green after each):

(a) **`resolve_chain`/`resolve_driven` dedup first**, in place in `mod.rs` (§5b.2-dedup).
   Diff the four drivers, confirm equivalence, introduce the two helpers, collapse the
   four resolvers. This is the highest-risk step — do it while everything is still in one
   file so the diff is reviewable against original line numbers. Run suite.

(b) **Split `compile_body`** (§5b.3) in place. Run suite.

(c) **Move clusters into sibling files**, in dependency order:
   `resolution.rs` → `context.rs` → `rc_emission.rs` → `fn_compiler.rs`. Reason for
   order: `resolution.rs` and `context.rs` are leaf-ward (resolvers + ctx are read by
   the emitter); `rc_emission.rs` carries `signature_heap_category` which `fn_compiler.rs`
   (and many sibling modules) read, so it moves before `fn_compiler.rs`. Each move adds
   `mod <name>;` to the hub and lets the compiler drive the per-file `use` list.

(d) **Add the `pub(crate) use` re-exports to the hub** so existing in-crate import paths
   survive. Inventory of paths to preserve (grep-verified consumers):
   - `crate::compiler::resolve_got_target` — used by `control_flow.rs` (`is_known_function`),
     `apply.rs`. Re-export: `pub(crate) use resolution::resolve_got_target;`.
   - `crate::compiler::resolve_func_arity` — `control_flow.rs` (`compile_fn_as_value`).
   - `crate::compiler::resolve_platform_effect_target`, `resolve_extern_target` — `apply.rs`.
   - `crate::compiler::got_data_symbol_name` — `control_flow.rs` (`emit_wrapper_call`),
     `cache::object` (re-exports it `pub(crate)`), `trace_codegen.rs`.
   - `super::signature_heap_category` — `control_flow.rs` (top `use`), `vec_codegen.rs`,
     others. Re-export from `rc_emission`.
   - `super::FnCompiler`, `super::CompileContext`, `super::CtorMeta`, `super::CtorField`,
     `super::MatchContext`, `super::TracedFnInfo`, `super::{build_adt_type_substitution,
     collect_var_ids_from_type, substitute_type_inline}` — all referenced by sibling
     codegen modules via `super::`/`use super::*`. **The hub must `pub(crate) use` each
     relocated item** so `super::Name` (where `super` = `compiler`) keeps resolving. The
     simplest safe form: in the hub, after each `mod`, write
     `pub(crate) use fn_compiler::{FnCompiler, MatchContext}; pub(crate) use context::{CompileContext, CtorField, CtorMeta}; pub(crate) use resolution::{…}; pub(crate) use rc_emission::{signature_heap_category, build_adt_type_substitution, collect_var_ids_from_type, substitute_type_inline};`.

(e) **Boundary check.** `CompileContext` (and its fields, `Clone`, `lookup_type_def`) is
   `pub` and **in `public-api.txt`** at path `cranelisp_backend::compiler::CompileContext`.
   After moving the struct to `context.rs`, the hub's `pub(crate) use context::CompileContext;`
   would make it `pub(crate)`, **narrowing it** — WRONG. The re-export for `CompileContext`
   must be **`pub use context::CompileContext;`** (not `pub(crate)`) so it re-exports at
   the original `pub` path. Same for any other boundary item that moves. **This is the
   single public-api hazard in 5b** — verify `public-api.txt` is byte-identical (the
   project's API-diff check) after the move. (All `resolve_*`, `signature_heap_category`,
   `FnCompiler`, etc. are `pub(crate)` and absent from `public-api.txt`, so they re-export
   `pub(crate)`.)

(f) **`tests.rs` sibling.** `compiler/tests.rs` does `use super::*;` / `use crate::…`.
   `use super::*;` (super = the hub) picks up everything the hub re-exports, so the
   `pub(crate) use` re-exports in (d) keep the test file compiling unchanged. Verify; if
   the test reaches a now-relocated **private** (`fn`, not `pub(crate)`) item, either
   widen that item to `pub(crate)` (note it) or add a targeted re-export. Keep
   `#[cfg(test)] mod tests;` in the hub.

(g) **Final hub check.** `cargo check -p cranelisp-backend` warning-clean; `public-api.txt`
   byte-identical; full suite 2846/0/0.

**Things that MUST stay together:**
- All four resolvers + `resolve_chain`/`resolve_driven` in `resolution.rs` (the dedup is
  meaningless if a consumer-specific walker is left behind in another file).
- `FnCompiler` struct def + `inner` + `compile_body` + scope mgmt in `fn_compiler.rs`
  (construction and lifecycle are one concern; splitting the constructor from the struct
  invites the field set drifting out of sync).
- `signature_heap_category` + the drop-glue field-dec helpers in `rc_emission.rs` (the
  heap-class single-source point AND its only structurally-coupled consumers).

> **FnCompiler field-count flag (carry-over, not this wave).** `audits/s87-maintainability.md`
> §2.7 flags `FnCompiler`'s field set as a god-object watch (→ `/arch`). Moving its `impl`
> methods into `fn_compiler.rs` does **not** address the field count — that is a separate
> `/arch` concern (FIXME territory), explicitly out of scope here. This decomposition is a
> file-locality reorg, not a struct-responsibility carve; record the field-count flag as
> unaddressed and route to `/arch` if `/sprint` wants it actioned.

---

## 3. Summary for /dev + /sprint

**5a (`control_flow.rs` → `control_flow/`):** 6 cluster files
(`let_if`, `par_bind`, `lambda`, `fn_as_value`, `free_vars`, `sparkability`) + 1 dedup
file (`capture_rc`). Dedup: 4(+1)-site capture-RC-inc → `emit_capture_inc` /
`emit_capture_inc_into`. Split: `compile_par_bind_continuation` → spine +
`define_par_cont_body` + `alloc_par_cont_closure`. Effort **M** (cluster structure is
already clean; the only behavioural-equivalence step is the capture-inc collapse).

**5b (`compiler/mod.rs` → slim hub + 4 submodules):** `resolution`, `context`,
`fn_compiler`, `rc_emission`. Dedup: 4-site import-chain walk + copy-pasted driver →
`resolve_chain` + `resolve_driven`. Split: `compile_body` → spine + `bind_defn_params`.
Effort **M**, with the `resolve_driven` collapse the hardest piece (the four drivers must
be diffed for equivalence first) and `CompileContext`'s `pub` re-export the one
public-api hazard.

**Located for the brief:** the `emit_extern_call_*` ladder is in `vec_codegen.rs`
(`_2/_3/_4`) + `control_flow.rs` (`_1`), **not** `mod.rs` — recommend it as a **separate**
S-effort dedup task (backlog item 7), not folded into either decomposition.

**Overarching `/dev` rule:** dedups and over-budget splits land **in place** (before the
file moves) so their diffs are reviewable against the original line numbers; the file
moves are then pure cut-paste + `use`/`mod`/re-export wiring. Suite green after every
step. `public-api.txt` byte-identical at the end (the one watch item: `CompileContext`'s
`pub` re-export in 5b).

## Next skills

- `/dev` — narrow `cranelisp-backend`, to execute 5a then 5b (serial; single working
  tree). Land each dedup/split as its own commit before the file moves.
- `/review` — narrow `cranelisp-backend`, to check the change-set against this doc's §0
  invariants (behaviour-preserving, public-api byte-identical, suite green) and confirm
  no logic drifted during the moves.
- `/arch` — only if `/sprint` wants the `FnCompiler` field-count god-object watch
  (§5b.4 carry-over) actioned; that is a struct-responsibility question, out of scope here.
