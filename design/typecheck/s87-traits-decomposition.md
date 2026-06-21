# `traits.rs` decomposition — S87 hygiene (Wave 5e design)

Owner: `/design` (typecheck). Status: **design only — `/dev` executes.** Subordinate to
`design/typecheck/typecheck.md` (master) and `design/typecheck/traits.md` /
`design/typecheck/monomorphisation.md` (subsystem). Where this doc and the master
disagree, the master wins; this doc is a scoped decomposition elaboration.

This document plans the decomposition of `crates/cranelisp-typecheck/src/traits.rs`
(2824 raw lines / ~1718 corrected prod LOC — the densest production module in the
workspace) into a `traits/` submodule set. It is the **highest-risk item** in the S87
maintainability backlog (`audits/s87-maintainability.md` Part 2 §2.3 + Part 3 item 21,
risk **high**), explicitly routed `target: /design` **first** before any `/dev` work.

The driving goal (user): *coherent and cohesive modules of manageable size.* The binding
constraints: **behaviour-preserving** (the `traits/tests.rs` sibling suite green
throughout) and **public surface UNCHANGED** (`public-api.txt` byte-identical).

---

## 0. The load-bearing fact that de-risks the whole move

**`traits.rs` is entirely crate-private. None of its items appear in `public-api.txt`.**

- `lib.rs:232` declares `mod traits;` — **private**, never `pub mod`, never `pub use
  traits::…`. Verified: `grep -in 'active\|monomorph\|trait_decl\|mangled' public-api.txt`
  returns nothing; the file is 121 lines and names no traits item.
- Every method in the file is on `impl<C, L> TypeCheckEnv<'_, C, L>` and is `pub(crate)`
  or private; the free functions are `fn` (private) or `pub(crate) fn` (only
  `build_mangled_name`). `ActiveConstraints` is `pub struct` but reached as
  `crate::traits::ActiveConstraints` — crate-internal, not re-exported.

**Consequence for the migration.** Splitting `traits.rs` into `traits/registry.rs`,
`traits/impl_check.rs`, etc. is a **pure intra-crate move**:

1. `lib.rs` keeps the single private `mod traits;` line; `traits/mod.rs` becomes the new
   module root that declares `mod registry; mod impl_check; …` and re-exports nothing to
   `lib.rs` it does not today.
2. Because all methods are `impl TypeCheckEnv` blocks, and **Rust allows inherent-impl
   blocks for one type to be spread across any number of submodules of the defining
   crate**, moving a method to a sibling file requires NO visibility change — the method
   keeps its `pub(crate)` and remains callable from `checker.rs`/`program.rs`/`infer.rs`
   exactly as before.
3. The only visibility care needed is for the **free functions** the submodules share
   (`concrete_type_name`, `build_mangled_name`, the `resolve_*_type_expr` family, the
   `collect_*` walkers, `type_expr_*` predicates) — these become `pub(super)` /
   `pub(crate)` so the new sibling modules can reach them. **No `pub`** — none crosses
   the crate boundary, so `public-api.txt` stays byte-identical by construction.

This is the single most important framing for `/dev`: **this is a file-organisation
refactor, not an API refactor.** The `public-api.txt` invariant is satisfied trivially as
long as no item gains `pub` and `mod traits` stays private. The risk is **not** API
breakage; it is **behaviour drift inside `monomorphise_call`** (§2) and **accidental
visibility-widening** (§4).

---

## 1. The cohesive concern clusters (validated against source)

The maintainability pass proposed `trait-method resolution / impl-storage / monomorphise
/ dispatch`. Read against the actual file, the genuine clusters are **six**, not four —
the pass under-counted the *registration* cluster (separate from impl-check) and the
*type-expr resolution* cluster (the free-function tail). The cluster boundaries below are
the section banners the file already carries (`// ---- Trait Registration ----`, etc.),
which is why the cut lines are clean.

| # | Target submodule | What moves (line ranges in current `traits.rs`) | Cohesion rationale |
|---|---|---|---|
| 1 | `traits/registry.rs` | `ActiveConstraints` struct + impl (L62–119); `register_trait_decl` (L131–212); `register_hkt_trait` (L216–306); `register_trait_method` (L308–355); `build_method_type` (L362–389) | The **write-side**: turning a parsed `TraitDecl` into symbol-table `TraitDecl` + per-method `Def` entries. `ActiveConstraints` lives here because it is the inference-time companion of registration (constraints recorded at registration, consulted at generalize). One concern: "a trait declaration becomes registry state." |
| 2 | `traits/impl_check.rs` | `register_trait_impl` (L398–573); `check_impl_methods_present` (L576–605); `check_impl_method` (L613–635); `check_impl_method_with_sig` (L652–802); `finalize_impl_method_writeback` (L825–910); `check_hkt_impl_method` (L919–1015); `check_defn_body_with_types` (L1022–1049); `generate_default_methods` (L1052–1107) | The **impl-recording + method-body-check** concern: validate an `(impl Trait Type …)`, store the `TraitImpl` entry (Decision 45 chain-follow `impl$FQType$FQTrait`), type-check each method body (single + HKT paths), and write mangled-name `Def`s. `finalize_impl_method_writeback` is the **already-extracted shared tail** of the single/HKT paths (audit Finding 3 resolution) — it belongs with both its callers. |
| 3 | `traits/dispatch.rs` | `try_resolve_trait_method` (L1121–1213); `primitive_for_trait_method` table (L1237–1287); `is_trait_method` / `is_trait_method_with_state` (L1300–1308); the nullary-return-poly D-default helpers `method_return_dispatch_type` (L2663–2678), `method_self_in_return` (L2683–2693), `method_self_in_return_in_module` (L2698–2734), `type_expr_references_self` (L2557–2567); the HKT-dispatch helpers `hkt_param_idx_for_method` (L2627–2647), `find_hkt_param_index_in_registry` (L2749–2765), `find_hkt_param_index_in_module` (L2775–2816) | The **read-side dispatch**: at a call site, decide *which impl* a trait-method call resolves to. The D-default helpers (this sprint's fix) are the dispatch-argument-selection logic for the nullary return-poly case — they belong WITH `try_resolve_trait_method`, their sole caller (see §4 hazard). The HKT-param-index helpers are also dispatch-argument selection. `primitive_for_trait_method` is the static lowering table consulted during dispatch. |
| 4 | `traits/monomorphise.rs` | `instantiate_constrained` (L1320–1362); **`monomorphise_call` (L1381–1684, ~307L)**; `register_mono_entry` (L1688–1737); `instantiate_and_resolve` (L1741–1785); `verify_constraints` (L1789–1822); `recheck_body_for_mono` (L1838–1881); `resolve_inner_constrained_calls` (L1885–1944); `monomorphise_inner_parametric_hops` (L1967–2081); `get_constrained_fn` (L2085–2128); free fns `collect_apply_var_calls` (L2144–2159), `collect_self_apply_calls` (L2166–2181), `build_mangled_name` (L2183–2206), `concrete_type_name` (L2211–2220) | The **monomorphisation engine** (`design/typecheck/monomorphisation.md` is the subsystem doc). This is the largest and most load-bearing cluster; `monomorphise_call` is documented load-bearing (S83/0355 cross-module mono + S84 concrete-boundary seam). `concrete_type_name` + `build_mangled_name` live here because the mangler is mono's naming primitive (its three callers are all in this cluster: `monomorphise_call`, `resolve_inner_constrained_calls`, `monomorphise_inner_parametric_hops`, plus one external in `program.rs`). |
| 5 | `traits/type_resolve.rs` | `impl_target_name` / `impl_target_name_or_panic` (L30–38); `type_from_intrinsic_ref` (L2323–2334); `resolve_trait_type_expr` (L2337–2392); `resolve_type_expr_hkt` (L2399–2465); `resolve_type_expr_hkt_impl` (L2470–2531); `type_expr_uses_con_var` (L2534–2549); `find_hkt_param_index` (L2570–2577); `con_var_arity` (L2580–2592); `find_applied_arity` (L2595–2613); `build_default_body` (L2229–2311); `trait_decl_matches` (L51–60) | The **`TypeExpr → Type` resolution free functions** + small structural predicates. These are pure free functions (no `self`), shared by registry + impl_check. The audit (§2.3) flagged the 3 `resolve_*_type_expr` variants as "3 near-dup" consolidation candidates — co-locating them here makes that future consolidation a one-file edit (do NOT attempt the consolidation in this sprint; see §4). `build_default_body` + `trait_decl_matches` are small structural helpers that ride along. |
| 6 | `traits/mod.rs` | Module root: file-level `//!` doc; `use` of `cranelisp_types::…`; `mod registry; mod impl_check; mod dispatch; mod monomorphise; mod type_resolve;` declarations; `#[cfg(test)] mod tests;` + `#[cfg(test)] mod primitive_dispatch_tests;` (the two existing sibling test files move under `traits/` — they are ALREADY there: `traits/tests.rs`, `traits/primitive_dispatch_tests.rs`) | The hub. Carries the crate-private re-exports (if any) the other typecheck modules import (`crate::traits::ActiveConstraints`, `crate::traits::build_mangled_name`). |

> **Note on the existing `traits/` dir.** `crates/cranelisp-typecheck/src/traits/` already
> exists holding `tests.rs` (53 KB) and `primitive_dispatch_tests.rs`, declared from
> `traits.rs` as `#[cfg(test)] mod tests;` / `mod primitive_dispatch_tests;`. When
> `traits.rs` becomes `traits/mod.rs`, those two declarations move verbatim into
> `mod.rs`. Rust resolves `traits/mod.rs` + `traits/tests.rs` identically to today's
> `traits.rs` + `traits/tests.rs`, so the test sibling files do not move and their
> `use super::*;` still reaches the production items (now re-exported through `mod.rs`).

### 1.1 Why six, not four (revision of the maintainability proposal)

- The proposal's **`impl-storage`** conflates two concerns: *registration* (write a
  `TraitDecl`/method `Def` — cluster 1) and *impl recording + body check* (write a
  `TraitImpl` + mangled `Def`s — cluster 2). These have different inputs (`TraitDecl` vs
  `TraitImpl`), different symbol-table writes, and different sizes (~250L vs ~600L).
  Splitting them keeps each file under ~600L and matches the file's own banner structure.
- The proposal's **`monomorphise`** is correct as one cluster, but the proposal omitted
  that the two mangling/naming free fns (`build_mangled_name`, `concrete_type_name`)
  belong with it, not with the type-resolve free-fn tail.
- The proposal had no home for the **`TypeExpr` resolution free-function family** (~280L
  of pure functions at the file tail) — cluster 5 captures it. This is the cluster the
  audit's "3 near-dup `resolve_*_type_expr`" finding (S87 §2.3) lives in.

### 1.2 Resulting sizes (approximate corrected prod LOC)

| Submodule | ~prod LOC | Largest fn |
|---|--:|---|
| `traits/registry.rs` | ~230 | `register_hkt_trait` (~90), `build_method_type` (~28) |
| `traits/impl_check.rs` | ~470 | `check_impl_method_with_sig` (~150), `check_hkt_impl_method` (~96), `register_trait_impl` (~110) |
| `traits/dispatch.rs` | ~270 | `try_resolve_trait_method` (~93), `find_hkt_param_index_in_module` (~42) |
| `traits/monomorphise.rs` | ~530 | `monomorphise_call` (~180 **after §2 split**, was ~307), `monomorphise_inner_parametric_hops` (~115) |
| `traits/type_resolve.rs` | ~280 | `resolve_type_expr_hkt` (~67), `resolve_type_expr_hkt_impl` (~62) |
| `traits/mod.rs` | ~40 | — |

All files land under the ~600-LOC navigability target; `monomorphise.rs` is the largest
and stays the densest, which is correct — it is the load-bearing cluster and gets the most
scrutiny.

---

## 2. `monomorphise_call` decomposition (the riskiest single item)

`monomorphise_call` (L1381–1684, ~307L) is the standout over-budget function
(`audits/cranelisp-typecheck-s87.md` Finding S87-2). The audit already names the shape:
*"a 7-phase sequential driver"* and recommends extracting *"`resolve_mono_trait_home` /
`recheck_and_resolve_body` / `register_and_verify`."* This section makes the phase
boundaries precise and pins the **invariant each phase relies on**, because the phases
mutate `state.subst` / `state.current_module` / the side-maps in a careful order and a
wrong cut silently mis-monomorphises (the symptom is a spurious `no impl of trait T for
type X`, or — post-S84 — a `from_expr` ambiguity error on a valid program, or a SIGSEGV
one hop deeper).

> **The method is already comment-delimited into phases.** The extraction is mechanical
> *if and only if* the state-threading contract below is honoured exactly. Do NOT
> reorder phases, do NOT change what is saved/restored, do NOT change the
> `state.subst` clone/restore points.

### 2.1 The phases, with boundaries and invariants

Numbered by the order they execute. Each becomes a private method on
`impl TypeCheckEnv` (in `traits/monomorphise.rs`), called in sequence by the slimmed
`monomorphise_call`. **Names are proposals; `/dev` may adjust.** The "Invariant relied
on" column is the contract that must not break.

| Phase | Lines | Proposed extraction | What it does | Invariant relied on (DO NOT BREAK) |
|---|---|---|---|---|
| **P0 — lookup** | 1390–1396 | *(inline — keep in `monomorphise_call`)* | `get_constrained_fn(state, fn_name, home)` → early-return `None` if not monomorphisable; clone `scheme` + `defn`. | `home` selects the lookup module (defining-module for imported callees, 0355). Early `None` is the "not a mono target" signal — callers depend on `Ok(None)` vs `Ok(Some)`. |
| **P1 — instantiate + concrete params** | 1398–1410 | *(inline — short)* | `instantiate_and_resolve` → `(resolved, var_mapping)`; extract `concrete_param_types`; early-`Ok(None)` if `resolved` is not a `Type::Fn`; build `mangled_name`. | `var_mapping` (original→fresh ids) MUST flow to P2's `verify_constraints` — the constraints are keyed by ORIGINAL scheme var_ids, only FRESH vars are in `state.subst` (0355 cross-module collision guard). Losing the mapping reintroduces the `IO`-collision bug. |
| **P2 — verify constraints (module-switched)** | 1412–1426 | `verify_mono_constraints(state, &scheme, &var_mapping, home, call_span)` | Save `current_module`, switch to `home`, run `verify_constraints`, **restore unconditionally**, then `?` the result. | The module switch MUST wrap ONLY `verify_constraints` and MUST restore before propagating the error (`verify_result?` AFTER restore). Impl lookup roots in `home` so a defining-module-local impl is visible. |
| **P3 — call-site return pinning (0349)** | 1428–1451 | `pin_call_site_return(state, &resolved, call_span)` → `concrete_ret_ty` | Extract `concrete_ret_ty` from `resolved`; if `state.expr_types[call_span]` exists, unify it with `concrete_ret_ty`. | This unify writes into `state.subst` and is what pins the CALLER's result var (0344/0349). It MUST run on the parent's live `state.subst` (NOT an isolated clone) — this is the one place the parent subst is intentionally mutated. Early-`Ok(None)` if `resolved` is not `Fn`. |
| **P4 — recheck body + harvest** | 1453–1476 | `recheck_and_resolve_inner(state, fn_name, &defn, &concrete_param_types, &concrete_ret_ty, home)` → `(resolutions, mono_expr_types)` | Wrap `defn` (DefnVariant) into a temp single-variant `Defn`; `recheck_body_for_mono` (saves/restores side-maps + module); `resolve_inner_constrained_calls`; `monomorphise_inner_parametric_hops` (recursive — this is where deeper hops are minted). | `recheck_body_for_mono` saves/restores `method_resolutions`/`expr_types`/`pending_auto_curry`/`current_module` itself — the extraction must pass the temp `wrap_defn` through by `&mut` so the post-passes annotate the SAME clone. `monomorphise_inner_parametric_hops` isolates `state.subst` around EACH inner recursion (0344) — that isolation stays inside that fn, do not lift it. |
| **P5 — self-recursion dispatch (0374)** | 1518–1542 | `record_self_recursion_dispatch(&wrap_defn, fn_name, &mangled_name, &mono_expr_types, &mut resolutions)` | Collect self-`Apply` calls; for each at the SAME concrete arg types (same `mangled_name`), insert a `SigDispatch` to this mono. | Skips spans already in `resolutions.resolved_calls`. The same-arg-type guard (`build_mangled_name(...) == mangled_name`) is what distinguishes the same-mono self-call from a distinct hop already minted in P4. This is a pure `resolutions` mutation — no `state.subst` touch. |
| **P6 — build annotated mono defn** | 1544–1577 | `build_annotated_mono_defn(state, fn_name, &mangled_name, &defn, &mono_expr_types, &resolutions, home)` → `Defn` | Recover parent metadata (docstring/visibility) via `resolve_terminal_entry_and_home` rooted at `home`-or-current; build `mono_defn_ast`; `annotate_defn_from_maps`; `apply_subst_to_defn`. | Metadata is read from `home.unwrap_or(current_module)` (0355). `apply_subst_to_defn` reads the parent's live `state.subst` (which P3+P4 populated) — it MUST run after P4, on the parent subst. |
| **P7 — concrete-boundary view + register** | 1579–1683 | `finalize_mono_codegen_view(state, mono_defn_ast, &mangled_name, &concrete_param_types, &concrete_ret_ty, defn.span)` → builds `MonoDefn`, runs `MonoExpr::from_expr` (the §3.11.1 ambiguity error on `Err`), calls `register_mono_entry`, returns `Some(mono_defn)` | The S84 concrete-boundary seam: `from_expr` over the subst-resolved body; `Err` → the unified ambiguity error; `Ok` → `MonoDefnVariant` codegen view; `register_mono_entry`. | `from_expr` MUST run AFTER `apply_subst_to_defn` (P6) — it reads each node's resolved `inferred_type`. The `Err` arm is the completeness backstop (Phase-4-A); it MUST stay an error return, not a silent skip. `register_mono_entry` preserves an existing slot on REPL-redefine. |

The slimmed `monomorphise_call` becomes a ~30-line driver: P0/P1 inline, then sequential
calls P2→P7 with the `?` and early-`Ok(None)` returns at the documented points.

### 2.2 The three state channels — the invariant that governs the whole split

`monomorphise_call`'s correctness rests on three mutable channels threaded through the
phases. The split must preserve **where each is mutated and where each is
isolated/restored**:

1. **`state.subst`** — the substitution. Mutated by P1 (`instantiate_and_resolve`
   unifies params), P3 (call-site return pin — the deliberate parent mutation), P4-inner
   (each inner hop is wrapped in `saved_subst = clone(); … ; state.subst = saved_subst`
   — isolation lives inside `monomorphise_inner_parametric_hops`). **Hazard:** if a future
   refactor lifts the P4-inner isolation up to the driver, the 0344 fold accumulator
   re-collapses. Keep isolation where it is.
2. **`state.current_module`** — the resolution root. Switched-and-restored around P2
   (`verify_constraints`) and inside P4 (`recheck_body_for_mono` does its own
   save/restore). Each switch is `home.map(|h| std::mem::replace(...))` + unconditional
   restore. **Hazard:** the restore must happen BEFORE the `?`-propagation of that phase's
   result (the current code restores then `verify_result?`). An extraction that returns
   early on error before restoring leaks the switched module into the caller.
3. **The side-maps** (`method_resolutions`, `expr_types`, `pending_auto_curry`) — harvest
   buffers. `recheck_body_for_mono` (inside P4) takes/restores them so the mono body's
   resolutions don't pollute the parent's. P6 reads the harvested `mono_expr_types` /
   `resolutions` (returned by P4), not the live `state` ones. **Hazard:** P6 must consume
   the RETURNED harvest, not re-read `state.method_resolutions` (which P4 already
   restored to the parent's).

### 2.3 Staging recommendation for `monomorphise_call`

Per §4 and the audit's sequencing: **land the `monomorphise_call` phase-split IN-PLACE in
`traits.rs` (no file move) and run the full suite green FIRST.** Only after the suite is
green with the slimmed function does the file move (cluster 4) happen. This isolates the
one genuine-untangle risk (the phase split) from the mechanical-move risk (the file
split), so a red suite unambiguously points at one or the other. Do NOT combine them in
one change-set.

---

## 3. Prelude-fallback dedup (audit Finding S87-5) — scope and a subtlety

The audit (`audits/cranelisp-typecheck-s87.md` §2 + Finding S87-5) found the
prelude-fallback gate has **2 direct callers + 1 inline** beside the shared
`cranelisp_types::resolve_with_fallback` primitive. The canonical single-name helper is
`checker.rs::resolve_terminal_entry_or_prelude` (L1451) — it bundles gate + the shared
primitive + chain-follow + I-1 public filter for a SINGLE NAME lookup.

### 3.1 What the traits.rs sites actually are — and why they do NOT route through the canonical helper

The two traits.rs prelude-fallback sites are:

- `find_hkt_param_index_in_registry` (L2749) → `find_hkt_param_index_in_module` (L2775)
- `method_self_in_return` (L2683) → `method_self_in_return_in_module` (L2698) — **this
  sprint's D-default addition**

**Critical distinction:** these are NOT single-name resolutions. They are **bulk
trait-decl iterations** (Principle 17 shape 4 — current-module-only bulk introspection):
they iterate *every* `TraitDecl` visible in a module looking for one that declares a
method named `method_name`, then read a field off it (`hkt_param_index` resp. whether
`ret_type` references `Self`). They cannot route through
`resolve_terminal_entry_or_prelude`, which resolves ONE name and returns ONE terminal
entry — there is no single name to resolve (the method name is not a symbol-table key;
it is a field on a `TraitDecl` entry whose key is the *trait* name).

So Finding S87-5's "route the direct callers through the shared primitive" does NOT apply
to these two as a name-resolution reroute. What they DO share is the **iterate-current +
prelude-fallback-iterate-with-public-filter** STRUCTURE — and that structure is now
**duplicated across the two `*_in_module` helpers and the two `*_in_registry` /
`method_self_in_return` orchestrators** (`find_hkt_param_index_in_module` and
`method_self_in_return_in_module` are near-identical: same name-collection block, same
`for name … resolve_terminal_entry_and_home … if let TraitDecl … for method …` loop, only
the per-method field read differs).

### 3.2 The dedup actually warranted — a shared trait-decl-method scan

Extract ONE shared bulk-scan helper that both D-default and HKT-index paths call. Proposed
shape (private to `traits/dispatch.rs`):

```text
fn find_trait_method_decl<R>(
    &self, state, method_name: &str,
    read: impl Fn(&TraitMethodSig) -> R,   // hkt_param_index  OR  references-Self
) -> Option<R>
```

It encapsulates: iterate `current_module` (staging-view) → on miss, consult
`prelude_fallback_target` with `public_only = true` → for each visible name,
chain-follow to a terminal `TraitDecl`, find the method, return `read(method)`. The two
existing callers become one-liners:

- `find_hkt_param_index_in_registry` → `find_trait_method_decl(state, name, |m| m.hkt_param_index).flatten()`
- `method_self_in_return` → `find_trait_method_decl(state, name, |m| type_expr_references_self(&m.ret_type)).unwrap_or(false)`

This collapses ~110 lines (the two `_in_registry`/`method_self_in_return` +
two `_in_module`) to ~50, and puts the **I-1 public-head filter discipline in ONE place**
— which is exactly the hardening Finding S87-5 wants (the seam DEF-1 fragmented once
already; one helper guards against the next missed chokepoint).

### 3.3 The behaviour subtlety to flag for `/dev`

There IS a real behaviour difference between the two existing helpers that the shared
helper must preserve, NOT smooth over:

- `find_hkt_param_index_in_module` returns `method.hkt_param_index` which is itself an
  `Option<usize>` — so the helper returns `Option<Option<usize>>` and the caller
  `.flatten()`s. A method present but with `hkt_param_index: None` is DISTINCT from a
  method absent.
- `method_self_in_return_in_module` returns a `bool` and treats "method found, ret_type
  has no Self" the same as a partial result, but "method absent" falls through to the next
  candidate name and ultimately `false`.

The generic `read: Fn(&TraitMethodSig) -> R` cleanly preserves both (R = `Option<usize>`
resp. `bool`); the helper returns `Option<R>` (`None` = method not found in any visible
trait decl), and each caller decides the not-found default. **Do not collapse the
not-found case into the read's own `None`** — that would conflate "no such method" with
"method exists but field is None," which the HKT path relies on distinguishing.

> **Note on the `src`-side / `checker`-side prelude-fallback.** The Wave-2 finding's
> canonical `resolve_terminal_entry_or_prelude` is the NAME-resolution helper, and its
> root-tier subtlety (the `src`-side REPL `describe_symbol` walk adds a `root`-module hop
> the typecheck side does not) is a **`/int`-side** concern (`src/repl.rs`), out of scope
> for this typecheck-internal decomposition. This doc's §3 dedup is purely the two
> typecheck **bulk-scan** sites; it does not touch `resolve_terminal_entry_or_prelude` or
> any name-resolution chokepoint. Flag for `/dev`: do NOT try to fold these bulk scans
> into the name-resolution helper — they answer a different question.

### 3.4 Staging this dedup

The §3.2 dedup is **independent of the file split** and is the lower-risk piece. Recommend
landing it **after** the file move (so it lands in the new `traits/dispatch.rs` where both
callers already live), as a separate change-set, suite-green-verified. It is NOT a
prerequisite for the decomposition — if sprint capacity is tight, the file move alone is
the deliverable and §3.2 carries forward. (It is below the audit's rule-of-three
extraction threshold strictly — 2 callers + the structural twin — but the D-default
addition this sprint made it a genuine twin, so it has crossed into "worth doing.")

---

## 4. Migration order + risk notes for `/dev`

**This is the highest-risk decomposition in the S87 backlog. Stage conservatively. One
change-set per stage, suite green between each. Do NOT batch.**

### 4.1 Recommended staging (most conservative)

| Stage | Action | Why this order | Suite gate |
|---|---|---|---|
| **A** | **Split `monomorphise_call` into phases IN-PLACE** (still in `traits.rs`, no file move). §2. | Isolates the one genuine untangle from all file-move noise. A red suite here is unambiguously a phase-cut error. | Full `cargo nextest run` green (incl. the 14 known-defect guards still red — no NEW red). `traits/tests.rs` + `program::tests` cross-module-mono tests are the acceptance set. |
| **B** | **Create `traits/mod.rs` from `traits.rs`; move clusters 1–5 into sibling files.** §1. Pure mechanical move; adjust free-fn visibility to `pub(super)`/`pub(crate)`; move the two `mod tests;`/`mod primitive_dispatch_tests;` decls into `mod.rs`. | The phase-split is already green, so the move is pure file-organisation. | Suite green; **`public-api.txt` byte-identical** (`diff` it — see §4.3). |
| **C** *(optional, capacity-permitting)* | **§3.2 prelude-fallback bulk-scan dedup** in the new `traits/dispatch.rs`. | Lands where both callers now live. Independent; defer-able. | Suite green; the HKT-dispatch + D-default-dispatch tests (`primitive_dispatch_tests` + the nullary-return-poly tests) are the acceptance set. |

If capacity allows only one stage, do **A only** (the function-budget win on the
load-bearing fn, lowest blast radius, no file churn). Stage B is the navigability win but
is mechanical; Stage C is hardening.

### 4.2 The explicit hazard list

1. **MUST stay together — the D-default helpers with their resolver.** `try_resolve_trait_method`
   (cluster 3) is the SOLE caller of `method_return_dispatch_type` (L1146), which calls
   `method_self_in_return` → `method_self_in_return_in_module` → `type_expr_references_self`.
   These four (this sprint's nullary-return-poly fix) MUST land in the same submodule as
   `try_resolve_trait_method` (`traits/dispatch.rs`). Splitting the resolver from its
   dispatch-type helper across files is legal Rust but defeats the cohesion goal and
   obscures the just-added fix. Cluster 3 keeps them together by design — verify `/dev`
   does not scatter them.
2. **MUST stay together — `monomorphise_call`'s phase helpers + the mangling free fns.**
   The P2–P7 extractions (§2.1), `register_mono_entry`, `instantiate_and_resolve`,
   `verify_constraints`, `recheck_body_for_mono`, `resolve_inner_constrained_calls`,
   `monomorphise_inner_parametric_hops`, `get_constrained_fn`, `build_mangled_name`,
   `concrete_type_name`, and the two `collect_*_apply_calls` walkers are one cohesive unit
   in `traits/monomorphise.rs`. `build_mangled_name` is `pub(crate)` (one external caller
   in `program.rs:3207`) — it MUST keep `pub(crate)`, not narrow to `pub(super)`.
3. **Visibility widenings — the one thing that can break `public-api.txt`.** The free
   functions currently `fn` (private to `traits.rs`) become reachable across the new
   sibling files. Grant them **`pub(super)`** (visible within `traits/`) — NOT `pub(crate)`
   unless an external caller exists, and NEVER `pub`. Audit each: only `build_mangled_name`
   needs `pub(crate)` (external caller); all other free fns
   (`concrete_type_name`, `resolve_trait_type_expr`, `resolve_type_expr_hkt`,
   `resolve_type_expr_hkt_impl`, `type_from_intrinsic_ref`, `type_expr_uses_con_var`,
   `type_expr_references_self`, `find_hkt_param_index`, `con_var_arity`,
   `find_applied_arity`, `build_default_body`, `impl_target_name`,
   `impl_target_name_or_panic`, `trait_decl_matches`, `primitive_for_trait_method`,
   `collect_apply_var_calls`, `collect_self_apply_calls`) → `pub(super)`. **A free fn that
   accidentally gets `pub` would still not enter `public-api.txt` because `mod traits` is
   private — but DO NOT rely on that; keep the minimal visibility as the structural guard
   (Principle 18 — enforce invariants structurally).**
4. **`ActiveConstraints` stays `pub struct` but crate-internal.** It is `pub struct`
   today (reached as `crate::traits::ActiveConstraints` from `checker.rs`). When it moves
   to `traits/registry.rs`, `traits/mod.rs` must `pub(crate) use registry::ActiveConstraints;`
   (or `checker.rs` updates its `use` path to `crate::traits::registry::ActiveConstraints`).
   Either works; the `mod.rs` re-export is cleaner (keeps `checker.rs` unchanged). Its
   methods stay `pub`/`pub(crate)` as today — they do not cross the crate boundary because
   the type itself does not (private `mod traits`).
5. **The `impl<C, L> TypeCheckEnv` block header repeats per file.** Each sibling that
   hosts methods re-opens `impl<C: CodeStore, L: LinkerStore> TypeCheckEnv<'_, C, L> { … }`.
   This is correct and idiomatic. The generic bounds + lifetime must match exactly across
   all blocks or the methods won't be recognised as the same impl. Copy the header
   verbatim.
6. **`use` hygiene.** Each new file needs its own `use cranelisp_types::{…}` +
   `use crate::checker::{CheckState, TypeCheckEnv};` + `use crate::scheme;` subset. Let
   the compiler/clippy drive the minimal set; do not blanket-import. (Unused-import
   warnings are the cheap signal that a cut was clean.)

### 4.3 The behaviour-preserving invariants (the acceptance contract)

- **Suite green throughout.** `cargo nextest run` (per root `CLAUDE.md` §Testing) — the
  full suite completes in ~9s. The known 14 failing-not-ignored defect guards + 2 unit
  guards stay red (they are not regressions); ANY red beyond that named set is a
  regression and blocks the stage. The `traits/tests.rs` sibling (952 test LOC) +
  `program::tests` cross-module-mono tests + `primitive_dispatch_tests` are the
  behaviour acceptance set.
- **`public-api.txt` byte-identical.** Regenerate per the baseline-diff discipline and
  `diff crates/cranelisp-typecheck/public-api.txt <regenerated>` → empty. This is the
  structural proof that no item gained crate-boundary visibility. Because `mod traits` is
  private (§0), this holds by construction if no `pub` is added and the re-export in §4.2
  item 4 stays `pub(crate)`.
- **No new inline FIXMEs** (root `CLAUDE.md`); if `/dev` finds a design gap, file
  `design/arch/fixmes/NNNN-*.md` `target: /design`.
- **CLIF spot-check for the mono path (optional, high-value).** Because Stage A touches
  `monomorphise_call` (the codegen-reaching seam), a `/clif <mono-name>` REPL check or
  `CRANELISP_CODEGEN_TRACE=1` on one cross-module-mono test before/after Stage A confirms
  the emitted IR is unchanged — the strongest behaviour-preservation evidence for the
  load-bearing function (root `CLAUDE.md` §"Keep reductions as small as possible").

### 4.4 What this decomposition deliberately does NOT do

To bound risk, these adjacent opportunities are **explicitly out of scope** — note them
for a future wave, do not bundle:

- **The 3 `resolve_*_type_expr` "near-dup" consolidation** (audit §2.3). Co-locating them
  in `traits/type_resolve.rs` (cluster 5) is in scope; *merging* them into one
  parameterised resolver is NOT — it is a genuine semantic change (the three differ in
  Self-handling, con-var handling, and FQTypeName module defaulting) and belongs in its
  own change-set with its own design pass.
- **The FQ-naming "no impl" renderer fix** (Finding S87-1 — `concrete_type_name` strips
  module qualification at the two `no impl of trait T for type X` sites). That is a
  separate user-facing defect with its own `/qa` repro owed; it touches
  `concrete_type_name`'s callers in `traits/dispatch.rs` + `traits/monomorphise.rs` but is
  a behaviour CHANGE, not a behaviour-preserving move. Keep it out of the decomposition
  change-sets.
- **`check_hkt_impl_method` (~103L) / `check_impl_method_with_sig` (~150L) further
  splitting.** Both are over/at budget (Finding S87-2) but co-locating them with their
  shared tail `finalize_impl_method_writeback` in `traits/impl_check.rs` is the S87
  deliverable; decomposing their bodies is a follow-up.

---

## 5. Quality-attribute assessment (per `/design` stewardship)

| Attribute | This decomposition's effect |
|---|---|
| **Simplicity** (Principle 6) | Net positive — no new complexity, removes the ~307L god function's cognitive load by phasing it. The §3 dedup removes ~60L of duplicated bulk-scan. Carries only the complexity the trait/mono spec demands. |
| **Maintainability** | The headline win. Six ~250–530L cohesive files replace one 1718-LOC dense file; a future change has bounded blast radius (a registration change touches `registry.rs` only; a mono change touches `monomorphise.rs` only). Matches the user's "coherent and cohesive modules of manageable size." |
| **Observability** | Unchanged — no trace surface touched. The CLIF spot-check (§4.3) is a one-time migration aid, not a new hook. |
| **Concurrency-safety** | Unchanged — `traits.rs` holds no shared state; all state is per-call `CheckState`. The decomposition does not alter the mutation discipline (`design/typecheck/typecheck.md` §6). |
| **Performance** | Unchanged — same call graph, same `state.subst` operations. The phase extraction is zero-cost (private methods inline at the same call depth). |
| **Testability** (Principle 5) | Improved — the phase helpers (§2.1) become independently unit-testable seams (P2 `verify_mono_constraints`, P7 `finalize_mono_codegen_view`), and the `traits/tests.rs` sibling already isolates the test surface from production. `/dev` may add narrow unit tests per extracted phase (mandatory unit-test-per-change applies if any phase boundary is non-trivially adjusted). |

Principles cited: **6** (complexity budget — the split carries no new complexity),
**7** (single source of truth — §3 collapses the duplicated bulk-scan to one helper),
**17** (module-locality — the bulk-scan helper preserves current-module-rooted +
prelude-fallback discipline), **18** (enforce invariants structurally — minimal
visibility is the structural guard on `public-api.txt`), **20** (model invariants by
representation — the §2 phase boundaries preserve the concrete-boundary `from_expr`
completeness backstop).

---

## 6. Next skills

- `/dev` (typecheck) — execute Stage A (`monomorphise_call` phase split in-place), then
  Stage B (file move), then optional Stage C (§3 dedup), each as its own suite-green
  change-set. The §2 phase table is the in-place plan; §1 is the file-move map; §4 is the
  hazard list. Mandatory unit-test-per-change applies to any non-trivial phase-boundary
  adjustment.
- `/review` (typecheck) — point-in-time review of each landed stage against this doc's
  invariants (§2.2 state channels, §4.2 hazards, §4.3 acceptance contract). Per
  `memory/feedback_review_root_cause_and_duplication`: check the §3 dedup actually
  collapses the twin (not a symptom patch) and that no phase extraction deepened a
  state-channel duplication.
- `/qa` — owns the FQ-naming "no impl" repro (Finding S87-1, out of scope here) if that
  separate defect is scheduled; not required for this decomposition.
