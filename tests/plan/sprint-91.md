# Sprint 91 — Failing-test PLAN (Phase 3 deliverable)

**Owner:** `/qa`. **Status:** PLAN ONLY — no test code yet. The failing tests
themselves land in **Phase 5 Stage 1** (QA-first, sprint-wide, before any per-crate
D/D/R cycle). This document enumerates the test surface so `/sprint` + the user can
review coverage before implementation waves are allocated.

**Scope source:** `sprints/SPRINT.md` (3 threads + FIXME burn-down) incl. the Phase-2
`/arch` verdict, the Pillar-3 design-refinement addendum (R13–R16), and the `### /spec`
rulings subsection. Design of record: `design/arch/repl-embedded-agent.md §11`,
`design/int/agent.md §25`, `design/typecheck/signature-match.md`. Spec rulings already
landed this sprint: appendix-a §A.3 (bitwise prims), §8.5.2/§5.2.6/§7.3.1 (field
accessors + impl-time collision), §8.11.4/§8.11.5 (additive lib-dir union),
§4.8.4/§2.5.2/§6.2 (literal-pattern reconciliation).

## Conventions / legend

- **Tier**: `unit` (`/dev`-authored, `crates/*/src/` `#[cfg(test)]`), `e2e`
  (`/qa`-authored, `tests/*.rs`, subprocess). **No middle tier** (`tests/CLAUDE.md`).
  Unit tiers below are NAMED so the plan shows the full surface, but `/qa` does NOT
  author them — `/dev` lands them in the same change-set as the fix (mandatory-unit-test
  discipline). `/qa` authors the e2e rows.
- **Posture**: `RED-first` = a failing guard `/dev` flips green (the feature/fix does not
  yet exist or is wrong on HEAD); `floor` = green-on-HEAD regression floor (asserts a
  property that already holds and must not regress).
- **P/N**: positive (asserts correct behaviour appears) / negative (asserts wrong
  behaviour is absent). `P+N` = the test carries both arms.
- All e2e tests are free-standing — zero `stdlib/` dependency; `PreludeVariant::None` or
  `PrimitivesOnly` unless operators/ADTs are required, then `TestPrelude`.

---

## Thread A — Pillar 3 `/search` (centerpiece)

Implementation gate (both required): `/typecheck` 0432 root fix (Thread C / R2-a) + CF.2
nice-worker `catch_unwind` (R2-b). Acceptance criteria source: `agent.md §25.8`,
`repl-embedded-agent.md §11`, `signature-match.md §6`.

> **Trigger model (Phase-3 user correction, 2026-06-25):** the burn-down is
> **eager-from-REPL-start-up** — it arms at REPL launch, NOT on first `/search` or first
> agent activation. In `--run`/`--link`/`--release` (batch) modes it **never arms** (the
> REPL-only invariant). An early `/search` may still catch the burn-down mid-flight (the
> partial-results path, A.7). Rows below reflect this model; A.7 carries the
> not-on-first-search `_neg` and the batch-mode-inert `_neg`.

### A.1 — `signature_matches_exact` (unit; `cranelisp-typecheck`)

Pure alpha-equivalence predicate, `fn(&Type,&Type)->bool`. Table-driven over hand-built
`Type`s; no fixture. `/dev`-authored unit suite (named here for surface completeness).
Trace: `signature-match.md §2/§3/§6`.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `sig_exact_id_alpha_equiv` | unit | `(Fn [a] a)` ~ `(Fn [b] b)` (same sharing pattern) | §2 MATCH row 1 | P | RED-first |
| `sig_exact_two_var_alpha_equiv` | unit | `(Fn [a b] a)` ~ `(Fn [x y] x)` | §2 MATCH row 2 | P | RED-first |
| `sig_exact_concrete_plus_var` | unit | `(Fn [Int a] (Vec a))` ~ same w/ renamed var | §2 MATCH row 3 | P | RED-first |
| `sig_exact_neg_arity_differs` | unit | `(Fn [a] a)` ✗ `(Fn [a b] a)` (1 vs 2 params) | §2 NO-MATCH | N | RED-first |
| `sig_exact_neg_sharing_pattern_differs` | unit | `(Fn [a a] a)` ✗ `(Fn [a b] a)` — the **bijectivity guard** (the subtle one) | §2 NO-MATCH | N | RED-first |
| `sig_exact_neg_concrete_not_subsumed_by_var` | unit | `(Fn [Int] Int)` ✗ `(Fn [a] a)` (exact-shape ≠ subsumption) | §2 NO-MATCH | N | RED-first |
| `sig_exact_neg_adt_head_differs` | unit | `(Fn [a] (Option a))` ✗ `(Fn [a] (Vec a))` | §2 NO-MATCH | N | RED-first |
| `sig_exact_neg_fq_module_differs` | unit | `(Box a)` from `m` ✗ `(Box a)` from `n` — **FQ discipline** | §2 NO-MATCH (load-bearing) | N | RED-first |
| `sig_exact_hkt_tyconapp_head_renamed` | unit | two `TyConApp` shapes match under head-renaming | §2.3 | P | RED-first |
| `sig_exact_neg_hkt_head_not_concrete_adt` | unit | a `TyConApp` head ✗ a concrete `ADT` head | §2.3 | N | RED-first |
| `sig_exact_canonical_shape_eq_idempotent` | unit | (if §3.1 helper ships) canon ~equiv pair `==`, diff-sharing `!=`, idempotent | §3.1 | P+N | RED-first |

### A.2 — `signature_matches_partial` (unit; `cranelisp-typecheck`)

Structural-contains sibling; `_exact(q,c) ⟹ _partial(q,c)`. Trace: `signature-match.md §4/§6`.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `sig_partial_param_subtree` | unit | query `(Vec Int)` ✓ candidate `(Fn [(Vec Int)] Bool)` | §4.1 | P | RED-first |
| `sig_partial_concrete_leaf_anywhere` | unit | query `Int` ✓ any candidate mentioning `Int` | §4.1 | P | RED-first |
| `sig_partial_return_subtree_alpha` | unit | query `(Option a)` ✓ `(Fn [b] (Option a))` under per-subtree renaming | §4.2 | P | RED-first |
| `sig_partial_implies_from_exact` | unit | every §2 MATCH row is ALSO a `_partial` match | §4.3 (`_exact ⟹ _partial`) | P | RED-first |
| `sig_partial_neg_sharing_pattern_carries` | unit | query `(Fn [a a] a)` ✗ candidate `(Fn [a b] a)` (no subtree alpha-equiv) | §4.1 | N | RED-first |
| `sig_partial_neg_concrete_leaf_mismatch` | unit | query `(Vec Bool)` ✗ candidate `(Fn [(Vec Int)] Bool)` | §6 | N | RED-first |
| `sig_partial_neg_containment_not_subsumption` | unit | query bare var `a` ✗ candidate `(Fn [Int] Bool)` (single var must NOT match a concrete subtree — the §5 boundary) | §4.1 / §6 (load-bearing) | N | RED-first |

### A.3 — Three-branch indexer coverage (e2e; `tests/agent.rs` or new `tests/search.rs`)

The indexer takes EXACTLY one branch per reachable module (`agent.md §25.1/§25.8`).
Project-fixture e2e: a per-test project tree (lib-dir ∪ project root) with controlled
`.meta` / registry state, driven through the binary. Observation seam: `/search` results
+ trace env (`CRANELISP_MODULE_TRACE`) for the "no typecheck" assertion.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `search_branch_a_registered_module_skipped` | e2e | a module present in the scheduler `ModuleState` registry (any pool state) is SKIPPED by the indexer — the real path owns it | §25.1b / R15 / §25.8(1a) | P | RED-first |
| `search_branch_b_valid_meta_populates_no_typecheck` | e2e | a reachable module with a **valid `.meta`** populates the index with **NO typecheck** (assert `check_forms` not invoked for it via module-trace) | §25.1(b) / R16 / §25.8(1b) | P | RED-first |
| `search_branch_b_neg_no_recheck` | e2e | NEG: the valid-`.meta` branch does NOT re-typecheck (no `MODULE_TRACE` typecheck event for that module) | §25.8(1b) | N | RED-first |
| `search_branch_c_stale_meta_typechecks_writes_meta` | e2e | a module with no/stale `.meta` is **typechecked once** on the nice worker against throwaway staging, then `.meta` is **written** via `cache::write_meta` (no `.o`) | §25.1(c) / R13 / §25.8(1c) | P | RED-first |
| `search_branch_c_neg_no_object_file` | e2e | NEG: branch (c) writes a `.meta` but **no `.o`** and never `register_module`s | §25.1 / R13 | N | RED-first |

### A.4 — No-SharedState-residue keystone `_neg` (e2e) — REWORDED per R13

The keystone +neg. After a burn-down, the four `SharedState` maps (`symbol_tables` /
`module_aliases` / `prelude_fallback` / `introspection`) are **byte-unchanged**. Assert
**NO SharedState entry, NOT "no disk write"** — a branch-(c) `.meta` is expected and
benign (R13). Mirrors `validate_dry_run_discards_does_not_commit` (`pull.rs`).

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `search_burndown_neg_no_sharedstate_residue` | e2e | after a burn-down indexing N modules, NO new entry appears in any of the four `SharedState` maps — observed via REPL introspection (`/list`/`/exports` show no indexed-but-unimported symbols leaking into the live session) | R13 / §25.8(2) | N | RED-first |
| `search_burndown_neg_indexed_symbol_not_in_session` | e2e | a symbol found by `/search` but NOT `/import`ed is absent from `/list`/`/info` (it is reachable, not resident) | R13 / §25.3 | N | RED-first |

> **Note (`/qa`):** the design's +neg mirror is a `SharedState` four-map assertion at the
> Rust-API seam (`pull.rs`-tier). The active suite has **no middle tier**
> (`tests/CLAUDE.md`) — `/qa` cannot construct `SharedState`. The mirror's *unit-tier*
> form (`/dev`-authored, `src/agent/` or `src/session_v4/`) IS the four-map byte-unchanged
> assertion; the e2e rows above assert the **observable** consequence (no residue leaks
> into the live session surface). Both are required: unit for the structural invariant,
> e2e for the user-visible floor. The unit row is named in A.8.

### A.5 — CF.2 containment (e2e) — the hard ship-gate

A 0432-shaped reachable module (multi-clause `defn` + unannotated self-call tripping the
monomorphiser) → logged per-module index-skip, **no worker/REPL crash, no `.meta` written
for the failed module**. (`agent.md §25.4`, R2-b.)

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `search_cf2_unindexable_module_skipped_no_crash` | e2e | a 0432-shaped reachable module → REPL stays alive, `/search` over the rest still returns results, a search-quality note renders | §25.4 / §25.8(4) | P | RED-first |
| `search_cf2_neg_no_killed_worker_no_meta` | e2e | NEG: the failed module produces **no `.meta`** and does **not** kill the nice worker (subsequent `/search` of other modules still succeeds — capacity intact) | §25.4 / §25.8(4) | N | RED-first |

### A.6 — `/search` query e2e (name + scheme, exact + partial) over lib-path ∪ project-root

Result row has four facets (`repl/spec.md §17.19.2`): name, `:Type` signature, originating
module, the exact `(import …)` form. `/search` is a default-build `ReplCommand` (R9a/R12).

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `search_by_name_exact_returns_four_facets` | e2e | `/search <name>` exact → row shows name + `:Type` sig + module + `(import …)` form | §25.6 / §17.19.2 | P | RED-first |
| `search_by_name_partial_substring` | e2e | `/search <fragment>` → case-insensitive substring matches over the bare name | §25.7 (Index A) | P | RED-first |
| `search_by_scheme_exact` | e2e | `/search (Fn [Int] Bool)` exact-shape → the alpha-equivalent symbol(s) | §25.7 (Index B, `_exact`) | P | RED-first |
| `search_by_scheme_partial_contains` | e2e | `/search (Vec Int)` → candidates whose scheme structurally-contains it | §25.7 (Index B, `_partial`) | P | RED-first |
| `search_spans_lib_path_and_project_root` | e2e | a symbol in a lib-dir AND a symbol in the project root both surface (union reachability) | §25.1 / R10 | P | RED-first |
| `search_neg_no_match_self_documenting_note` | e2e | empty/no-match → a "no importable symbols matched" note, NEVER an opaque error | §25.6 (self-documenting) | N | RED-first |
| `search_neg_already_imported_not_relisted` | e2e | a symbol already in scope is NOT re-offered as importable (reachable-but-not-yet-imported only) | §11 (reachable not resident) | N | RED-first |

### A.7 — Partial-result path + index→import cache-hit (e2e)

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `search_partial_results_during_indexing` | e2e | the burn-down arms **eagerly at REPL start-up** (NOT on first `/search`); a `/search` issued before it finishes still catches it mid-flight → serves partial results + an "indexing N modules…" note | §25.5 (eager-from-startup, REPL mode) / §17.19 | P | RED-first |
| `search_burndown_arms_at_repl_startup_neg_not_on_first_search` | e2e | NEG: in REPL mode indexing begins **at start-up**, NOT gated on first `/search` or agent activation — the first `/search` is served against an already-in-progress/complete index, never the event that arms it | §25.5 (eager-from-startup) | N | RED-first |
| `search_neg_batch_mode_inert_no_index_no_meta_writes` | e2e | NEG (REPL-only invariant): a `--run`/`--link` invocation over a tree with reachable-but-unimported modules produces **NO search index and NO index-driven `.meta` writes** — the indexer never arms outside REPL mode | §25.5 (REPL-only trigger) / §25.8 default-build-stable invariant | N | RED-first |
| `search_index_to_import_is_meta_cache_hit` | e2e | a symbol found via `/search` then `(import …)`'d is a `.meta` **cache-hit** — NO re-typecheck on the live import path (`MODULE_TRACE` shows cache-hit, not typecheck) | R13 / §25.5 / §25.8(3) | P | RED-first |
| `search_index_rebuild_from_meta_reproduces_results` | e2e | clearing the in-memory indices + re-scanning `.meta` reproduces the same `/search` results — no `CACHE_SCHEMA_VERSION` bump | R16 / §25.8(5) | floor (P) | RED-first |

### A.9 — Nice-worker flush / shutdown lifecycle guards (e2e) — R18

Per the nice-worker flush handling added this review (R18): the eager index burn-down must
abandon cleanly on shutdown without corrupting the cache, and must never be part of a
correctness-gating flush. Trace: R18 (nice-worker flush handling), `agent.md §25.1`
(separate `IndexModule` worklist, no `.o`-lifecycle entanglement).

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `search_shutdown_mid_burndown_neg_no_corrupt_meta` | e2e | a REPL session shut down while the eager burn-down is in flight leaves **no corrupt `.meta`** (abandon-on-shutdown; `.meta` writes are atomic — a half-written module produces no `.meta`, not a truncated one) | R18 / §25.1 | N | RED-first |
| `search_next_session_rebuilds_index_cleanly_after_interrupt` | e2e | the **next** REPL session after a shutdown-interrupted burn-down rebuilds the index cleanly and `/search` returns correct results (no stale/partial index poisons the new session) | R18 / R16 | P | RED-first |
| `flush_neg_does_not_block_on_index_work` | e2e | a flush / `--link` path drains **object codegen only** and does NOT block on index work — the `IndexModule` worklist is never part of a correctness-gating flush (a `--link` over a tree with reachable-but-unindexed modules completes without waiting on the indexer) | R18 / §25.1 (separate worklist) | N | RED-first |

### A.8 — `/dev`-owned unit floors (named for surface completeness; NOT `/qa`-authored)

| Test name | Tier | Asserts | Trace | P/N |
|---|---|---|---|---|
| `index_burndown_four_sharedstate_maps_byte_unchanged` | unit (`src/`) | the four `SharedState` maps unchanged after burn-down (the design's literal +neg mirror) | R13 / §25.8(2) | N |
| `index_branch_c_catch_unwind_converts_to_skip` | unit (`src/`) | branch-(c) unwind → logged skip, worker continues | §25.4 | P+N |

---

## Thread B — qualified-name conformance (D-qual fix + 0434 sweep)

### B.1 — Existing D-qual repros flip green (e2e; `tests/spec_07_traits.rs`)

These two are the **2 known reds** in the S90-close baseline; the D-qual-impl-target fix
flips them green. They already exist — this row tracks the transition.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `impl_qualified_primitive_type_target_resolves_to_canonical` | e2e | `(impl Num2 primitives/Int …)` resolves to canonical `Int` → `:a 7`; NEG: no `user/primitives/Int` phantom | §7.3.1 + §8.5 | P+N | RED→green this sprint |
| `impl_qualified_user_type_target_resolves_to_canonical` | e2e | `(impl Tagger user/Widget …)` resolves to canonical `user/Widget` → `99`; NEG: no `user/user/Widget` | §7.3.1 + §8.5 | P+N | RED→green this sprint |
| `impl_bare_type_target_dispatches_control` | e2e | existing bare-target green control (pins the fix target) | §7.3.1 | P | floor |

### B.2 — 0434 sweep: qualified-AND-bare pairs for every REPL-displayed-qualified name-position

Each pair asserts interchangeability (qualified ≡ bare) or documents intended divergence.
New e2e file or extensions to `spec_03_types.rs` / `spec_06_pattern_matching.rs` /
`spec_08_modules.rs`. All `PreludeVariant::PrimitivesOnly` (free-standing). Trace: FIXME
0434, `§7.3.1`/`§8.5`.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `annotation_qualified_type_equals_bare_typecheck` | e2e | `:primitives/Int x` ≡ `:Int x` (type annotation position) — both pin the same type, same result | §8.5 / §3.x annotation | P | RED-first (likely) |
| `annotation_qualified_type_neg_no_reroot` | e2e | NEG: `:primitives/Int` does NOT re-root to `user/primitives/Int` (no phantom in any diagnostic) | §8.5 | N | RED-first (likely) |
| `deftype_field_qualified_type_ref_equals_bare` | e2e | `(deftype Box [:primitives/Int v])` ≡ `(deftype Box [:Int v])` (deftype type-ref) | §5.2 / §8.5 | P | RED-first (likely) |
| `deftrait_method_qualified_type_ref_equals_bare` | e2e | a `deftrait` method sig using `primitives/Int` ≡ bare `Int` | §7.x / §8.5 | P | RED-first (likely) |
| `match_qualified_constructor_pattern_equals_bare` | e2e | `(match v [(option/Some x) …])` ≡ `(match v [(Some x) …])` (qualified ctor pattern) | §6.2 / §8.5 | P | RED-first (likely) |
| `match_qualified_constructor_neg_no_reroot` | e2e | NEG: a qualified ctor pattern does NOT re-root the type name | §6.2 / §8.5 | N | RED-first (likely) |
| `import_qualified_target_resolves` | e2e | an `(import …)`/`(mod …)` target path resolves to the canonical module (no double-rooting) | §8.3 / §8.5 | P | RED-first (likely) |

> **Posture note:** the sweep is a **proactive coverage class** (FIXME 0434) — the
> D-qual-impl-target fix is at the impl-target seam; whether the *other* name-positions
> already canonicalise correctly is UNKNOWN until the tests run. Each row is authored
> RED-first; any that pass green-on-HEAD become floors (the position already canonicalises
> correctly — the sweep then PROVES it, closing the blind spot). Any that go RED surface a
> NEW D-qual-shaped defect at that position → handed to `/frontend` with the repro as the
> brief. The "(likely)" tag flags expected-RED; the run determines truth.

### B.3 — Spec-side annotation (coordination, not a test)

After the sweep is green, `/spec` promotes `spec/07-traits.md §7.3.1` to `[Tested+Neg]`
(coordinate; `/qa` confirms the P+N pairs green first). Record sweep result in
`tests/plan/ledger.md`.

---

## Thread C — FIXME burn-down

### C.0416 — bitwise integer intrinsics (e2e; new `tests/spec_appendix_a_bitwise.rs`)

Each primitive positive + edge. Spec: appendix-a §A.3 (rows landed). `PrimitivesOnly`
(prims are in the synthetic `primitives` module). Unit-tier codegen lowering is
`/dev`-authored in `cranelisp-backend`.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `bit_and_basic_and_edge` | e2e | `(bit-and 0b1100 0b1010)` = 8; AND with 0 = 0; AND with -1 (all bits) = identity | §A.3 `bit-and` | P | RED-first |
| `bit_or_basic_and_edge` | e2e | `(bit-or 0b1100 0b1010)` = 14; OR with 0 = identity; OR with -1 = -1 | §A.3 `bit-or` | P | RED-first |
| `bit_xor_basic_and_edge` | e2e | `(bit-xor 0b1100 0b1010)` = 6; XOR self = 0; XOR -1 = bit-not | §A.3 `bit-xor` | P | RED-first |
| `bit_not_full_width_twos_complement` | e2e | `(bit-not 0)` = -1; `(bit-not x)` = `(- (- x) 1)`; full-64-bit complement | §A.3 `bit-not` + "Int width" | P | RED-first |
| `shl_zero_fill_and_sign_bit` | e2e | `(shl 1 3)` = 8; left-shift into the sign bit produces a negative value (bit 63) | §A.3 `shl` + "Shift count" | P | RED-first |
| `shr_arithmetic_signed_int` | e2e | `(shr -8 1)` = -4 (**arithmetic**, sign replicated; CLIF `sshr`); `(shr 8 1)` = 4 | §A.3 `shr` "right-shift semantics" | P | RED-first |
| `shift_count_mod_64` | e2e | shift amount taken **modulo 64** (`(shl 1 64)` ≡ `(shl 1 0)`) | §A.3 "Shift count" | P | RED-first |
| `popcount_basic_and_full_width` | e2e | `(popcount 0)` = 0; `(popcount -1)` = 64; `(popcount 0b1011)` = 3 | §A.3 `popcount` | P | RED-first |
| `bitwise_run_through_all_modes` | e2e | a bitwise expr is mode-equivalent across REPL/`--run`/`--link` (`run_through_all_modes`) | §A.3 (inline prim) | floor (P) | RED-first |

### C.0365 — `Type.member` field accessors + impl-time collision (e2e; `tests/spec_05_definitions.rs`)

Positive: `Box.v`/`Cup.v` disambiguate a poisoned duplicate field. `_neg` (R3): a trait
`impl` whose method name collides with the target type's field accessor is REJECTED at
impl time. Spec: §8.5.2 (field accessors), §5.2.6, §7.3.1 (impl-time collision).

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `type_member_field_accessor_disambiguates_poisoned_field` | e2e | with `(deftype Box [:Int v])` + `(deftype Cup [:Int v])` (bare `v` poisoned), `(Box.v (Box 5))` = 5 and `(Cup.v (Cup 9))` = 9 | §8.5.2 + §5.2.6 | P | RED-first |
| `type_member_accessor_typed_fn_of_type` | e2e | `Box.v` is first-class — typed `(Fn [Box] Int)`, may be bound/passed; `/sig Box.v` shows the accessor scheme | §8.5.2 | P | RED-first |
| `impl_method_colliding_with_field_accessor_rejected_neg` | e2e | `(impl SomeTrait Box (defn v [x] …))` is a **compile-time error** naming the collision + both sites; the program does NOT run | §7.3.1 (R3 impl-time collision) | N | RED-first |
| `accessor_cross_type_duplicate_field_name` | e2e | existing poisoned-bare-`v` ambiguity guard still holds (bare poison preserved; dotted form is the escape) | §5.2.6 + §8.6.5 | P+N | floor |

### C.0410 — `Cranelisp.toml` scaffold + additive resolution (e2e; `tests/cache.rs` or new `tests/project_config.rs`)

REPL pointed at a bare project root scaffolds a `Cranelisp.toml`; additive resolution is
**unchanged** by the scaffold; never-overwrite; the scaffold carries current
`CRANELISP_LIB` paths commented-out; search order CLI→env→toml→stdlib. Spec: §8.11.4/§8.11.5
(additive union ruling). `/dev`-authored unit tier in `src/session_setup.rs`.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `scaffold_creates_toml_on_bare_project_root` | e2e | REPL launched at a project-root dir (§0.5 rule 3) lacking `Cranelisp.toml` creates one + a `[created Cranelisp.toml]` notice | FIXME 0410 / §0.5 | P | RED-first |
| `scaffold_neg_never_overwrites_existing` | e2e | an existing `Cranelisp.toml` is NEVER overwritten (idempotent) | FIXME 0410 | N | RED-first |
| `scaffold_neg_not_created_on_bare_cwd_repl` | e2e | the no-arg `cranelisp` cwd-default launch does NOT litter `Cranelisp.toml` | FIXME 0410 (trigger scope) | N | RED-first |
| `scaffold_resolution_unchanged_prelude_still_loads` | e2e | after scaffolding, prelude/stdlib still resolve (additive union — the scaffold ADDS nothing that suppresses lower tiers) | §8.11.4 (additive) | P | RED-first |
| `scaffold_carries_commented_lib_paths` | e2e | the generated file carries the current `CRANELISP_LIB` paths as a **commented-out** example (teaches the schema, adds nothing active) | FIXME 0410 / §8.11.4 | P | RED-first |
| `lib_dir_search_order_cli_env_toml_stdlib` | e2e | first-match resolution precedence: CLI flag > `CRANELISP_LIB` env > toml `lib-dirs` > `{root}/stdlib/` | §8.11.4 (search order ruling) | P | RED-first |
| `lib_dir_union_neg_empty_toml_does_not_suppress` | e2e | NEG: an empty/absent `lib-dirs` (or `lib-dirs = []`) does NOT suppress the `{root}/stdlib/` tier (the dissolved footgun — additive union) | §8.11.4 | N | RED-first |

### C.0423 — regen / `(mod …)` extraction writes to lib-dir, not cwd (e2e; `tests/regression.rs`)

The repro + the fix assertion. Run the binary with CWD = a fresh tmpdir ≠ the lib-dir,
exercise a `(mod …)` module, assert no stray backing files appear outside the lib-dir.
Trace: FIXME 0423, §8.2.5. `/dev`-authored unit tier in `src/` regen path.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `regen_mod_extraction_writes_to_lib_dir` | e2e | a `(mod …)` body's backing file is written next to its parent module (lib-dir), independent of CWD | FIXME 0423 / §8.2.5 | P | RED-first |
| `regen_mod_extraction_neg_no_cwd_relative_cruft` | e2e | NEG (the repro): CWD ≠ lib-dir → **no** stray `./<module>/…/test.cl` trees appear at CWD | FIXME 0423 | N | RED-first |
| `regen_annotation_spacing_no_space_after_colon` | e2e | secondary: regen emits `:Type` (no space), not `: Type` (reader-macro binds following form) | FIXME 0423 secondary | N | RED-first |

### C.0431 — give-up e2e for corrected Phase-6 turn-end semantics (e2e; `tests/agent.rs`)

The existing `agent_build_cap_exhausted_give_up_stays_wire_valid` was already corrected
in-place by `/dev` (asserts the give-up line is ABSENT when the turn ends on a `done:`
answer). `/qa`'s addition: a NEW fixture whose script ends WITHOUT a terminal `done:` so
the turn exhausts the budget with no answer → the give-up line renders **exactly once**.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `agent_build_cap_exhausted_give_up_stays_wire_valid` | e2e | (existing) turn ENDS on a `done:` → give-up line ABSENT, model answer renders | FIXME 0431 / §17.14.4 | P+N | floor (already green) |
| `agent_turn_produces_nothing_shows_give_up_once` | e2e | NEW: script ends WITHOUT `done:` (budget exhausted, no answer) → the give-up line renders **exactly once**; committed NOTHING | FIXME 0431 / §16.4 | P | RED-first (new fixture) |
| `agent_turn_give_up_neg_not_per_failed_submit` | e2e | NEG: the give-up line does NOT print per-failed-submit mid-turn (the live defect) | FIXME 0431 | N | floor |

> Unit-tier arms already landed with the fix (`src/agent/mod.rs::
> give_up_line_not_shown_when_turn_ultimately_submits`,
> `::give_up_line_shown_once_when_turn_produces_nothing`).

### C.0432 Face A — repro-check (e2e; `tests/spec_05_definitions.rs` or `tests/regression.rs`)

Author the narrow repro that determines whether the annotated→codegen variant reproduces
on HEAD. The result decides disposition: **RED → retarget to `/backend`** (carry as a
known-red guard); **green → document the non-repro** and close the FIXME with the
repro-pass record. (Face B closed S90.) Trace: FIXME 0432 Face A, §5.1.2.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `defn_multi_clause_annotated_self_call` | e2e | the annotated multi-clause self-call `(defn sum-to ([:Int n] (sum-to n 0)) ([:Int n :Int acc] …))` compiles and `(sum-to 5)` = 15 (the in-body self-call lowers to the dispatched mangled variant symbol) | §5.1.2 / FIXME 0432-A | P | **repro-check** (RED → `/backend` retarget; green → close FIXME) |
| `defn_multi_clause_arity` | e2e | existing positive (multi-clause defn, no self-call) still passes | §5.1.2 | P | floor |

> **Disposition rule:** this row is the cross-skill-handoff minimal repro
> (`CLAUDE.md §"Cross-skill defect handoff requires minimal repro"`). If RED, it is
> committed failing-not-ignored with a `// FIXME(/backend)` brief; if green, the
> repro-pass is recorded in `tests/plan/ledger.md` and FIXME 0432 closes. NOT a committed
> backend fix this sprint.

### C.0433 — literal-pattern reconciliation (spec-internal; NO test change expected)

`/spec` reconciled §4.8.4/§2.5.2 to §6.2/§6.6.2 (literal patterns are NOT a feature). This
is spec-internal — **no compiler work, likely no test change**. `/qa` confirms the existing
`[Tested]` §6.6.2 no-literal-patterns guard still holds.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `pattern_int_match_with_wildcard` | e2e | existing §6.6.2 guard: a literal in pattern position is rejected; Int dispatch uses wildcard/variable + `if`/`case` | §6.6.2 | P | floor (confirm holds) |

> **Resolution:** likely no new test. If the reconciled §4.8.4 example introduces a new
> verified-compiling form worth pinning, `/qa` adds one positive row; otherwise this is a
> documentation-only close (confirm-floor-holds).

---

## Roll-up

| Thread | RED-first guards (e2e) | floors (e2e) | `/dev` unit suites named | Keystone |
|---|---|---|---|---|
| A — Pillar 3 | ~23 e2e (+2 trigger-model `_neg`: not-on-first-search, batch-mode-inert; +3 R18 flush/shutdown lifecycle) | 2 | `_exact` (11) + `_partial` (7) + 2 src/ unit | A.4 no-SharedState-residue `_neg` (reworded R13) + A.5 CF.2 ship-gate |
| B — qual conformance | ~7 sweep e2e | 3 (2 reds→green + 1 control) | `/dev` impl-target unit seam | B.2 0434 sweep |
| C — burn-down | ~24 e2e | 5 | backend lowering (0416), src/ regen (0423), session_setup (0410) | C.0432-A repro-check (disposition fork) |

**Phase-5 Stage-1 authoring order (QA-first):** A.1/A.2 predicate units gate Thread A
e2e; B.1 transitions ride the `/frontend` fix; C threads are independent. The two known
S90-close reds (B.1) flip green with the D-qual fix; the 14 S81 known-defect guards are
untouched by this plan unless 0432-A / 0434-sweep surface within them.

**Discipline reminders:** failing-not-ignored (`memory/feedback_failing_not_ignored.md`);
every `/dev` fix lands with a mandatory unit test (`tests/CLAUDE.md §Unit-test-per-fix`);
free-standing tests (zero stdlib); `// spec:` annotation on every `#[test]`; row in
`tests/plan/ledger.md` at authoring time. A genuine regression is any RED beyond these
named guards + the 14 S81 guards.

---

## Phase-5 Stage-1 LANDED (Wave 0, QA-first) — `/qa`, 2026-06-25

**Entry baseline confirmed (default lane):** `cargo nextest run` = **1548 tests, 1546
passed, 2 failed** — exactly the 2 known D-qual reds (`spec_07_traits::impl_qualified_
{primitive,user}_type_target_resolves_to_canonical`). The "14 S81 guards" are in the
`--features agent` lane, untouched by this wave. The default lane is otherwise clean.

**After Wave 0 (default lane):** **1597 tests, 1562 passed, 35 failed** = **33 NEW
intentional reds** + the 2 pre-existing D-qual reds. Plus **1 new RED in the `--features
agent` lane** (the 0431 give-up fixture). **All 34 new reds FAIL at runtime — NONE
errors-on-compile** (both lanes pass `cargo nextest run --no-run`). Spec-link linter clean
on all touched files.

### Landed-RED e2e (this wave's deliverable)

| File | Tests | Posture / disposition |
|---|---|---|
| `tests/spec_appendix_a_bitwise.rs` (NEW) | 9 RED — `bit_and/or/xor/not`, `shl`, `shr`(arith), `shift_count_mod_64`, `popcount`, `bitwise_run_through_all_modes` | flips green when **Wave 4** lands the 0416 primitive rows + 1:1 CLIF lowering |
| `tests/project_config.rs` (NEW) | 5 RED — `scaffold_creates_toml_on_bare_project_root`, `scaffold_neg_never_overwrites_existing`(**green floor**), `scaffold_neg_not_created_on_bare_cwd_repl`(**green floor**), `scaffold_resolution_unchanged_lib_still_loads`, `scaffold_carries_commented_lib_paths`, `lib_dir_search_order_cli_env_toml_stdlib`, `lib_dir_union_neg_empty_toml_does_not_suppress` | scaffold rows flip green at **Wave 6** (`scaffold_project_config`); the two `_neg` rows are GREEN-today floors (no scaffold exists, so they hold) |
| `tests/search.rs` (NEW, Pillar 3) | 14 RED across A.3/A.4/A.5/A.6/A.7/A.9 — `/search` query (name/scheme × exact/partial), lib∪root span, no-match note, already-imported-not-relisted, branch-(c) `.meta`-no-`.o`, no-SharedState-residue observable `_neg`×2, CF.2 ×2, eager-from-startup `_neg`, batch-mode-inert `_neg`, cache-hit-on-import, index-rebuild floor, shutdown-no-corrupt-meta `_neg`, next-session-rebuild, flush-no-block `_neg` | flips green at **Wave 5** (`/search` + indexer + CF.2). Default-build lane (NOT agent-gated, per R9a/R12) |
| `tests/spec_05_definitions.rs` (+4) | `defn_multi_clause_annotated_self_call` (0432-A repro-check), `type_member_field_accessor_disambiguates_poisoned_field`, `type_member_accessor_typed_fn_of_type`, `impl_method_colliding_with_field_accessor_rejected_neg` | 0365 rows flip green at **Waves 1+3** (frontend transport + typecheck typing/collision); 0432-A is the **repro-check** — RED → confirms a real annotated-self-call codegen defect → **Wave 7** retarget `/backend` |
| `tests/spec_08_modules.rs` (+1) | `regen_annotation_spacing_no_space_after_colon` (0423 secondary) | the 0423 primary lib-dir-relative repro (`inline_mod_test_extraction_writes_lib_dir_relative_not_cwd`) ALREADY EXISTED; this adds the `:Type`-no-space secondary; both flip green at **Wave 6** |
| `tests/agent.rs` (+1, `#[cfg(feature="agent")]`) | `agent_turn_produces_nothing_shows_give_up_once` (0431 new fixture) | RED in the agent lane (give-up notice not yet rendered at no-answer turn-end); flips green when /dev's §17.14.4 turn-end give-up decision lands |

### Thread B 0434 sweep — RESULT (the proactive coverage class verdict)

`tests/spec_qualified_name_sweep.rs` (NEW, 7 rows): **6 GREEN-on-HEAD floors + 1 fresh
RED defect.** The sweep PROVED most REPL-qualified name-positions already canonicalise
correctly — closing the blind spot — and surfaced ONE new D-qual-shaped defect:

- **GREEN floors** (position already canonicalises; the sweep now guards it): `annotation_qualified_type_equals_bare_typecheck`, `annotation_qualified_type_neg_no_reroot`, `deftype_field_qualified_type_ref_equals_bare`, `match_qualified_constructor_pattern_equals_bare`, `match_qualified_constructor_neg_no_reroot`, `import_qualified_target_resolves`.
- **RED (fresh defect → `/frontend`):** `deftrait_method_qualified_type_ref_equals_bare` — a `deftrait` method signature using a qualified type `:primitives/Int` fails with `type error: unknown type: primitives/Int`, while the bare `:Int` works. This is a D-qual-shaped defect at the **deftrait-method-type-ref resolution seam** (distinct from the impl-target seam the 2 known reds cover). **Handoff brief for `/frontend`:** the qualified type-ref in deftrait-method-signature position is not routed through the §8.5 canonical splitter (the same class as the impl-target `type_ref_from_name` fix — likely a sibling site in `ast_builder.rs` that hand-rolls a `TypeRef` for deftrait method param/return types). Minimal repro is the named test. Fix candidate: Wave 1/2 (same frontend resolution pass as the impl-target/trait-name splits).

### Deferred to `/dev` unit-tier (NOT authored here — would break the test binary)

Per the wave boundary, the following named unit suites are `/dev`'s, authored alongside
the impl in their crate (`#[cfg(test)]`); a `/qa` reference to a not-yet-existing `fn`
would break compilation of the whole test binary:

- **A.1 `signature_matches_exact`** (11 rows) + **A.2 `signature_matches_partial`** (7 rows) — `cranelisp-typecheck`, Wave 3 (the two additive `public-api.txt` predicate lines).
- **A.8** `index_burndown_four_sharedstate_maps_byte_unchanged` + `index_branch_c_catch_unwind_converts_to_skip` — `src/`, Wave 5 (the SharedState four-map +neg mirror + CF.2 unit; the e2e here assert the observable consequence).
- 0416 codegen lowering unit tests (`cranelisp-backend`, Wave 4); 0410 `assemble_lib_dirs`/`scaffold_project_config` unit (Wave 6); 0365 frontend transport-invariance + typecheck accessor-typing/collision units (Waves 1/3).

### Notes for `/sprint`

- The pre-existing 0423 primary repro (`spec_08_modules::inline_mod_test_extraction_
  writes_lib_dir_relative_not_cwd`) and the existing 0432 Face-B convergence guards were
  NOT re-authored (already present, correct). 0432-A is the NEW Face-A repro-check.
- 0433 (literal-pattern) is spec-internal — the existing `spec_06_pattern_matching::
  pattern_int_match_with_wildcard` §6.6.2 floor still holds (confirmed green); no new test.
- The existing `spec_platforms::cranelisp_toml_takes_precedence_over_cranelisp_lib_env`
  test asserts the OLD precedence (config-tier wins over env). The S91 §8.11.4 ruling
  REVERSES this (env BEFORE config). That test is GREEN today (old behaviour) but the
  Wave-6 additive `assemble_lib_dirs` will make it RED. **`/qa` flag:** when Wave 6 lands,
  that existing test must be re-aligned to the S91 search order (env > toml) — it is an
  existing floor that the spec ruling supersedes, not a regression. The NEW
  `lib_dir_search_order_cli_env_toml_stdlib` already pins the CORRECT S91 order.

### Addendum (2026-06-26) — 0365 INVERTED-model guards (`/qa`, post-`/dev`-inversion)

The 0365 field-accessor model was **inverted** mid-sprint (design of record:
`design/typecheck/fixme-0365-field-accessor-dotted.md §1.6`): `Type.field` (`Box.v`) is the
**canonical, uniformly-Public** accessor (one compiled function per (type, field)); bare
`field` is a **convenience alias** (an `Import` edge to the canonical key); **ambiguity lives
in the bare alias**. `/dev` landed the inverted impl green. `/qa` added GREEN regression
guards in a new file `tests/spec_field_accessor.rs` (7 tests), tracing §5.2.6 / §8.5.2
(reframed) / §8.6.5 + the §1.6.6 `/qa`-guard spec:

- **Cross-module no-cliff (load-bearing):** `cross_module_canonical_accessor_resolves`
  (`shapes/Box.v` cross-module → 7), `cross_module_contested_canonical_accessors_no_cliff`
  (`shapes/Box.v` AND `shapes/Cup.v` BOTH resolve cross-module in the contested case → 14 —
  the regression guard proving the inversion; would have FAILED under the retired
  non-Public-on-contest design), `cross_module_contested_bare_accessor_rejected_neg`
  (contested bare `shapes/v` does NOT silently dispatch — asserts the BEHAVIOURAL outcome,
  exit≠5, not the message; the diagnostic on that path is currently the module-resolution
  error, a separate diagnostic-quality gap noted in-test).
- **Bare alias:** `bare_alias_resolves_when_field_unique` (single type → bare `v` → 5),
  `bare_alias_ambiguous_canonical_both_work` (contested bare `v` errors-ambiguous while
  `Box.v`/`Cup.v` both still work → 5 and 9).
- **`/list` shows canonical qualified accessor:** `list_shows_canonical_qualified_accessor`
  asserts `Box.v` appears; a `// FIXME(0438)` note marks where the bare-`v`-present/absent
  assertion goes once `/repl` resolves 0438 (option A "canonical only" vs B "annotate alias")
  — NOT asserted yet, per the open `/repl` call.
- **One compiled function per (type,field) — e2e behaviour-equivalence:**
  `bare_alias_and_canonical_dispatch_equivalently` (both forms → 42; the `/dev` unit-tier owns
  the no-duplicate-GOT-slot assertion).

**Before/after (default lane):** before this addendum **1597 tests / 35 failed**; **after
1604 tests / 1575 passed / 29 failed.** The 7 new guards are GREEN (0 in the fail list). The
fail-count drop (35→29) is the inverted 0365 impl + the D-qual frontend fix flipping SIX prior
Wave-0 reds green between waves (the 3 spec_05 0365 rows, the 2 spec_07 D-qual reds, the
`deftrait_method_qualified_type_ref_equals_bare` sweep red). The remaining 29 reds are exactly
the other-wave RED-first guards (search ×14, bitwise ×9, project_config ×5, 0432-A ×1) —
**no regressions.**

### Addendum (2026-06-26, later) — Wave-4 bitwise close: `main`-shape fix (`/qa`)

Wave-4 (`/dev` 0416) landed the bitwise lowering — 8 of the 9 `spec_appendix_a_bitwise`
reds flipped GREEN. The 9th, `bitwise_run_through_all_modes`, was RED for a **test-authoring**
reason (NOT a lowering bug): its `(defn main [] (bit-or …))` returned a bare `Int`, but
`--run`/`--link` require `main : (Fn [] (IO _))` (the REPL permutations already observed `8`
correctly; the `--run`/`--link` permutations type-errored on the `main` shape). Fixed by
wrapping the result in `(Pure …)` — the same `main` shape `build_confidence.rs::
mode_equiv_primitive_arithmetic` uses; the `assert_all_equal(8)` target is unchanged. All 9
`spec_appendix_a_bitwise` are now GREEN.

Also **deleted the redundant FIXME** `design/arch/fixmes/0439-bitwise-all-modes-main-shape.md`
(filed `target: /qa` by `/dev` for this test): per `memory/feedback_no_fixme_with_failing_test`,
a defect with a failing-not-ignored repro does NOT also need a numbered FIXME — the failing
test was the record; the fix resolves it, nothing to track. (Deletion is the `/qa`-resolution
action for a FIXME targeting `/qa`, the one file-ownership exception.)

**Before/after (default lane):** before **1604 tests / 1583 passed / 21 failed** (bitwise ×9
included 1 red); **after 1604 tests / 1584 passed / 20 failed** — the fail count dropped by
exactly 1. The remaining 20 reds are ONLY the future-wave RED-first guards: **search ×14
(W5), project_config ×5 (W6), 0432-A ×1 (W7)** — no regressions.

### Addendum (2026-06-26, Wave-5 close) — `/search` four-facet needle reconcile (`/qa`)

Wave-5 (`/dev` Pillar-3 `/search`) landed — 20 of the 21 `tests/search.rs` reds flipped
GREEN. The 21st, `search_by_name_exact_returns_four_facets`, was RED for a **test-authoring**
reason (NOT an impl gap): its needle `:primitives/Int` asserted a colon-per-leaf rendering
**stricter than `repl/spec.md §17.19.2`'s own example.** Verified independently against the
binary: `/search gcd2` renders `:(Fn [primitives/Int primitives/Int] primitives/Int) gcd2 …
in mathx — (import [mathx [gcd2]])` — the `:Type` colon prefixes the WHOLE `(Fn …)` form,
with FQ leaf names (`primitives/Int`) inside it, exactly as §17.19.2 shows (`grid-get ::
(Fn [primitives/Int primitives/Int] primitives/Int)`) and matching `/sig`/`/list`. The impl
IS §17.19.2-faithful and all four facets are present — so this was a needle relax, not a
`/dev` route-back. Reconciled the needle to assert the four facets as actually rendered:
`gcd2` + the full `(Fn [primitives/Int primitives/Int] primitives/Int)` signature (FQ leaves,
single `:Type`) + `mathx` + `(import [mathx [gcd2]])` — all four still asserted, no weakening
to vacuity.

Also **deleted the redundant FIXME** `design/arch/fixmes/0439-qa-search-four-facet-needle-
stricter-than-spec.md` (filed `target: /qa` by `/dev`; a second reuse of the 0439 number this
sprint) — the failing test was the record; `memory/feedback_no_fixme_with_failing_test`.

**Before/after — both lanes.** Default: before **1612 / 1605 passed / 7 failed** (search ×1
red) → **after 1612 / 1606 passed / 6 failed** (search ×14 all green). Remaining 6 = future-
wave guards only: project_config ×5 (W6), 0432-A ×1 (W7). Agent lane: **1752 / 1743 passed /
9 failed** = project_config ×5 (W6) + 0432-A ×1 (W7) + 0431 `agent_turn_produces_nothing_
shows_give_up_once` (W6) + the two pre-existing not-mine agent-lane failures
`agent_on_no_provider_is_dormant` and `repl_introspection::mem_baseline_zero_at_process_start`
(env-sensitive; untouched by this work). No regressions in either lane.

### Addendum (2026-06-26, Wave-6 close) — additive lib-dir precedence re-align + 0431 give-up fixture fix (`/qa`)

Wave-6 (`/dev`) landed the additive lib-dir model (spec §8.11.4 settled S91), owing `/qa`
two re-aligns:

1. **Precedence test re-align (superseded floor).** `spec_platforms::cranelisp_toml_takes_
   precedence_over_cranelisp_lib_env` asserted the OLD config > env precedence; it correctly
   went RED when `/dev`'s additive `assemble_lib_dirs` landed. Renamed to
   `cranelisp_lib_env_searched_before_toml_lib_dirs` and rewritten to assert the S91 additive
   model: (1) same-module shadow → the **env** path is searched first and **wins** (exit 13,
   not 99 — env > config, REVERSING the old order) + a `assert_ne!(99)` negative companion;
   (2) **additive union** — a module present ONLY in the config tier still resolves (exit 42),
   proving env does not replace config. Traced `// spec:` §8.11.4. This is the spec ruling
   superseding an existing floor, NOT a regression (flagged in the Wave-0 notes above).

2. **0431 give-up fixture fix (test-authoring, NOT impl gap).** `agent_turn_produces_nothing_
   shows_give_up_once` was RED because its fixture had only **4** broken submits — too few to
   exhaust the turn iteration budget (`MAX_TURN_ITERATIONS=8`, each step's repair loop also
   consuming scripted completions), so the give-up path never fired and the script ran dry.
   Verified the impl IS correct (it produces the give-up-once at true turn-end — proven by the
   impl's own unit guard `give_up_line_shown_once_when_turn_produces_nothing`, which uses 64
   broken submits). Bumped the fixture to 64 broken submits (mirroring the unit guard);
   assertions unchanged (give-up renders exactly once + commits nothing + wire-valid). The
   fixture, not the impl, was the fault — so this was a fixture provision fix, not a `/dev`
   route-back. **Deleted `design/arch/fixmes/0431-qa-give-up-line-turn-end-e2e.md`** (target
   `/qa`; the test is the record; `memory/feedback_no_fixme_with_failing_test`).

**Before/after — both lanes.** Default: before **1621 / 1614 passed / 7 failed** (the 5
project_config W6 reds + the superseded precedence test + 0432-A) → **after 1621 / 1620
passed / 1 failed** — only `defn_multi_clause_annotated_self_call` (0432-A, W7) remains.
Agent lane: before ~9 failed → **after 1761 / 1759 passed / 2 failed** =
`agent_on_no_provider_is_dormant` (pre-existing, not mine) + 0432-A (W7); the 0431 give-up
test is now GREEN. (`mem_baseline_zero_at_process_start` passed this run — genuinely
env-sensitive, not touched.) No regressions in either lane.
