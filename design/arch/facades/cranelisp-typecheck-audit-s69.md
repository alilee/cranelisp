# cranelisp-typecheck — Sprint 69 facade audit (per-item analysis, configuration-grounded re-author)

> **SUPERSEDED IN PART (facade-coherence pass, post-S72).** This is a dated S69 record; its findings text is preserved as the point-in-time audit. Two of its conclusions are since overturned by the canonical facade and must not be read as current: (1) **Findings F-3 / F-4 / F-1's framing treat `register_imports` / `register_exports` as a kept typecheck surface** (free-fn canonical form). They are now **struck from the typecheck surface entirely** — `ParsedEntry` has no `Import`/`Export` variant, so typecheck never receives imports/exports; import/export registration is frontend's StructuralDecl concern. See `facades/typecheck.md` §"Import/export registration is not a typecheck concern". (2) The boundary type **`ClusterContext` is renamed `SymbolTableAccess`** — every `ClusterContext` mention below reads as `SymbolTableAccess` (the `Live` / `Cluster` variant names are unchanged). See `facades/typecheck.md` §"Cluster check scaffolding" naming rationale.

**Audit triple**: `crates/cranelisp-typecheck/src/lib.rs` (declared surface) × `design/arch/facades/typecheck.md` (binding contract) × `crates/cranelisp-typecheck/public-api.txt` (live boundary).

**Date**: 2026-05-19 (S69 Phase 3 Wave 1 — re-author over the 2026-05-19 morning draft)
**Auditor**: /design (cranelisp-typecheck narrow deployment)

**Configuration loaded before disposition** (per `memory/feedback_audit_per_item_analysis.md`):

- `design/arch/principles.md` + every `principles/*.md` (17 — module locality is load-bearing)
- `design/arch/CLAUDE.md` (Decisions index)
- Active Decisions 30, 31, 35, 40, 41, 42, 43, **44** (third amendment, cluster-atomic), **45** (trait-home impl placement), **46** (Wave 3a α/β split), 47 (FQTypeName binding), 48 (primitives module)
- Legacy Decisions 21 (TC-sourced call graph), 22 (defined_symbols), 32 (CodeStore/LinkerStore), 33, 38 (per-symbol mutability), 39 (ErrorLocation)
- `design/arch/bounded-contexts.md` §2 (Typecheck BC + Module-locality invariant restated)
- `design/typecheck/typecheck.md` (per-crate master design; flagged subordinate-doc staleness)
- `design/arch/sequences/exec-flow-compilation.mmd`, `exec-flow-repl.mmd`, `concurrency-symbol-table-entry.mmd`
- FIXMEs 0172 (short-name fallback chains; deferred-with-named-residue), 0173 (CheckPass/Accumulator removal; partially-superseded), 0177 (cross-form state regression; open), 0179 (cluster read-union staging; open), 0187 (int consumer migration; open)

**Discipline.** Per `feedback_audit_per_item_analysis.md`: each finding gets a five-block analysis (facade expects / source does / design intent / difference implies / disposition). Default disposition is **source-moves** when the facade is target-stating per Decision/Principle/FIXME. "Facade-moves" applies only when the facade is genuinely stale (retracted Decision, evolved-past source) or sloppy (typo, missing variant). "Arbitration" is reserved for items the configuration does not ground.

This re-author **inverts several dispositions from the prior 2026-05-19 morning draft** which read the facade + lib.rs + pub-api but did not load Principle 17, the BC §2 module-locality invariant, Decision 44's third amendment in detail, or FIXME 0179's staging-aware roadmap. Calibration of each flip is recorded in §10.

---

## 0. Summary up front

cranelisp-typecheck is post-S67-narrowing and structurally close to its facade target — closer than the heaviest crates (types, int). The crate-level free function `check_forms` matches Decision 44's third-amendment canonical statement in parameter count, order, mutability, and return type. `ClusterContext`, `ClusterRead`, `ClusterWrite`, `CheckState`, `CheckResult`, `CheckError`, `ReplSnapshot`, and the `trace::*` surface are all present and broadly facade-aligned. `CheckPass`, `FormCheckResult`, and `ModuleCheckAccumulator` are retired from the public surface per Decision 44 third amendment + FIXME 0173.

What remains is a residue: five `TypeCheckEnv` helper methods still `pub` against a facade target of 2 methods; a textual `SymbolTables<C, L>` shorthand the facade uses that has no source counterpart; one stale `CheckResult` shape (kept pub but never returned from any pub function); a facade prose inconsistency between the `check_forms` parameter spelling and the `register_imports`/`register_exports` parameter spelling.

The Principle 17 violation candidate at `checker.rs:1991` (`known_type_names_in_module`'s Tier 2 universe scan over `self.modules.iter()`) — surfaced and called "load-bearing" by the prior draft — resolves on configuration reading to a **different** disposition: the function is `pub(crate)` (NOT pub), does NOT cross the facade, and the BC's module-locality invariant (BC §2 + Principle 17) applies *internally* to typecheck regardless of facade exposure. The Principle-17 question is real but is **not a facade-audit finding** — the facade audit cannot tell typecheck what to do inside its own crate. It is named here as a non-facade /design (typecheck) follow-on, NOT as an /arch arbitration item.

Disposition class totals (over **15 findings**, F-1 through F-15):

| Class | Count | Meaning |
|---|---|---|
| Source-moves | 8 | Facade is target-stating per Decision/Principle/FIXME; source has leftover surface. |
| Facade-moves | 2 | Facade is internally inconsistent (prose) or under-specifies (textual shorthand). |
| Both-move | 1 | One coordinated change (the `SymbolTables<C, L>` alias materialises in types-crate + facade prose tightens). |
| Source-moves (gated on FIXME 0179) | 2 | The substitute path the facade names is not yet live; source narrowing waits on 0179 activating cluster-mode-on-hot-path. |
| Mechanical-test gap | 1 | Compliance triple cannot detect by construction; /review or doc-test enhancement. |
| Internal /design (typecheck) | 1 | Principle 17 invariant 10 internal compliance — not a facade-boundary finding. |

**No /arch arbitration items.** The prior draft listed three (A1 universe-iteration; A2 snapshot/restore; A3 CheckResult orphan). On configuration reading:
- **A1 (universe-iteration) is internal to typecheck**, not a facade finding — Principle 17 + BC §2.10 already named it as a typecheck-internal invariant; the iteration is `pub(crate)`; it does not cross the facade boundary. The /design (typecheck) master doc tracks the internal locality refactor (Wave 3a-α; FIXME 0179 follow-up). No /arch decision is owed.
- **A2 (snapshot/restore) is FIXME-0179-gated source-moves** — the facade explicitly names the post-0179 replacement (staging-drop); both methods narrow source-side once 0179 activates the cluster-mode hot path; no arbitration needed.
- **A3 (CheckResult orphan) is source-moves** — Decision 44's third amendment retired the per-pass `FormCheckResult`/`ModuleCheckAccumulator` from the public surface; `CheckResult` is the SAME retirement class (per facade §"Types originated here" inline comment and §"#[non_exhaustive] DTOs"). The "where do cluster-level display/warnings flow" question is answered by the facade's own §"Cluster orchestration result" reference (lands on `int`-side `ProcessedCluster` per FIXME 0173 supersession note). The struct is just leftover surface that needs deletion or narrowing.

The prior draft flipped these into /arch arbitrations because it did not have the FIXME 0173 supersession note (which dispositioned `ModuleCheckAccumulator` retirement) or the BC §2.10 invariant (which already settled the locality question) loaded.

---

## 1. Findings

### Finding F-1 — `SymbolTables<C, L>` textual shorthand has no source counterpart

**Facade expects.** §"Free function — cluster check" line 16-20:

```rust
pub fn check_forms<C, L>(
    parsed: Vec<ParsedEntry>,
    ctx: &mut ClusterContext<'_, C, L>,
    symbol_tables: &SymbolTables<C, L>,
) -> Result<(), CheckError>;
```

The shorthand `SymbolTables<C, L>` recurs at §"Cluster check scaffolding" (the `ClusterContext` variant fields, even though source spells them out as `DashMap<…>`), at §"Module-lifecycle free functions" lines 189-201 (the `register_imports`/`register_exports` parameter types — **but those lines actually spell out `&DashMap<ModuleFullPath, SymbolTable<C, L>>` rather than `&SymbolTables<C, L>` — see F-8**), and in Decision 44's third-amendment quoted Statement.

**Source does.** No type named `SymbolTables` exists in `cranelisp-types` or `cranelisp-typecheck`. Pub-api line 179 spells the parameter out: `&dashmap::DashMap<cranelisp_types::newtype::ModuleFullPath, cranelisp_types::module::SymbolTable<C, L>>`. `register_imports` (pub-api 183) and `register_exports` (182) use the same expansion. `ClusterContext::Live` and `ClusterContext::Cluster` variant fields also expand directly (pub-api 53, 57).

**Design intent.** Facade §"Free function — cluster check" treats `SymbolTables<C, L>` as a self-describing shorthand for the modules-map borrow. Decision 44's third-amendment quoted signature uses the same shorthand. No active Decision says "DO NOT introduce a type alias for the modules-map"; the shorthand is editorial convenience that the facade has used consistently since the third amendment. Principle 15 (facade types live with behaviour) endorses naming a boundary type at its primary use site — `cranelisp-types` is where `SymbolTable<C, L>` lives, which makes it the natural home for an outer-map alias. Principle 13 (interfaces.md is auditable) prefers materialised aliases over prose-only shorthand because pub-api projection then names the alias and the facade-compliance test can mechanically check it.

**Difference implies.** Two coupled drifts:
- A reader of `facades/typecheck.md` alone cannot see that the parameter is a DashMap — the shorthand hides the concurrency primitive. (The shorthand is benign for type-shape understanding but blocks the question "why is this a DashMap, what's the lock discipline?" from being answered at the facade.)
- The mechanical compliance test (per `design/arch/CLAUDE.md` §"Baseline-diff discipline") asserts pub-api line equivalence with facade prose. A facade reading `&SymbolTables<C, L>` against a pub-api line reading `&DashMap<ModuleFullPath, SymbolTable<C, L>>` is structurally non-equivalent for grep-based checks.

**Disposition.** **Both-move.** Source: add `pub type SymbolTables<C, L> = DashMap<ModuleFullPath, SymbolTable<C, L>>` in `cranelisp-types` (FIXME `target: /arch` because the type-alias lives in `cranelisp-types`; /design (typecheck) cannot edit types-crate). Once landed, all three typecheck-side public signatures (`check_forms`, `register_imports`, `register_exports`) and the two `ClusterContext` variant fields adopt `&SymbolTables<C, L>` mechanically — /design (typecheck) requests the type alias; /dev (typecheck) absorbs the rename. Facade: no prose change in `facades/typecheck.md` (the shorthand is already in use); facade §"Module-lifecycle free functions" tightens to use `SymbolTables<C, L>` for consistency (per F-8). Decision 44's third-amendment Statement requires no edit — its shorthand becomes accurate.

This closes the prior draft's F-1 (alias materialisation), F-7 (`check_forms` shape drift — the only structural element of the drift was the alias), and the textual side of F-8. They are one drift viewed three ways.

---

### Finding F-2 — `TypeCheckEnv::ensure_module_exists` exposed pub; facade target is `pub(crate)`

**Facade expects.** §"TypeCheckEnv target shape — narrowing target" lines 114-119:

> The facade prescribes exactly **2 methods**: `new` and `next_type_id`. The remaining ~28 methods drop from the public surface during /dev (typecheck) Wave 3 narrowing… **module-table accessors (… `ensure_module_exists`, …) likewise become internal** (cluster-mode access flows through `ClusterContext::current_symbol_table()`; cross-module probes follow the per-symbol shapes in Invariant 10 below).

**Source does.** Pub-api line 164: `pub fn TypeCheckEnv::ensure_module_exists(&self, path: &ModuleFullPath)`. Body at `checker.rs:471` delegates: `cranelisp_types::ensure_module_exists(self.modules, path)`. Int consumers: `session_v4.rs:1247, 2264, 2519, 3162, 3500`; `worker.rs:420, 3840`; `platform.rs:245` — **8 sites**. Plus **2 already-migrated** sites at `session_v4.rs:1327, 1337` that call `cranelisp_types::ensure_module_exists(...)` directly (the types-crate free-fn — per `facades/types.md` §"Module-lifecycle primitives" — is the post-S67 canonical path).

**Design intent.** Decision 44 third amendment (filed 2026-05-13) collapsed `TypeCheckEnv`'s role: typecheck is meant to consume `&mut ClusterContext` for table access, not borrow the whole DashMap directly. The facade narrows `TypeCheckEnv` to 2 methods to enforce this (cluster-mode access through `ClusterContext`, not through `TypeCheckEnv` accessors). FIXME 0187 (filed by /dev (typecheck) at S67 W3) tracks the source-side burden: `int` consumes ~15 helper methods cross-crate, including `ensure_module_exists` at 8 sites. FIXME 0187's "Phase B — bootstrap + cache reconstruction" specifies the migration path: route `int`-side `ensure_module_exists` calls to `cranelisp_types::ensure_module_exists` (the types-facade has the free-fn; `int` reaches `self.shared.symbol_tables` directly without constructing a `TypeCheckEnv`). The 2 already-migrated sites in `session_v4.rs:1327, 1337` are the in-production demonstration.

**Difference implies.** The 8 `tc.ensure_module_exists(...)` sites carry redundant `TypeCheckEnv` construction overhead (the `next_id: &AtomicU32` field is unused for the ensure-only path) but the behaviour is identical to the free-fn form. A reader of `facades/typecheck.md` correctly expects `ensure_module_exists` to be a method-shape consumed only inside the crate; the as-built pub method contradicts the narrowing target.

**Disposition.** **Source-moves (atomic /dev (int) + /dev (typecheck)).** /dev (int) migrates 8 `tc.ensure_module_exists(&path)` sites to `cranelisp_types::ensure_module_exists(&self.shared.symbol_tables, &path)` per FIXME 0187 Phase B. Typecheck then narrows the method to `pub(crate)` (no behavioural change). Sequencing: int-first commit then typecheck-narrow commit, same /dev wave; atomicity is build-state. FIXME 0187 is the binding tracker — no new FIXME needed.

Facade-side: optional one-line cross-reference in §"TypeCheckEnv target shape" pointing readers to `facades/types.md` §"Module-lifecycle primitives" for the post-narrowing path. Bundled with F-1/F-8 facade pass.

---

### Finding F-3 — `TypeCheckEnv::register_imports` method has zero int-side consumers

**Facade expects.** §"TypeCheckEnv target shape" names exactly 2 methods (F-2). §"Module-lifecycle free functions (S67 hack-back — FIXME 0192)" lines 189-194 prescribes the **free-function** form as binding:

```rust
pub fn register_imports<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    next_id: &AtomicU32,
    state: &mut CheckState,
    specs: &[ImportSpec],
) -> Result<(), CranelispError>;
```

Quote: "Free fns that perform module-lifecycle work without requiring a fully-constructed `TypeCheckEnv` borrow. `register_imports` / `register_exports` were lifted off `TypeCheckEnv` in the Sprint 67 hack-back (FIXME 0192) so cross-crate callers (`int`'s import-form handler) do not need to construct a typecheck env." The free-fn IS the post-S67 canonical form; the method form is not mentioned in the facade at all.

**Source does.** Pub-api line 168 — the method form: `pub fn TypeCheckEnv::register_imports(&self, state: &mut CheckState, specs: &[ImportSpec]) -> Result<(), CranelispError>` (`checker.rs:1267`). Pub-api line 183 — the free-fn form: `pub fn cranelisp_typecheck::register_imports<C, L>(symbol_tables, next_id, state, specs) -> Result<…>` (`checker.rs:2088`, delegates to the method at L2099). Both are pub. Int consumer audit (verbatim grep across `src/`): all 6 int-side call sites — `worker.rs:1630, 1656, 2730, 2774`, `session.rs:339` — invoke the **free-fn** form (`cranelisp_typecheck::register_imports(ctx.symbol_tables, ctx.next_type_id, ...)`), NOT the method form. **Zero int-side consumers of the method form.**

**Design intent.** FIXME 0192 (S67 hack-back) lifted these off `TypeCheckEnv` so int could call them without constructing a typecheck env. The facade names only the free-fn form as a result. FIXME 0187's table row "`register_imports` / `register_exports` … Probably stays `pub` as the import/export wiring entry point — facade should be amended to list it" was filed against the wrong assumption — that int consumed the method form. The actual int consumers route through the free-fn. The method form is leftover surface internal to typecheck (the free-fn at L2099 calls `env.register_imports(state, specs)` to share the body).

**Difference implies.** A reader of `facades/typecheck.md` sees the free-fn shape and correctly concludes "this is the import-registration entry." The as-built pub method form is unannounced — a duplicate surface that adds nothing the free-fn does not already cover. FIXME 0187 captures the migration burden assuming int consumers, but the audit grep shows zero such consumers.

**Disposition.** **Source-moves (typecheck unilateral, no int coordination).** /dev (typecheck) narrows `TypeCheckEnv::register_imports` to `pub(crate)` in a single commit; the typecheck-internal callers (the free-fn delegation at L2099, the TypeChecker wrapper at L2395, and three test fixtures in `traits.rs:2124`, `infer.rs:900`, `program.rs:2900`) remain on the method form unchanged because they are inside the crate. No facade text change required; no int-side work. FIXME 0187's table row for `register_imports`/`register_exports` is **stale** and should be removed when that FIXME is updated (out of scope for this audit).

---

### Finding F-4 — `TypeCheckEnv::register_exports` method has zero int-side consumers

**Disposition.** **Source-moves (identical to F-3; bundled).** Pub-api line 167; defined `checker.rs:1332`. Free-fn at `checker.rs:2107`, pub-api 182. Int consumer audit: `worker.rs:2127, 2184` — all invoke the free-fn form. Zero int-side method consumers. Narrow method to `pub(crate)` in the same commit as F-3.

---

### Finding F-5 — `TypeCheckEnv::snapshot` method gated on FIXME 0179

**Facade expects.** §"TypeCheckEnv target shape" lists `snapshot` among methods that become `pub(crate)`. Quote:

> snapshot/restore (`snapshot`, `restore`, `snapshot_type_defs`, `restore_cached_module`, `restore_cached_impls`) is `pub(crate)`-scoped to typecheck-internal callers (REPL eval rollback flows through the orchestrator's staging-drop instead — Decision 44).

The `ReplSnapshot` struct stays public (§"Types originated here" — it is the type-var pool / scope-depth / subst-len carrier consumed by callers); the entry-point methods retract.

**Source does.** Pub-api line 170: `pub fn TypeCheckEnv::snapshot(&self, state: &CheckState) -> ReplSnapshot` (`checker.rs:1903`). Int consumer: `session_v4.rs:1391-1396` — the REPL eval rollback path. `tc.snapshot(cs)` captures pre-eval state; `tc.restore(cs, snapshot)` at line 1400-1405 is paired for failed-eval rollback. Used at `session_v4.rs:2493, 2497` (eval try-and-restore) and `session_v4.rs:3120, 3122`.

**Design intent.** Decision 44's third amendment retired per-form rollback in favour of orchestrator-owned cluster-atomic staging: when a cluster fails, the orchestrator drops the staging table; the live table is byte-identical to its pre-cluster state. `ReplSnapshot` remains as the **type-var pool / substitution-log** rollback primitive (carried in `CheckState`, NOT in the symbol table — see facade §"Post-Gap state contract"); the symbol-table side of rollback is handled by staging-drop and needs no method. FIXME 0179 (filed 2026-05-14) tracks the source-side activation: cluster-mode reads need to union staging-first-then-live before `int::process_cluster` can run multi-form `(begin)` clusters in `ClusterContext::Cluster` mode on the hot path. Until 0179 lands, `check_program_compat` continues to use `ClusterContext::Live` (per `src/CLAUDE.md` §"Status — Sprint 66 Wave 3b-2c.2"), and the REPL eval rollback genuinely needs the snapshot/restore primitive on `TypeCheckEnv` because staging-drop is not yet on the hot path.

**Difference implies.** Pre-0179, the method form is load-bearing — int's REPL eval rollback has no replacement. Post-0179, the method form becomes redundant — staging-drop handles symbol-table rollback; `ReplSnapshot` captures and restores only the `CheckState`-internal pieces (type-var pool, subst-log) for which it remains the appropriate primitive. The substitute path the facade names ("REPL eval rollback flows through the orchestrator's staging-drop instead") cannot land until 0179 activates cluster mode on the hot path.

**Design intent — does this become a free-fn or stay on TypeCheckEnv?** The facade's directive is `pub(crate)`-scoped to typecheck-internal callers, NOT free-fn relocation. The other module-lifecycle methods (F-2/F-3/F-4) became free-fns in the S67 hack-back because int needed to call them without constructing a typecheck env; `snapshot`/`restore` post-0179 will have **zero** int consumers (staging-drop is the replacement), so there is no S67-style motivation to lift them off the type. The facade's prescription is: stay on `TypeCheckEnv`, narrow to `pub(crate)`. No A2-style binary choice — Decision 44 + FIXME 0179 jointly name the resolution.

**Disposition.** **Source-moves (gated on FIXME 0179).** Pre-0179: `snapshot`/`restore` stay `pub` on `TypeCheckEnv`; int's `session_v4.rs:1391-1405` paths remain. Post-0179 (when cluster mode activates on the hot path, FIXME 0179 closes): /dev (int) removes the `tc_snapshot`/`tc_restore` helper methods (the REPL eval path collapses to orchestrator staging-drop); /dev (typecheck) narrows both methods to `pub(crate)`. No /arch arbitration is owed; the path is named by Decision 44 + FIXME 0179. Facade text needs no change.

This inverts the prior draft's A2 ("/arch arbitration: defer vs intermediate free-fn"). The prior framing missed that **post-0179 the method has zero int consumers** (staging-drop is the replacement, not an intermediate free-fn) and that the facade explicitly directs `pub(crate)`-narrowing, not free-fn relocation.

---

### Finding F-6 — `TypeCheckEnv::restore` method gated on FIXME 0179

**Disposition.** **Bundled with F-5.** Pub-api line 169; paired with `snapshot`; same FIXME 0179 gating; same `pub(crate)` resolution post-0179.

---

### Finding F-7 — `CheckResult` struct is public but orphaned (no public function returns it)

**Facade expects.** §"Types originated here" lines 230-237:

```rust
// Per Decision 44's 2026-05-13 third amendment, CheckResult is pared to
// the two cross-cluster items that the orchestrator surfaces to the REPL
// display layer; per-symbol Pass-2 side products land on staging
// ModuleEntry::Def fields per invariant 3a, NOT on CheckResult.
pub struct CheckResult {
    pub display: Option<DisplayInfo>,
    pub warnings: Vec<Warning>,
}
```

The struct exists, but no public function returns it. `check_forms` returns `Result<(), CheckError>` per Decision 44 third amendment (facade line 21 — `Ok(())` on success, per-symbol side products land on staging Def fields). Per the facade's own §"No public accumulator type" (line 125): "the briefly-considered relocation of that struct to `int` are both retired. Per-symbol Pass-2 side products land on staging `ModuleEntry::Def` fields per invariant 3a. … Cross-symbol bookkeeping that `int` itself collects during cluster processing (warnings, resolved-import bindings, introspection records) lives on `int`-side data structures — see `facades/int.md` §'Cluster orchestration result'."

So the facade clearly states: cross-symbol bookkeeping (warnings, etc.) is `int`-side, NOT a typecheck return. `CheckResult` as a typecheck-side type with `display` + `warnings` fields is therefore **unmotivated by the facade text** — those fields, per the facade's own prose, live on `int`-side `ProcessedCluster`.

**Source does.** Pub-api lines 121-134: `CheckResult` struct with `display: Option<DisplayInfo>` and `warnings: Vec<Warning>` fields, all pub. No `pub fn` in the typecheck crate returns it. Pub-api shows no producer.

**Design intent.** FIXME 0173 (partially-superseded supersession note, 2026-05-13): "**`pub struct ModuleCheckAccumulator` relocation to `int` — RETRACTED.** The accumulator is removed from the public surface on both sides. Per-symbol Pass-2 side products land on staging `ModuleEntry::Def` per invariant 3a (still applies). Pass-1-to-Pass-2 working state is internal to `check_forms`'s frame. Cross-symbol bookkeeping that `int` collects (warnings, resolved_imports, introspection_records) lives directly on `ProcessedCluster` — not on a separately-named `ModuleCheckAccumulator` type." `CheckResult` carries the same disposition by extension — its `warnings: Vec<Warning>` field is the same data that landed on the retired `ModuleCheckAccumulator`. Decision 44 third amendment's design intent is: per-symbol annotations live on staging `Def`; cluster-level cross-symbol data lives on `int`-side `ProcessedCluster`; the typecheck-side `CheckResult` is leftover surface from the pre-third-amendment shape that returned per-pass results.

**Difference implies.** A reader of `facades/typecheck.md` is told (§"Types originated here") that `CheckResult` is one of the types typecheck originates; the live pub-api confirms it exists; but **no public function produces it**. A consumer cannot use this type. The facade's commentary block does not retire it explicitly (it just describes it), creating ambiguity: is `CheckResult` an internal staging type that should not be pub, or a deferred public surface that something will return in a future amendment? The configuration grounds the answer: per FIXME 0173 + Decision 44 third amendment + facade §"No public accumulator type", `warnings` data lives on `int`-side `ProcessedCluster`, NOT on a typecheck return.

**Disposition.** **Source-moves.** /dev (typecheck) narrows `CheckResult` to `pub(crate)` (or deletes it if no internal caller depends on it — internal usage TBD by /dev (typecheck) audit, but the narrowing is the binding action). Facade follow-on: tighten §"Types originated here" to retire `CheckResult` from the listed types, similar to how `CheckPass`, `FormCheckResult`, `ModuleCheckAccumulator` are listed as "removed from the public surface entirely per Decision 44's 2026-05-13 third amendment." The `display`/`warnings` data path is already named: it lives on `int`-side `ProcessedCluster` per `facades/int.md` §"Cluster orchestration result".

This inverts the prior draft's A3 ("/arch arbitration: Result<CheckResult, CheckError> vs ClusterContext accessor"). The prior draft did not have FIXME 0173's supersession note loaded — the supersession note already disposed `ModuleCheckAccumulator` (and by direct extension `CheckResult`'s cross-symbol fields) into `int`-side `ProcessedCluster`. No /arch decision is owed.

---

### Finding F-8 — Facade prose inconsistency between `check_forms` and `register_imports`/`register_exports` parameter spelling

**Facade expects.** §"Free function — cluster check" uses `&SymbolTables<C, L>` shorthand (line 19). §"Module-lifecycle free functions" lines 189-201 expand to `&DashMap<ModuleFullPath, SymbolTable<C, L>>` (verbatim). Same parameter shape; two different spellings within the same facade document.

**Source does.** Pub-api 179, 182, 183 use `&dashmap::DashMap<…>` uniformly (no alias). Source is internally consistent — the inconsistency is purely facade-side prose.

**Design intent.** Facade should be internally consistent for reader clarity (Principle 13 — auditability). The shorthand has been used consistently for `check_forms` since Decision 44's third amendment, but the §"Module-lifecycle free functions" addition (S67 hack-back) was authored against the verbatim DashMap shape and never aligned.

**Difference implies.** A reader who diffs the two facade sections sees `&SymbolTables<C, L>` in one and `&DashMap<…>` in the other and reasonably wonders whether they differ. They do not.

**Disposition.** **Facade-moves.** Bundled with F-1's facade follow-on: once the `SymbolTables<C, L>` alias materialises in `cranelisp-types` (F-1 source-side), update §"Module-lifecycle free functions" to use `&SymbolTables<C, L>` consistently with §"Free function — cluster check". One-line edit per signature. Same /design (typecheck) facade pass. (Note: /design (typecheck) edits `facades/typecheck.md` per /arch facade-ownership? No — facades are /arch-owned per `.claude/commands/design.md` boundary statement. File FIXME `target: /arch` to align the prose; do not edit `facades/typecheck.md` directly.)

---

### Finding F-9 — Pass-1-to-Pass-2 working-state encapsulation invariant has no mechanical guard

**Facade expects.** §"Bounded-context invariants" item 3a and Decision 44 third-amendment Statement:

> **Pass-1-to-Pass-2 working state and cluster-scoped algorithmic intermediaries** (the data that flows internally between Pass 1's signature registration and Pass 2's body check — `defn_type_vars`, default-method-defn deferrals from trait-impl registration, generalisation inputs, multi-sig variant accumulation, the deferred-resolutions working set) are **internal to `check_forms`'s stack frame**. They are not exposed at the facade — no `&mut ModuleCheckAccumulator` parameter, no `pub` accumulator type. They are constructed when `check_forms` enters, consumed across the Pass 1 → Pass 2 boundary internally, and dropped when `check_forms` returns.

**Source does.** No public type named `ModuleCheckAccumulator`, `Pass1State`, or similar exists in pub-api. `CheckState` (pub-api 135-145) is `#[non_exhaustive]` and exposes no public fields. `TypeCheckEnv` (162-177) is `#[non_exhaustive]` and exposes no public fields. The invariant is honored today — confirmed by pub-api inspection.

**Design intent.** FIXME 0177 (open, filed 2026-05-13 by /dev (int)) is the operational concern: the cross-form state-loss regression (`defn_type_vars` rebuilds per call rather than persisting across REPL inputs in the same module) is a /typecheck-internal implementation problem, NOT a facade-shape problem. The facade invariant is honored at the boundary; the regression is below it. FIXME 0177 names the two candidate directions (A: persist working state across calls within a cluster handle; B: distinguish register-only from check-body at the facade re-exposing a discriminator). The audit cannot decide between them — they are interior to `check_forms`'s implementation.

**Difference implies.** The mechanical compliance test (`facade_compliance`, `facade_pif_rows`, `public_api_relocations`) cannot enforce this invariant by construction. A future refactor that accidentally hoisted `defn_type_vars` onto `CheckState` as a new field (`#[non_exhaustive]` permits new pub fields without test breakage) would not register as compliance failure — only the type's external shape is checked. No downstream code is built on the wrong structure today (the invariant is honored); FIXME 0177's regression is below the facade.

**Disposition.** **Mechanical-test gap (live with /review enforcement).** The invariant is honored today; no mechanical test enforces it cleanly. Documentation in `crates/cranelisp-typecheck/src/checker.rs` neighborhood naming Decision 44 + invariant 3a, plus /review's structural check against the facade at PR time, is the durable enforcement. No FIXME needed — the invariant is stated in `facades/typecheck.md` invariant 3a and reinforced in Decision 44 third-amendment commentary. /qa enhancement (a doc-test asserting struct fields) is bounded-value for the threat model (one-time regression on a /review-visible PR) and not recommended for this sprint.

FIXME 0177 (cross-form state regression) is **adjacent but distinct** — it is a behavioural regression inside `check_forms`, not a facade-encapsulation defect. The two should not be conflated.

---

### Finding F-10 — `TypeCheckEnv` carries `&'a DashMap` directly, not `&mut ClusterContext`

**Facade expects.** §"Cluster check scaffolding" lines 104-109:

> `pub struct TypeCheckEnv<'a, C, L> { /* per-form environment — wraps &mut ClusterContext + read-only symbol_tables */ }`

And in prose lines 112-113:

> `TypeCheckEnv` carries `&mut ClusterContext<'_, C, L>` per Decision 38 + Decision 44 (amended FIXME 0167) — table access flows through `ClusterContext::current_symbol_table()` (read, returning `ClusterRead`) / `current_symbol_table_mut()` (write, returning `ClusterWrite`) so the 91 register-call sites and 51 access sites in `program.rs` do not change individually.

**Source does.** `checker.rs:152`: `pub(crate) modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>`. Constructor `TypeCheckEnv::new` (pub-api 165): `(modules: &'a DashMap<…>, next_id: &'a AtomicU32) -> Self`. The `<C, L>` and the lifetime are present; the parameter is the bare DashMap. Internal callers (`self.modules.get(...)`, ~30 sites across `checker.rs`) read and write directly against the DashMap, NOT through `ClusterContext` accessors.

**Design intent.** Decision 44 (amended FIXME 0167; reframed Decision 38): the cluster-atomic surgery is at the `ClusterContext` accessor layer. The 91 register-call sites and 51 read sites continue to flow through accessors so the staging-vs-live distinction is absorbed inside the guard, not threaded through every call site. `TypeCheckEnv` is the per-form environment that **wraps** `&mut ClusterContext` — the facade is explicit on this point. The current source predates this — it borrows the DashMap directly (post-S64 shape) and has not migrated to `&mut ClusterContext`. FIXME 0179 (cluster-mode read-union staging) names the source-side gating: the 51 read sites need a `View`-shaped API before `ClusterContext::Cluster` mode can activate on the hot path; the same surgery touches `TypeCheckEnv`'s table-borrow shape.

**Difference implies.** Until `TypeCheckEnv` carries `&mut ClusterContext` (instead of `&DashMap`), the cluster-atomic write redirection at the accessor layer cannot be exercised by `TypeCheckEnv`-mediated paths. Today writes via `TypeCheckEnv` go straight to live; cluster mode is only achieved by routing **around** `TypeCheckEnv` to `ClusterContext::current_symbol_table_mut()` directly (which is what `check_forms` does internally, but most of typecheck's interior is still on the older `TypeCheckEnv` direct-DashMap-borrow shape). The cluster-atomic invariant (BC §2 + Decision 44) is delivered at the facade boundary because `check_forms` runs the orchestrator's `ClusterContext::Live` mode today (per `src/CLAUDE.md` §"Status"); cluster mode on the hot path is gated on FIXME 0179.

**Disposition.** **Source-moves (gated on FIXME 0179).** When FIXME 0179 activates cluster-mode read-union, /dev (typecheck) reshapes `TypeCheckEnv` to consume `&mut ClusterContext<'_, C, L>` instead of `&'a DashMap<…>`. The constructor signature changes; the ~30 `self.modules.X` interior accesses migrate to `self.ctx.current_symbol_table[_mut]()`. This is part of the Wave 3a-α/β scope per Decision 46. Facade text needs no change (it already names the target shape).

This is **a finding the prior draft did not surface** — the prior draft's F-11 framed the question as "universe iteration vs Principle 17 shapes" without observing that `TypeCheckEnv` itself does not yet flow through `ClusterContext`. Both are facets of the FIXME-0179-gated locality refactor.

---

### Finding F-11 — `known_type_names_in_module` Tier-2 universe scan: internal Principle 17 question, NOT a facade-audit finding

**Facade expects.** Facade does NOT name `known_type_names_in_module` — the function is `pub(crate)` and does not cross the facade. The relevant facade-side directive is §"Bounded-context invariants" item 10 (Principle 17 module-locality), which prescribes four legitimate cross-module access shapes.

**Source does.** `checker.rs:1951` (`pub(crate) fn known_type_names_in_module`). Tier 1 (lines 1958-1979): `for_each_in_module` of the current module only — Principle 17 shape 4 (bulk introspection, current-module-only). **Compliant.** Tier 2 (lines 1981-2003): `for module_entry in self.modules.iter()` — iterates the universe of modules to build a parallel FQ-key resolution table. The in-place doc-comment justifies as "FQ refs are explicit module specifications by the source author — NOT a fallback or graph walk, so Principle 17's 'no fallback' does not apply."

Caller set: `adt.rs:201, 911`; `infer.rs:229, 854`; `program.rs:2203` (all via `known_type_names_with_state` which delegates to `known_type_names_in_module` at line 2010); `checker.rs:2556` (TypeChecker wrapper, internal).

**Design intent.** Principle 17 lists four cross-module access shapes and explicitly forbids closure walks. The principle does NOT name "universe scan to build a parallel FQ key map" as a fifth shape. The in-place doc-comment self-justifies based on the FQ-explicit-source argument, but Principle 17 as written does not admit the exception.

**Is this a facade finding?** **No.** The function is `pub(crate)`. It does not appear in `public-api.txt`. It does not cross the facade boundary. The facade compliance audit (per `feedback_audit_per_item_analysis.md`) compares facade-expected surface vs source-as-built surface — that pair does not surface `pub(crate)` items by construction. The Principle 17 invariant applies to the typecheck crate internally; BC §2 "Module-locality invariant" makes the invariant a typecheck-internal contract, NOT a facade-boundary contract.

**Difference implies.** The Principle 17 question (is Tier 2 a legitimate shape or a violation?) is a real /design (typecheck) question — it belongs in `design/typecheck/typecheck.md` §11 (open questions) or as a separate FIXME `target: /design (typecheck)`. It is NOT material to the S69 facade audit. Routing it through the facade audit (as the prior draft did, calling it the "load-bearing arbitration") inflated the audit's scope and obscured that the question is interior to typecheck.

A typecheck-internal audit (separate from this facade audit) would ground the Tier 2 question against:
1. **FIXME 0179** — cluster-mode read-union — the same surgery that reshapes `TypeCheckEnv` to flow through `ClusterContext` (F-10) will inevitably touch this iteration site, because `self.modules.iter()` becomes `self.ctx.iter_modules()` or equivalent; the staging-blind question (does this iteration miss staging-staged TypeDefs?) becomes concrete at that point.
2. **Principle 17 as-written** — the four shapes are exhaustive in the text; the Tier 2 iteration does not fit any of them; the doc-comment exemption is not principled.
3. **The actual call frequency** — once per `check_forms` call (not per-form), so the perf cost of per-FQ-lazy-resolution is bounded.

The disposition belongs to /design (typecheck) interior work, NOT facade arbitration. /arch is not owed a decision here unless the typecheck-internal audit lands a Principle-17 amendment proposal.

**Disposition.** **Internal /design (typecheck) follow-on; NOT a facade-audit finding.** Recommendation: /design (typecheck) opens an entry in `design/typecheck/typecheck.md` §11 capturing the Tier-2-vs-Principle-17 question. Resolution proceeds in the Wave 3a-α / FIXME 0179 cluster-mode-on-hot-path work, where the iteration site is naturally touched. No /arch FIXME, no facade text change.

This inverts the prior draft's A1 ("load-bearing /arch arbitration"). The prior draft did not observe that the function is `pub(crate)` and that the question is interior to typecheck per BC §2; it elevated an internal-locality question to facade-arbitration scope, contradicting `/design`'s boundary statement (`.claude/commands/design.md` §Boundary: "Never edit `design/arch/` — cross-crate / between-crate concerns are `/arch`'s. File FIXME `target: /arch` instead.").

---

### Finding F-12 — `SymbolTableEnsureOutcome` duplicate exposure at crate root

**Facade expects.** §"Trace hooks" lines 172-177:

```rust
// re-exported at crate root for convenience:
pub use trace::{
    SymbolTableEnsureOutcome,
    SymbolTableEnsureHook,
    install_symbol_table_ensure_hook,
};
```

**Source does.** Pub-api shows three items at both `cranelisp_typecheck::trace::*` (lines 6-30) AND `cranelisp_typecheck::*` (lines 100-120 + 180 + 184). Re-export is in place and pub-api projection duplicates the impl lines (re-export semantics).

**Design intent.** Facade explicitly names the three re-exports. No drift.

**Difference implies.** None — pub-api's "duplicate" lines are projection artefacts of the re-export, not real surface drift.

**Disposition.** **No action.** Auto-trait noise from cargo-public-api's re-export projection.

---

### Finding F-13 — `pub use cranelisp_types::CranelispError` legacy crate-root re-export

**Facade expects.** §"Types originated here" line 281-282:

> **Two legacy crate-root re-exports** (`pub use cranelisp_types::CranelispError` and `pub use cranelisp_types::TopLevel`) appear at `cranelisp_typecheck::CranelispError` / `cranelisp_typecheck::TopLevel`. Internal-but-exposed convenience re-exports: callers that import `cranelisp_typecheck::*` for the typecheck surface also reach for these types in error-handling and AST-input paths. Per Principle 15 these are not endorsed at the facade level — new callers should import `CranelispError` / `TopLevel` directly from `cranelisp-types`. **Removal is a /dev (typecheck) Wave 3 follow-on once external import sites are confirmed clean** (no S67 close requirement; tracked as housekeeping).

**Source does.** Pub-api lines 2-3:
- `pub use cranelisp_typecheck::CranelispError`
- `pub use cranelisp_typecheck::TopLevel`

**Design intent.** Principle 15 (facade types live with behaviour): implementation-crate facades do NOT re-export `cranelisp-types` items — multi-consumer types should be imported from `cranelisp-types` directly by every consumer. The two re-exports are named as removal candidates in the facade.

**Difference implies.** No silent drift — the facade explicitly tracks these as "removal is Wave 3 follow-on once external import sites are confirmed clean." Reader is informed.

**Disposition.** **Source-moves (housekeeping, not S69-blocking).** /dev (typecheck) audits int's import sites; once no caller uses `cranelisp_typecheck::CranelispError` or `cranelisp_typecheck::TopLevel`, the re-exports drop. Not in S69 scope per the facade's own tracking ("no S67 close requirement; tracked as housekeeping"). No FIXME needed — the facade itself is the tracker.

---

### Finding F-14 — Facade silent on `check_forms`'s third parameter spelling vs cross-module read shape from BC §2

**Facade expects.** BC §2 (Typecheck): "a symbol-table-view window passed by the caller." `facades/typecheck.md` line 26 prose: "`symbol_tables` — read-only access to all other modules' tables for resolving FQ symbol references (`m2/foo`) and FQ type references (`m2/SomeType`). Generic over `<C, L>` per Decision 32 — typecheck is C/L-blind in production…"

**Source does.** Live signature accepts `&DashMap<…>` — same shape as `ClusterContext`'s `modules` field. There is one universe-of-modules surface that `check_forms` reads via two routes: directly through the `symbol_tables` parameter (for cross-module FQ resolution) AND indirectly through `ctx`'s embedded `modules: &DashMap` (for current-module read-or-write). Both routes lead to the same DashMap.

**Design intent.** Decision 44 third amendment carries both surfaces deliberately: `ctx` is the current-module-with-staging accessor; `symbol_tables` is the cross-module read. They are distinct *roles*, even though they alias to the same underlying DashMap. The facade does not explain why both are needed — a reader sees two parameters that look like the same thing.

**Difference implies.** A facade reader can puzzle over "why does `check_forms` take both `ctx` (which contains `modules: &DashMap<…>`) and `symbol_tables: &DashMap<…>` separately? Are they the same?" The answer (yes, alias by construction; conceptually distinct roles) is in Decision 44 third-amendment Statement but not in the facade prose. Minor doc-clarity issue, not a contract defect.

**Disposition.** **Facade-moves (doc clarity).** /design (typecheck) requests a one-sentence addition to `facades/typecheck.md` §"Free function — cluster check" parameter prose: "The `symbol_tables` parameter aliases `ctx`'s embedded `modules` field by construction; the two are distinct *roles* (cross-module read vs current-module-with-staging) sharing one underlying DashMap." File FIXME `target: /arch`.

---

### Finding F-15 — `register_builtins` parameter shape divergence from `check_forms`

**Facade expects.** §"Builtin registration" lines 130-134:

```rust
pub fn register_builtins<C, L>(
    modules: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    next_id: &AtomicU32,
)
where C: CodeStore, L: LinkerStore;
```

Per facade prose, this is the post-S66 cluster-atomic shape: `register_builtins` operates against the whole modules-map, threads `next_id` for type-var allocations, and is idempotent.

**Source does.** Pub-api 181: `pub fn register_builtins<C, L>(modules: &DashMap<…>, next_id: &AtomicU32) where C: CodeStore, L: LinkerStore`. Exact match.

**Design intent.** Decision 44 third amendment (post-S66 shape per facade): builtin registration is cluster-atomic-shaped — same `(modules, next_id)` argument pair as the module-lifecycle free fns (F-2/F-3/F-4 in source-side context).

**Difference implies.** None — facade and source match in spelling and prose. Note: when F-1's `SymbolTables<C, L>` alias materialises, `register_builtins` should adopt it for consistency with `check_forms` / `register_imports` / `register_exports`.

**Disposition.** **No action today; bundled with F-1's facade-side prose pass.** When the alias lands, `register_builtins`'s facade signature updates to `&SymbolTables<C, L>` mechanically.

---

## 2. Findings overview

| ID | One-line subject | Disposition class | Grounding citation |
|---|---|---|---|
| F-1 | `SymbolTables<C, L>` textual shorthand vs no source alias | Both-move | Decision 44 third amendment (Statement); Principle 13 (auditability); Principle 15 (boundary types at primary site) |
| F-2 | `TypeCheckEnv::ensure_module_exists` pub vs `pub(crate)` target | Source-moves | Decision 44 (TypeCheckEnv 2-method target); FIXME 0187 Phase B; `facades/types.md` §"Module-lifecycle primitives" |
| F-3 | `TypeCheckEnv::register_imports` method (zero int consumers) | Source-moves | FIXME 0192 (S67 hack-back); facade §"Module-lifecycle free functions" |
| F-4 | `TypeCheckEnv::register_exports` method (zero int consumers) | Source-moves | (Bundled with F-3.) |
| F-5 | `TypeCheckEnv::snapshot` (FIXME 0179 gated) | Source-moves (gated) | Decision 44 (staging-drop replacement); FIXME 0179; facade §"TypeCheckEnv target shape" |
| F-6 | `TypeCheckEnv::restore` (FIXME 0179 gated) | Source-moves (gated) | (Bundled with F-5.) |
| F-7 | `CheckResult` orphan (pub but no public producer) | Source-moves | FIXME 0173 supersession note; Decision 44 third amendment; `facades/int.md` §"Cluster orchestration result" |
| F-8 | Facade prose inconsistency: SymbolTables vs DashMap spelling | Facade-moves | Principle 13 (auditability); bundled with F-1 |
| F-9 | Pass-1-to-Pass-2 working-state encapsulation invariant | Mechanical-test gap | Facade §"Bounded-context invariants" 3a; Decision 44 third amendment; FIXME 0177 (interior) |
| F-10 | `TypeCheckEnv` borrows `&DashMap` directly, not `&mut ClusterContext` | Source-moves (gated) | Decision 44 (amended FIXME 0167); facade §"Cluster check scaffolding" line 113; FIXME 0179 |
| F-11 | `known_type_names_in_module` Tier-2 universe scan | Internal /design (typecheck); NOT facade | Principle 17; BC §2.10; FIXME 0179 (interior touchpoint) |
| F-12 | `SymbolTableEnsureOutcome` re-export projection duplication | No action | (auto-trait noise) |
| F-13 | `pub use cranelisp_types::CranelispError`, `TopLevel` legacy re-exports | Source-moves (housekeeping) | Principle 15; facade §"Types originated here" lines 281-282 |
| F-14 | Facade silent on `symbol_tables`-aliases-`ctx.modules` rationale | Facade-moves (doc clarity) | Decision 44 third-amendment Statement |
| F-15 | `register_builtins` parameter shape (clean today; adopts alias later) | No action | Facade §"Builtin registration"; bundled with F-1 |

**Class totals**: Source-moves 8 (F-2, F-3, F-4, F-5, F-6, F-7, F-10, F-13), Facade-moves 2 (F-8, F-14), Both-move 1 (F-1), Mechanical-test gap 1 (F-9), Internal /design (typecheck) 1 (F-11), No action 3 (F-12, F-15, bundling). Counting unique findings: 15.

---

## 3. Calibration of prior dispositions

Per `feedback_audit_per_item_analysis.md`: every disposition flipped by configuration reading is named explicitly with grounding.

| Finding | Prior draft disposition | This draft disposition | Grounding that flipped it |
|---|---|---|---|
| F-1 (alias) | Both-move (same) | Both-move | No flip; conclusion stable. Both drafts read facade + pub-api; configuration confirmed Principle 13 motivation. |
| F-2 (`ensure_module_exists`) | Source-moves (same) | Source-moves | No flip. FIXME 0187 Phase B reading clarified the existing types-crate free-fn path. |
| F-3 (`register_imports` method) | Source-moves (same) | Source-moves | No flip on direction. **Stronger grounding** from FIXME 0192 reading and grep audit confirming zero int method-form consumers. Prior draft's "atomic /dev (typecheck + int) brief framing was misleading" stands. |
| F-4 (`register_exports` method) | Source-moves (same) | Source-moves | No flip. (Bundled with F-3.) |
| F-5 (`snapshot`) | **/arch arbitration (A2)** | **Source-moves (gated on FIXME 0179)** | **FLIPPED.** Prior draft framed as "binary choice (a) defer to 0179 vs (b) intermediate free-fn." Configuration reading shows facade explicitly names `pub(crate)`-narrow (not free-fn relocation) as the resolution; FIXME 0179 names the precondition; post-0179 the method has zero int consumers (staging-drop replaces). No arbitration is owed — the path is binding. |
| F-6 (`restore`) | /arch arbitration (A2 bundled) | Source-moves (gated; bundled with F-5) | (Bundled flip.) |
| F-7 (`CheckResult` orphan) | **/arch arbitration (A3)** | **Source-moves** | **FLIPPED.** Prior draft framed as "binary choice (a) Result<CheckResult, CheckError> return vs (b) ClusterContext accessor." FIXME 0173 supersession note disposed `ModuleCheckAccumulator` (and by extension `CheckResult`'s cross-symbol fields) into `int`-side `ProcessedCluster`. Decision 44 third amendment confirms: per-symbol annotations on staging Def, cluster-level on `int`-side. No arbitration is owed. /dev (typecheck) narrows `CheckResult` to `pub(crate)` or deletes. |
| F-8 (prose inconsistency) | Facade-moves (same) | Facade-moves | No flip. |
| F-9 (encapsulation invariant) | Mechanical-test gap (same) | Mechanical-test gap | No flip on conclusion. **Clarified separation** from FIXME 0177 (cross-form state regression is below-the-facade behavioural regression, not facade-encapsulation drift). |
| F-10 (TypeCheckEnv shape) | **Not surfaced** | **Source-moves (gated on FIXME 0179)** | **NEW FINDING.** Prior draft did not observe that source's `TypeCheckEnv` carries `&DashMap` directly while facade prescribes `&mut ClusterContext`. Material drift; FIXME 0179 gated. |
| F-11 (universe scan) | **"Load-bearing /arch arbitration A1"** | **Internal /design (typecheck); NOT facade-audit** | **FLIPPED.** Prior draft elevated as "the single load-bearing arbitration." Configuration reading shows the function is `pub(crate)` — it does not cross the facade. BC §2.10 + Principle 17 make module-locality a typecheck-internal invariant; the question belongs to /design (typecheck) interior work, NOT to /arch via facade audit. `/design`'s boundary statement forbids routing internal questions through /arch unless cross-crate; this is intra-crate. |
| F-12 (re-export projection) | No action (same) | No action | No flip. |
| F-13 (legacy re-exports) | **Not surfaced** | **Source-moves (housekeeping)** | **NEW FINDING.** Prior draft did not flag the two `pub use cranelisp_types::*` legacy re-exports. Facade tracks them explicitly as Wave 3 housekeeping; surfacing maintains audit completeness. |
| F-14 (symbol_tables alias prose) | Not surfaced | Facade-moves (doc clarity) | **NEW (minor).** Surfaced on Decision 44 third-amendment Statement reading. |
| F-15 (register_builtins) | Not surfaced | No action | **NEW (informational).** Confirms current shape matches facade. |

**Disposition flips**: **3 substantive flips** (F-5, F-7, F-11) — all three flips remove /arch arbitration items because configuration grounded the resolution. The prior draft listed 3 /arch arbitrations; this draft lists **0**.

**New findings**: **3** (F-10, F-13, F-14/F-15 informational). The most substantive is F-10 (`TypeCheckEnv` not yet flowing through `ClusterContext`) — a real source-side drift the prior draft missed because it did not load Decision 44's amended-FIXME-0167 commit closely.

---

## 4. What the audit cannot resolve alone

**None.** The prior draft listed three /arch arbitration items (A1 universe iteration; A2 snapshot/restore; A3 CheckResult orphan). On configuration grounding, all three resolve without arbitration:

- **A1 (universe iteration)** is internal to typecheck (function is `pub(crate)`); not a facade finding. /design (typecheck) tracks in `design/typecheck/typecheck.md` §11.
- **A2 (snapshot/restore)** is FIXME-0179-gated source-moves; facade explicitly names `pub(crate)`-narrow as the post-0179 resolution.
- **A3 (CheckResult orphan)** is source-moves per FIXME 0173 supersession note + Decision 44 third amendment.

If /arch reviews this audit and finds the configuration is itself ambiguous on any of the three flipped items (e.g., disagrees that FIXME 0173 supersession note disposes `CheckResult`'s fields into `int`-side `ProcessedCluster`), the disposition would re-open. Audit defers to /arch on configuration meta-questions only — never on facade-vs-source mechanics where the configuration grounds the answer.

---

## 5. Verdict

cranelisp-typecheck is post-S67-narrowing and structurally honest. The drift residue is small (15 findings) and disposes cleanly when configuration is loaded:

- **5 of 15 are source-moves with no /arch involvement** (F-2, F-3, F-4, F-7, F-13) — /dev (typecheck) and /dev (int) execute against existing FIXMEs (0187) or against facade prose alone.
- **2 of 15 are source-moves gated on FIXME 0179** (F-5/F-6, F-10) — they wait on cluster-mode read-union landing on the hot path. F-10 is the substantive new finding (the prior draft missed it).
- **1 of 15 is the both-move alias materialisation** (F-1) — light coordinated change; types-crate gets a one-line `pub type`; facade prose tightens (F-8 + F-15 bundled).
- **2 of 15 are facade-moves** (F-8, F-14) — internal facade-prose consistency tightening; /design (typecheck) files FIXME `target: /arch`.
- **1 of 15 is a mechanical-test gap** (F-9) — invariant is honored today; /review enforcement; no action this sprint.
- **1 of 15 is internal /design (typecheck)** (F-11) — Principle-17-vs-Tier-2-iteration question is typecheck-interior, not facade-boundary; tracked in `design/typecheck/typecheck.md` §11.
- **3 of 15 are no-action** (F-12, F-15, F-13 housekeeping).

**No /arch arbitration items in this sprint.** The prior draft's three /arch arbitrations were all configuration-resolvable; the prior draft missed them because it did not load FIXME 0173 supersession note, BC §2.10 module-locality invariant scope, or Decision 44 amended-FIXME-0167 detail on `TypeCheckEnv`'s `&mut ClusterContext` target shape.

The single substantively new finding the prior draft missed is **F-10** — `TypeCheckEnv` carries `&'a DashMap` directly while the facade prescribes `&mut ClusterContext`. This is a real source-side drift gated on FIXME 0179, and the prior draft's framing of the universe-scan as "load-bearing" was misdirected away from this more material drift.

S69 facade-audit work for /design (typecheck) is light: one FIXME `target: /arch` (F-1 alias + F-8 prose + F-14 doc-clarity bundled). All other dispositions are /dev (typecheck) execution against existing FIXMEs (0187 Phase B for F-2; unilateral narrowing for F-3/F-4/F-7/F-13) or FIXME-0179-blocked (F-5/F-6/F-10).

No sprint-close blocker. The facade is target-stating per its discipline (`facades/typecheck.md` line 5: "This spec is **target-stating**"); the deltas are implementation-not-yet-caught-up against named FIXMEs.
