---
number: 0173
target: /dev (typecheck)
filed_by: /arch
filed_at: 2026-05-13
sprint_filed: 66
refers_to: design/arch/facades/typecheck.md §"check_forms — cluster check", §"Types originated here", §"#[non_exhaustive] DTOs", §"Bounded-context invariants" item 3a; design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md (2026-05-13 third amendment); crates/cranelisp-typecheck/public-api.txt L133–L153, L208, L213, L214; crates/cranelisp-typecheck/src/**.rs (the implementation site)
status: partially-superseded — see supersession note below
---

# Remove `CheckPass` from public API + (RETRACTED — `ModuleCheckAccumulator` relocation to int) — superseded by Decision 44 third amendment

## SUPERSESSION NOTE (2026-05-13)

This FIXME's three items have different dispositions after Decision 44's 2026-05-13 third amendment (which collapses `check_form_signatures` + `check_form_body` into a single `check_forms` function):

1. **`pub enum CheckPass` removal — STILL APPLIES.** The pass discriminator is internal to `check_forms`'s frame; no public enum.
2. **`pub struct ModuleCheckAccumulator` relocation to `int` — RETRACTED.** The accumulator is removed from the public surface on both sides. Per-symbol Pass-2 side products land on staging `ModuleEntry::Def` per invariant 3a (still applies). Pass-1-to-Pass-2 working state is internal to `check_forms`'s frame. Cross-symbol bookkeeping that `int` collects (warnings, resolved_imports, introspection_records) lives directly on `ProcessedCluster` — not on a separately-named `ModuleCheckAccumulator` type. See `facades/int.md` §"Cluster orchestration result".
3. **Method-form `check_form` / `merge_form_result` / `finalize_check_result` removal — STILL APPLIES.** Replaced by the single `check_forms` free function. Pre-S66 method-form callers migrate to `check_forms`.

The implementation work the FIXME was originally filed to capture is now subsumed into the Wave 3a-β re-fire under the collapsed `check_forms` shape. The work item is left here as a record; `/dev (typecheck)` should treat Decision 44's third amendment as the authoritative direction and the canonical facade text (`facades/typecheck.md` §"check_forms — cluster check") as the target.

---

# Remove `CheckPass` from public API + relocate `ModuleCheckAccumulator` to int + write Pass 2 side products onto staging `ModuleEntry::Def`

## Issue

The pre-Wave-3a-β `cranelisp-typecheck` public API surface carries three items that should not be public per the user-arbitrated direction of 2026-05-13 (the Wave 3a `/arch` round):

1. **`pub enum CheckPass { Pass1Signatures, Pass2Bodies }`** (public-api.txt: present; facade was the last place that named it). The pass discriminator is now implicit in the free-function-pair dispatch (`check_form_signatures` vs `check_form_body`); a public runtime enum adds nothing the function-by-function dispatch does not already encode.
2. **`pub struct ModuleCheckAccumulator { … }`** (public-api.txt L133–L153). Single-consumer type per Principle 15 — `int` is the only crate that constructs / drains it. Relocates to `int` (the cluster-atomic orchestrator owns it; the new home is documented in `facades/int.md` §"`ModuleCheckAccumulator` — cluster-level cross-symbol bookkeeping").
3. **`pub fn TypeCheckEnv::check_form(…, pass: CheckPass, …, accumulator: &mut ModuleCheckAccumulator) -> Result<FormCheckResult, CranelispError>`** (public-api.txt L208) and its sibling `finalize_check_result` (L213) / `merge_form_result` (L214). The method-shape per-form entry is replaced by the two free functions; both `CheckPass` and `ModuleCheckAccumulator` parameters drop with it.

Wave 3a-β already mandates removing the duplicate `check_program*` / `check_repl_input*` paths (audit Finding 1) and pivoting to the two-pass free functions. This FIXME captures the residual public-API cleanup that Wave 3a-β's design doc (§7.2) names but does not implement in the design pass.

The amended facade also pins **Pass 2 side products land on staging `ModuleEntry::Def`** (per §10 Q1 option (c)) — no `FormCheckResult` return, no `&mut FormCheckResult` accumulator parameter. Pass 2 writes `method_resolutions`, `expr_types`, `mono_defns`, `callees` into the staging `ModuleEntry::Def` entry's existing fields (`Def.callees`, `Def.ast` annotations, additional staged `Def` entries for mono specialisations). The orchestrator's drain into live (`int::insert_cluster`) carries them with each entry.

## Proposed resolution

Wave 3a-β implementation (or a paired follow-up before Wave 3b opens):

1. **Delete `pub enum CheckPass`** from `crates/cranelisp-typecheck/src/lib.rs` re-exports. If `pub(crate)` internal scaffolding wants to retain a pass enum, keep it `pub(crate)`.
2. **Move `ModuleCheckAccumulator` to `src/` (the int crate)** under whichever module owns `process_cluster` / `insert_cluster`. Keep the existing field set (`warnings`, `method_resolutions`, …) initially; the per-symbol fields drop in step 4 below as their data migrates onto staging `Def` entries. `cluster-level` fields stay (warnings, resolved_imports, introspection_records — the new home documented in `facades/int.md`). The rename to `ClusterCheckAccumulator` is deferred — keep the legacy name for cross-skill conceptual continuity, file a follow-up rename FIXME if/when the legacy name becomes a readability burden.
3. **Delete `TypeCheckEnv::check_form` (method form), `finalize_check_result`, `merge_form_result`** as part of removing the whole-program loop per Wave 3a-β §7.2. The two free functions are the replacement.
4. **Migrate Pass 2 side products onto staging `ModuleEntry::Def`**:
   - Call-graph edges → `Def.callees` (already the field, per Decision 21).
   - Per-span resolved-method calls → annotation on `Def.ast` (the typed-AST annotation pass that lands during Pass 2).
   - Per-span expr types → annotation on `Def.ast`.
   - Mono specialisations → additional staged `Def` entries with mangled names (`add$Int+Int`, etc., per existing OverloadVariant / mono pattern).
5. **Update `crates/cranelisp-typecheck/public-api.txt`** to reflect the deletions.
6. **Run `cargo nextest run -p cranelisp-typecheck`** to confirm no internal callers depended on the public surface that's being demoted.
7. **No test changes are mandated by this FIXME** — the Wave 3a-β gate tests (`process_form_dispatch.rs`) exercise the two free functions directly and do not depend on `CheckPass` / `ModuleCheckAccumulator`.

## Operational implication / Context

This FIXME is downstream of `/arch`'s facade-currency cycle for Wave 3a. The facade text is authoritative; the source implementation must close the gap. No new design questions are open — option (c) for Pass 2 side products is user-arbitrated; the relocation per Principle 15 is user-arbitrated; the CheckPass removal is user-arbitrated.

If `/dev` encounters an obstacle (e.g., a hidden public consumer of `CheckPass` or `ModuleCheckAccumulator` outside `int`), file a counter-FIXME `target: /arch` before deviating — the facade is the current `/arch` position.
