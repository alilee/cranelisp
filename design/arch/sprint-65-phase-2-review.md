# Historical — original Phase 2 review for the (superseded) facade-adoption-at-edges scope; superseded by sprint-65-reshape-phase-2-review.md.

# Sprint 65 — Phase 2 Architecture Review

**Reviewer**: `/arch`
**Date**: 2026-05-05
**Status**: APPROVE WITH REVISIONS

This document is the Phase 2 verdict gating Phase 3. Five sections per the sprint plan; verdict at end.

---

## 1. Facade acceptability

Read seven facades end-to-end: `types.md`, `frontend.md`, `typecheck.md`, `backend.md`, `runtime.md`, `platform.md`, `int.md`.

**Verdict per facade — all seven acceptable as binding commitments for the duration of this sprint.**

Per-facade notes:

- **`types.md`** — Acceptable. The aspirational `FQTypeName` migration carries; `ResolutionGap` / `CheckError` / `PlatformError` already speced here are about to relocate per FIXMEs 0098 + 0100 + 0104; that relocation is in-scope work, not a facade defect. `ErrorLocation` (Decision 39) is comprehensive. `SymbolTable<C, L>` shape per Decisions 25/31/32/33 is settled.
- **`frontend.md`** — Acceptable. The four free functions (`parse`, `extract_module_declarations`, `build_ast`, `build_expr`, `expand`) plus `parse_preserving_comments`, defmacro helpers, and `next_synthetic_span` cover all consumers. `ExpansionError` move from types→frontend is a FIXME 0098 deliverable. The `SymbolTables<C, L>` alias declaration is a type alias only; structural — it does not invert the dep DAG.
- **`typecheck.md`** — Acceptable. `check_form` free-function shape with `Result<CheckResult, CheckError>` is the contract; `register_builtins` and the trace install hook complete the boundary. Originated types (`CheckResult`, `CheckError`, `ResolutionGap`, `CheckState`, `TypeCheckEnv`, `CheckPass`, `FormCheckResult`, `ModuleCheckAccumulator`, `ReplSnapshot`) match what `int` consumes today (per `src/worker.rs` and `src/session_v4.rs` import sweep).
- **`backend.md`** — Acceptable, with one observation flagged: the facade lists `Jit`, `Linker`, and `Code` types. Today `int` imports `cranelisp_backend::cache::Linker`, `cranelisp_backend::jit::Jit`, `cranelisp_backend::cache::object::{CacheWritePacket, process_cache_packet}`, `cranelisp_backend::exe::generate_startup_object`, and `cranelisp_backend::compiler::TracedFnInfo`. The path-form imports against `cache::*`, `jit::*`, `exe::*`, `compiler::*` modules will need to resolve through facade-listed re-exports (or those items hoisted into the crate root). `Jit` and `Linker` themselves are facade-listed at root level — the path-form imports need a sweep but no facade change. `CacheWritePacket`, `process_cache_packet`, `generate_startup_object`, and `TracedFnInfo` are NOT facade-listed; these are reach-arounds, catalogued in §3 below with resolutions.
- **`runtime.md`** — Acceptable. The extern-fn-name-as-symbol surface plus `IoEvent`/`IoObserver`/`register_io_observer` per Decision 40 cover everything. Today's `pub use io_trace::{...}` and `pub use trace::{...}` blocks in `crates/cranelisp-runtime/src/lib.rs` will be deleted as part of FIXME 0103 — the facade already commits to the post-relocation shape.
- **`platform.md`** — Acceptable. `OwnedPlatformFnDescriptor`, `CLType`/`CLHeap` family, `PlatformManifest`/`PlatformFn`/`HostCallbacks` (FFI repr exempt per Principle 14), `load_manifest`, `parse_type_sig`, `derive_jit_name`, `declare_platform!`, `ABI_VERSION`. The `IO_TAG_*` constants currently exposed at the crate root (`IO_TAG_PURE/EFFECT/BIND/PAR`, `IO_EFFECT_RESOURCE_OFFSET`) are NOT in the facade. Today `cranelisp_runtime::drop` and `cranelisp_runtime::io` import them. Section §3 catalogues this with resolution.
- **`int.md`** — Acceptable. Largest facade — appropriately so as the integration crate. `CompilerSession` + `SharedState` + `CompileScheduler` + `ObjectCache` + worker functions cover everything. The composed introspection flows section is target-stating only (no new types).

**No facade entry removed.** No edits to facade specs by `/arch` in Phase 2.

**Sufficiency check** — given the in-scope FIXMEs (0098, 0099, 0100, 0103, 0104, 0107, 0108) and the consumer-side fixes outlined in §3, the seven facades are sufficient. There is one in-scope dependency — exposing `IO_TAG_*` constants on `cranelisp-platform`'s public API — that the facade does not currently address. Resolution covered in §3.

---

## 2. Migration dependency graph

| FIXME | Title | Depends on | Blocks | Notes |
|---|---|---|---|---|
| 0104 | `PlatformError` adoption | — (Phase 1 of itself adds the type to `cranelisp-types`) | 0107 (same crate) | `cranelisp-types` Phase 1 is foundational; platform + int phases land together. Independent of every other in-scope FIXME. |
| 0107 | `OwnedPlatformFnDescriptor` `#[non_exhaustive]` | 0104 (bundled — same `lib.rs`) | — | Half-hour edit; coupled with 0104 mechanically. |
| 0098 | `ResolutionGap` / `CheckError` / `ExpansionError` migration | 0100 Phase 1 (relocates `CheckError`/`ResolutionGap` from types→typecheck) — sequencing matters | 0099 (lighter coupling: GotObserver doesn't depend on gap types but lands in same wave naturally) | The largest FIXME — touches frontend, typecheck, types, int. Can land sequentially with 0100 Phase 1 OR can land first; if 0098 lands first, types stay temporarily over-broad and 0100 Phase 1 trims them after. **Recommendation: do 0100 Phase 1 (typecheck-side relocations) first, then 0098.** |
| 0100 | Single-consumer type relocation | — (Phase 1: typecheck; Phase 2: backend) | 0098 (typecheck phase simpler if 0100 Phase 1 lands first); 0099 (backend phase confirms `GotEvent` etc. land in backend not types) | Two parallelisable phases. Phase 3 (verification sweep) waits on `cargo public-api` from Wave 1. |
| 0099 | `GotObserver` implementation | 0100 Phase 2 (light — just confirms target home; if 0100 Phase 2 lands first, 0099 doesn't need to relocate types into backend; if 0099 lands first, 0100 Phase 2 just verifies they're already there) | — | Backend + int dual-crate work. Independent of 0098 and 0103. |
| 0103 | `trace.rs` + `io_trace.rs` runtime→int relocation; `IoObserver` contract | — | — | Independent of every other in-scope FIXME. ~1700 LOC physical move plus observer wiring. |
| 0108 | `display.rs` backend→int relocation | 0099 (light — both touch `int` files; coupling is "same wave makes sense") | — | Mechanical 831 LOC move. Co-locatable with 0099. |

### Wave shape recommendation (advisory; `/sprint` writes Phase 4)

The dependency graph admits this wave structure:

- **Wave 1**: Foundation. `cargo public-api` install + per-crate baseline JSON commit + 95% gate test list. **No code changes.** (This is what the sprint already calls Wave 1.)
- **Wave 2**: Types crate. FIXME 0104 Phase 1 (`PlatformError` to `cranelisp-types`) + FIXME 0100 Phases 1 & 2 (relocate single-consumer types out of `cranelisp-types` into typecheck and backend). These touch only `cranelisp-types` and the receiving crates' lib.rs re-exports. After Wave 2, `cranelisp-types`'s public surface is at its target shape.
- **Wave 3**: Pilot crate. **Recommendation: pilot is `cranelisp-frontend`** for size and self-containment per the sprint's provisional choice. Wave 3 closes the typecheck and frontend sides of FIXME 0098 (`ResolutionGap` migration into proper homes via the gap-orchestration retry loop). This produces the first non-types crate at facade-faithful shape with `cargo public-api` clean.
- **Wave 4**: Parallel fan-out. Backend (FIXME 0099 GotObserver + FIXME 0108 display relocation), runtime (FIXME 0103 trace/io_trace relocation), platform (FIXME 0104 Phases 2 + 3, FIXME 0107). `int` consumer-side fixes for all of these land here.
- **Wave 5**: `src/` integration close. Final `int` consumer fixes for FIXME 0098 Phase 4 + the residual reach-around resolutions per §3. `cargo check --workspace` green; `cargo public-api` clean for all 7 crates.
- **Wave 6**: Close gate. Full `cargo nextest run`, validate ≥885, file carry FIXMEs.

This shape satisfies the sprint plan's hard constraints (pilot first; parallel only after pilot soundness). Wave 4 fan-out is acceptable because Wave 3's pilot establishes the migration pattern and the `cargo public-api` workflow.

---

## 3. Reach-around catalogue

A reach-around is a consumer importing a non-facade item. Resolutions are (a) narrow the type's home, (b) restructure the consumer, or (c) remove the dependency. Facade widening (d) is forbidden.

### Catalogue

| # | Consumer | Provider | Item | Resolution | Effort |
|---|---|---|---|---|---|
| R1 | `src/code.rs` | `cranelisp-backend` | `cranelisp_backend::cache::Linker` (path-form) | (b) Restructure: re-import via root `cranelisp_backend::Linker` (already facade-listed at root). Mechanical sed. | trivial |
| R2 | `src/code.rs`, `src/code.rs (test)` | `cranelisp-backend` | `cranelisp_backend::jit::Jit` (path-form) | (b) Restructure: re-import via root `cranelisp_backend::Jit` (already facade-listed at root). Mechanical sed. | trivial |
| R3 | `src/session.rs`, `src/session_v4.rs`, `src/worker.rs` | `cranelisp-backend` | `cranelisp_backend::cache` module (used as path) | (b) Restructure: replace `cache::Foo` path uses with the specific items, hoisted as facade entries IF facade-listed at root, OR reshape the call sites if the item is not in the facade. Per-call audit needed. | small |
| R4 | `src/cache_writer.rs` | `cranelisp-backend` | `cranelisp_backend::cache::object::{CacheWritePacket, process_cache_packet}` | (a) Narrow the type's home: `CacheWritePacket` and `process_cache_packet` are caller-specific orchestration types — their single consumer is `int`'s cache writer. Relocate to `src/cache_writer.rs` (single-consumer per FIXME 0100's pattern). | medium |
| R5 | `src/exe.rs` | `cranelisp-backend` | `cranelisp_backend::exe::generate_startup_object` | (a) Narrow the type's home: `generate_startup_object` is part of `--link` orchestration which the int facade puts on `int`. Relocate to `src/exe.rs` or the `cranelisp-exe-bundle` crate — not in the backend facade and shouldn't be. | medium |
| R6 | `src/session_v4.rs` | `cranelisp-backend` | `cranelisp_backend::compiler::TracedFnInfo` | Investigation needed. Either (a) relocate to int (if int-only consumer; likely), or (c) remove the dependency if it duplicates an int-side type. | small |
| R7 | `src/session_v4.rs` | `cranelisp-backend` | `cranelisp_backend::display::{format_type_qualified, format_scheme_display}` | (a) Narrow: these move to int as part of FIXME 0108 (`display.rs` backend→int relocation). Resolution is the FIXME itself — no separate work. | (covered by 0108) |
| R8 | `src/pipeline.rs` | `cranelisp-runtime` | `cranelisp_runtime::alloc_with_rc` | Already facade-listed (`pub fn alloc_with_rc(payload_size: usize) -> *mut u8`). NOT a reach-around — root-level public surface. No action. | none |
| R9 | `cranelisp-runtime/src/{drop,io}.rs` | `cranelisp-platform` | `IO_TAG_PURE`, `IO_TAG_EFFECT`, `IO_TAG_BIND`, `IO_TAG_PAR` | (a) Narrow the type's home: the IO node tags are the protocol between platform's `CLIO<CL>` builder and the runtime's IO trampoline reduction. Two semi-consumers (platform constructs, runtime reduces) — borderline for `cranelisp-types` per Principle 15. Recommended resolution: **add these constants to the platform facade as published items** (one-line facade addition under "Public consts") — this is NOT facade widening because they were already public on the crate; the facade was incomplete. **`/arch` is willing to commit to this addition**: the four `IO_TAG_*` constants + `IO_EFFECT_RESOURCE_OFFSET` are part of platform's published contract. Edit `design/arch/facades/platform.md` §"Public consts". | trivial (one edit + facade update) |

### Resolution summary

- (a) Narrow the type's home: R4, R5, R6 (likely), R7, R9 → **5 reach-arounds**
- (b) Restructure the consumer: R1, R2, R3 → **3 reach-arounds**
- (c) Remove the dependency: 0
- **STOP-class (no resolution)**: 0

### Facade edits proposed under Phase 2 authority

Per the sprint plan's allowance — `/arch` may edit facade specs in Phase 2 if and only if the edit is to remove an unacceptable entry. The R9 case is the inverse: `IO_TAG_*` constants are missing from the platform facade but already public on the crate. This is an *omission*, not an unacceptable entry. The strict reading of "no facade expansion during the sprint" forbids adding to the facade mid-sprint.

**Resolution path**: `/arch`'s preference is option (1) below; user direction in Phase 2 advance closes this:

1. **Edit `facades/platform.md` §"Public consts" to list the `IO_TAG_*` constants as published BEFORE Phase 3 advance.** This is a Phase 2 facade correction (truth-telling about what's already public) — not a sprint-time expansion. **`/arch` is willing to commit to this addition** as a binding facade entry. The edit is one-line and enforces nothing new — just makes the facade match the implemented public surface.
2. Alternatively: (a)-style narrowing — relocate the constants into `cranelisp-types` (since they cross platform→runtime). This is more invasive and matches Principle 15's letter (multi-consumer constants live in types). It also deletes platform's public surface.
3. Alternatively: keep the constants un-published on platform; expose a Rust constructor API on `CLIO<CL>` that produces tagged i64 values; runtime reads tags via a runtime-internal path (this is structurally cleaner but requires more refactor).

**`/arch` recommends (1)**. It's the smallest correction, makes the platform facade honest, and doesn't expand work. The edit lands as part of the Phase 2 deliverable upon user approval.

**This review does NOT make the edit speculatively.** I have not edited `facades/platform.md` in this Phase 2 pass. `/sprint` should consult `/arch` before advancing if user wants option (2) or (3).

---

## 4. `cargo public-api` adoption plan

### Tool feasibility

`cargo public-api` is **NOT currently installed** on this machine (`cargo public-api --version` errors). It is well-established (used by tokio, rustls, etc.), works on stable Rust, and reads rustdoc JSON output. It produces a textual diff of the public API surface plus per-crate baseline files.

**Feasible: yes.** The tool fits the workspace shape (7 lib crates plus 1 bin), gives us the diff-on-drift signal the sprint needs, and integrates cleanly into CI.

### Wave 1 setup deliverable

`/qa` owns this setup, per the sprint plan. The deliverable is:

1. **Install**: `cargo install --locked cargo-public-api` in CI image and developer environment.
2. **Per-crate baseline files**: One `crates/cranelisp-{crate}/public-api.txt` baseline file per workspace crate, plus one for `src/` (the bin crate has limited public surface but should still be checked). Files are committed to git.
3. **Generation command** (run once at Wave 1; written to a `justfile` or `xtask`):
   ```
   cargo public-api --manifest-path crates/cranelisp-{crate}/Cargo.toml > crates/cranelisp-{crate}/public-api.txt
   ```
4. **CI check** (run on every PR): `cargo public-api --diff --deny=changed,added,removed` against the committed baseline; non-zero exit on drift. Add a step that prints the diff for human review.
5. **Update workflow**: When a PR intentionally changes the public surface (e.g., relocating a type), the developer regenerates the baseline file and commits it alongside the code change. PR review checks that the baseline change matches the FIXME the PR closes.

### Diff-on-drift workflow

When a `/dev` agent changes a public surface:

1. CI runs `cargo public-api --diff` and fails. The diff is in the build log.
2. The agent inspects the diff:
   - **Expected drift** (per the FIXME being closed): regenerate `public-api.txt` for affected crates, commit.
   - **Unexpected drift**: investigate — the change leaked something not in the FIXME (a stray `pub fn`, a wider re-export). Either narrow the change or revisit the design before regenerating.
3. `/review` per-crate verifies: does the regenerated `public-api.txt` match the facade's as-designed surface (modulo aspirational entries like `FQTypeName`)?

### Limitations / things to watch

- `cargo public-api` is **rustdoc-driven**. It catches signature changes, added/removed items, visibility changes. It does NOT catch:
  - Internal behaviour changes (a function body change with same signature is invisible).
  - Re-export indirection (an item re-exported via `pub use` shows as the re-exported path; multiple re-export sites can hide).
- It uses nightly toolchain for rustdoc JSON; `cargo public-api` handles toolchain selection automatically but CI must allow this.
- For the bin crate (`src/`), public-api output is sparse. The facade for `src/` is mostly internal — `cargo public-api` will not catch facade drift between `src/` modules. The `int` facade enforcement is partly manual (per `/review` per-PR check) and partly through how `int` re-exports its own types.

**Conclusion: feasible and sufficient for the sprint's enforcement goal.** No reason to consider an alternative tool.

---

## 5. 95% gate calibration

### Current baseline

S64 close: 953 tests / 932 pass / 21 fail / 6 skip. Sprint gate: ≥885 passing → up to ~47 net-new failures acceptable as carries.

**Today's reality**: a probe `cargo nextest run --workspace` (run during this review) failed to complete the suite because of an early link-failure error (4 fails in `build_confidence` mode-equiv tests at ~3.8s). This may be a transient build issue, a stale ccache, or a local-only failure. `/qa` should sanity-check the baseline before declaring the gate.

**Action item for Wave 1**: `/qa` re-establishes the 932/21/6 baseline and confirms the 21 known-failing list matches what's documented in S64 close. Without that, the gate is not calibrated.

### Pre-classified expected reshapes

Tests likely to need reshaping during this sprint, given the FIXMEs:

| FIXME | Expected test-shape impact |
|---|---|
| 0098 (ResolutionGap migration) | Tests that import `cranelisp_types::CheckError` or `cranelisp_types::ResolutionGap` will need import updates → `cranelisp_typecheck::*`. Mechanical. ~5–10 tests likely. |
| 0099 (GotObserver) | New test surface (additive); no existing tests should break. |
| 0100 (single-consumer relocation) | Same as 0098 — import path changes for consumers. ~5–10 tests likely. |
| 0103 (trace/io_trace relocation) | Tests that import `cranelisp_runtime::io_trace::*` need rewrites → `crate::io_trace::*` (now in `src/`). The 11 failing sketch_port tests + 2 v4_platform tests carried from S64 may include some that will be reshaped further. ~10–15 tests likely. |
| 0104 (PlatformError) | Tests that match on `CranelispError::ModuleError` for platform-load failures will need to match on `CranelispError::Platform(PlatformError::*)` instead. ~3–5 tests likely. |
| 0107 (`#[non_exhaustive]`) | Tests that struct-literal-construct `OwnedPlatformFnDescriptor` from outside `cranelisp-platform` will fail to compile. None expected (descriptors are produced by `manifest_to_descriptors`); but if any exist they need a `From`-style helper. |
| 0108 (display relocation) | Tests that import `cranelisp_backend::display::*` need rewrites → `crate::display::*` or whatever int names the relocated module. ~5 tests likely. |

**Total expected reshape**: ~30–50 tests. These are mechanical (import path changes, error-type pattern rewrites). They should be in scope for the same `/dev` agent that does the migration; they should NOT count as "carries" against the budget.

### Carries vs reshapes — terminology check

The 5% budget is for **net-new failures** carried into S66+. A test that NEEDS A NEW IMPORT PATH is not a failure — it's a mechanical update the migration owner does in the same PR. A test that genuinely cannot pass under the new shape (e.g., a test that depended on a specific implementation detail that the relocation changes) is a carry candidate.

I expect ~10–20 genuine carries from this sprint, mostly from: (1) the 11 sketch_port tests that already fail and may shift further; (2) any test that exercises `cargo public-api` enforcement and needs a freeze-then-update workflow that doesn't fit the test shape.

### Gate verdict

**Confirm: ≥885 passing at sprint close.** The 5% budget is roughly right. If the baseline re-check in Wave 1 reveals fewer than 932 currently passing, `/sprint` should adjust the gate proportionally (95% of whatever the verified baseline is) — not anchor to 932 if reality is different.

**Flag**: FIXME 0098 (the multi-crate ResolutionGap migration) is the riskiest of the seven for the budget. It touches frontend + typecheck + types + int, requires coordinated landing across waves, and breaks the `expand` signature (which has many call sites in `int`). If anything blows the budget it's likely 0098. Worth watching closely in Wave 3 (the pilot wave) since frontend is the pilot and 0098 lands there.

---

## Verdict

- [ ] APPROVE — Phase 3 may proceed
- [x] **APPROVE WITH REVISIONS — Phase 3 may proceed after the listed revisions are reflected in `sprints/SPRINT.md`**
- [ ] PAUSE — sprint scope is wrong; return to Phase 1 reconsideration

### Required revisions

1. **`facades/platform.md` truth-telling correction (R9)** — `IO_TAG_PURE`, `IO_TAG_EFFECT`, `IO_TAG_BIND`, `IO_TAG_PAR`, `IO_EFFECT_RESOURCE_OFFSET` must appear in the platform facade's "Public consts" section. `/arch` proposes the edit (option 1 in §3), but defers the call to user — alternatives are option 2 (relocate constants to `cranelisp-types`) and option 3 (encapsulate behind a Rust API). User picks; `/arch` lands the chosen edit before Phase 3 advances. Without this, runtime's import of these constants is technically a reach-around with no resolution, and Wave 4's runtime work (FIXME 0103) cannot land cleanly.

2. **Wave 1 baseline sanity check by `/qa`** — the 932/21/6 baseline needs re-verification; my probe of the test suite hit early-fail in a `build_confidence` cluster that wasn't in the S64 close note. Either the probe is wrong or the baseline drifted. `/qa` confirms before Wave 1 closes.

3. **Wave structure recommendation in §2 above** — `/sprint` reflects this into Phase 4 SPRINT.md when it advances. Specifically: Wave 2 is types-only (FIXME 0104 Phase 1 + 0100 Phases 1 & 2); pilot in Wave 3 is `cranelisp-frontend` carrying FIXME 0098's frontend + typecheck phases; Wave 4 fans out backend/runtime/platform; Wave 5 is `src/` close; Wave 6 is the test gate. This matches the sprint's hard-constraint of pilot-first / parallel-after.

4. **Reach-around catalogue handoff** — `/sprint` reflects the §3 catalogue's 8 actionable rows (R1–R7, R9; R8 is no-op) into Phase 4 wave plans so each FIXME lands with its consumer-side fixes packaged. The mechanical (b)-class fixes (R1, R2, R3) bundle with whichever wave the affected files are touched in. R4–R6 are (a)-class single-consumer relocations that should be filed as new sub-FIXMEs (or rolled into the parent FIXMEs) so they're tracked.

5. **`cargo public-api` install in Wave 1** — before any code change in Wave 2, the tool must be installed and per-crate baselines committed. Hard gate; this IS Wave 1's deliverable.

### Items NOT requiring revision

- All seven facades are acceptable as binding commitments. No facade entries removed.
- No STOP-class reach-arounds. The sprint scope is sound.
- 95% gate (≥885) is correctly calibrated subject to revision (2).

---

## Phase 2 conclusion

The sprint scope is sound. The seven facades are acceptable. The reach-arounds have resolutions. `cargo public-api` is feasible. The 95% gate is calibrated. Five revisions are required before Phase 3 advances; none are blocking; all are mechanical or coordinative.

**Recommendation: `/sprint` reflects revisions 1–5 into `sprints/SPRINT.md` and advances to Phase 3.**
