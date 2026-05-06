# Sprint 65 Wave 4b — cross-cutting check across the 9 W4a implementation slices

**Status.** Final.
**Author.** /arch, 2026-05-07.
**Reads.** the 9 W4a implementation slices (`design/{frontend,typecheck,backend,primitives,intrinsics,platform,runtime,int}/implementation-slice-s66.md` + `tests/plan/implementation-slice-s66.md`); `design/arch/principles/16-punctuation-symbols-are-not-special.md` (filed `a5a9339`); `design/arch/decisions/{0010,0011,0027,0030,0031,0035,0040,0041,0042,0043}.md`; `design/arch/principles/{14,15}-*.md`; W3 sweep at `5b25663` + observer-encapsulation follow-up at `b93b34f`.

**Scope.** Slice-level cross-check. The facade-level cross-Decision/Principle audit was the W3 sweep at `5b25663`. W4b verifies bilateral pairing across the W4a slices, confirms each slice reflects the relevant active Decisions, and records two W4a-resolved questions (D38/D39, `not` primitive).

---

## 1. Bilateral dependency check

Each W4a slice authored a "Cross-crate dependencies (bilateral)" table. W4b verified each entry against the named partner slice's table. Status legend: **P** present in both slices; **A** asymmetric (one side names; other side does not name the reciprocal); **MoB** missing-on-both (real cross-crate dependency neither slice tracks).

### 1.1 Pair matrix (high-traffic edges)

| # | Pair | Source row | Partner side | Status |
|--:|---|---|---|---|
| 1 | frontend `expand` consumes `&SymbolTables<C, L>` | frontend row 7, 8 | typecheck §4 row "SymbolTables alias home"; int §4 row "SymbolTables alias consumer" | P |
| 2 | frontend → int: `expand` migration + `MacroResolver` deletion | frontend row 7, 17 | int row 35, 48 | P |
| 3 | typecheck `check_form` mutability-pivot to `&SymbolTable` | typecheck row 1, 12 | int row 7, 49; frontend §4 row "SymbolTables alias" | P |
| 4 | typecheck → int: `CheckResult`/`CheckError`/`ReplSnapshot` migrate from types into typecheck | typecheck row 6, 9 | int row 49 (consumed surface alignment); types-slice mirror (verify-only) | P |
| 5 | typecheck → int: `process_form` Gap pattern-match | typecheck row 1 (acceptance) | int row 3, 4 | P |
| 6 | backend `compile_to_module` returns `Result<(), CompilationError>` + direct writes | backend row 1, 2 | int row 8, 9, 12 | P |
| 7 | backend `Code` migrate to backend home | backend row 3 | int row 10, 11 | P |
| 8 | backend `display.rs` migrate-out to int | backend row 7 | int row 25, 26 | P |
| 9 | backend `GotObserver` + `register_got_observer` extension | backend row 6 | int row 23, 52; qa §4.2 | P |
| 10 | backend Cargo.toml dep flip (drop runtime, add primitives + intrinsics) | backend row 10 | primitives row 12; intrinsics D13; runtime-retiring row 18 | P |
| 11 | backend `IntrinsicSymbol` array — primitives portion | backend row 11 | primitives row 11 | P |
| 12 | backend `IntrinsicSymbol` array — intrinsics portion | backend row 11 | intrinsics D13 | P |
| 13 | backend trait-knowledge map deletion (D43 / Principle 16) | backend row 8 | primitives row 9 (`cranelisp_op_*` delete); stdlib audit (FIXME 0150 Phase 4) | P |
| 14 | primitives ↔ intrinsics — single-commit workspace skeleton lockstep | primitives row 1, 2 | intrinsics D1; runtime-retiring row 18 | P |
| 15 | intrinsics IO trampoline + IoObserver | intrinsics D7, D8 | int row 20, 21 (registration + ring buffer); platform §4 row 4 (HeapString layout governance) | P |
| 16 | intrinsics `consume_trace_call` carve-out → int trace | intrinsics D4 | int row 22; runtime-retiring row 3 carve-out | P |
| 17 | runtime-retiring → primitives + intrinsics + int (file moves) | runtime-retiring rows 1–14 | matching rows in destination slices | P |
| 18 | runtime-retiring workspace member deletion + runtime CLAUDE.md vacuum | runtime-retiring row 17, 18, 19 | primitives row 14; intrinsics D12; backend row 10 | P |
| 19 | platform PlatformError signature-change | platform row 1, 2 | int row 27, 28 (consumer-side `format_error` arm + `load_platform_dll` reshape); types-slice (Phase 1 mirror) | P |
| 20 | platform `parse_type_sig`/`load_manifest` placement | platform row 8, 9 (verify) | int row 28 (load_platform_dll reshape) | P |
| 21 | int — gap orchestration retry loop | int row 3, 4, 5, 36 | frontend row 7 (Gap producer); typecheck row 1 (Gap producer) | P |
| 22 | int reach-around R4 — `CacheWritePacket` carries `ObjectArtefact` | int row 29 | backend row 14 | P |
| 23 | int reach-around R5 — `generate_startup_object` to exe-bundle | int row 30 | backend row 13 (`load_object` shape); runtime-retiring (linker archives) | P |
| 24 | int reach-around R6 — `TracedFnInfo` int-side home | int row 22 | backend slice (verify no duplicate; OQ-5) | P (with verify) |
| 25 | qa — public-api baselines per crate | qa §1, §6 | each /design slice §5 references baseline-generation step | P |
| 26 | qa — got_trace.rs e2e file | qa §4.2 | backend row 6; int row 23 | P |
| 27 | qa — platform_errors.rs + platform_abi.rs | qa §4.5, §3.5 | platform row 2; int row 27, 28 | P |
| 28 | qa — stdlib_trait_impls.rs (load-bearing for D43 Phase 4) | qa §4.8 | primitives row 9; backend row 8; intrinsics §"trait impls"; runtime-retiring row 12 | P |
| 29 | qa — process_form_dispatch.rs + retry path | qa §3.8, §4.1 | int row 3 §6 (stress); frontend row 7 §5 | P |

**Result.** 29 bilateral pairs verified. **All present.** No asymmetric pairs requiring slice edits. No missing-on-both pairs. No STOP-class findings.

### 1.2 Notes

- The /qa slice is uniform on the `/design (crate) §5 — test surface impact` mirror; every /qa cross-crate row corresponds to a Test surface impact row in the named slice. The W4a authoring discipline succeeded on bilateral coverage.
- The runtime-retiring slice's coordination role (5 sister slices, 9 dependency rows) is the most fan-out edge in the matrix — all 9 entries paired cleanly with destination slices.
- Pair #24 (`TracedFnInfo` duplicate) is recorded as **P (with verify)** — int slice OQ-5 surfaces the question; backend slice does not enumerate a duplicate today; if implementation surfaces one, the int slice files a coordination FIXME at S66 enactment time. Not a substantive gap.

---

## 2. Cross-Decision / cross-Principle audit

Active Decisions: 0010, 0011, 0027, 0030, 0031, 0035, 0040, 0041, 0042, 0043. Plus Principles 14 (FFI), 15 (facade types live with behavior), 16 (punctuation symbols not special — `a5a9339`).

### 2.1 Decision × slice matrix

Cell content: ✓ slice substantively reflects; — peripheral; n/a not relevant.

| Decision | frontend | typecheck | backend | primitives | intrinsics | platform | runtime-retiring | int | qa |
|---|---|---|---|---|---|---|---|---|---|
| 0010 base-pointer ABI | n/a | n/a | n/a | — | ✓ (D2) | ✓ (row 4 layout) | — | n/a | n/a |
| 0011 embedded drop-glue ptr | n/a | n/a | n/a | n/a | ✓ (D4) | n/a | — | n/a | n/a |
| 0027 G8 lands before G9 | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a (sequencing-only — historical) |
| 0030 form-by-form scheduler | ✓ (Reads) | n/a | n/a | n/a | n/a | n/a | n/a | ✓ (mutual-import handling) | ✓ (regression test) |
| 0031 one JitModule per batch | n/a | n/a | ✓ (row 4 cardinality) | n/a | n/a | n/a | n/a | ✓ (lifecycle row) | ✓ (lifecycle test) |
| 0035 Code enum | n/a | n/a | ✓ (row 3) | n/a | n/a | n/a | n/a | ✓ (row 10) | n/a |
| 0040 trace + io_trace relocate | n/a | n/a | n/a | n/a | ✓ (D8 + D40 cite) | n/a | ✓ (rows 7, 10) | ✓ (rows 21, 22) | ✓ (§4.4) |
| 0041 per-symbol JIT direct writes | n/a | n/a | ✓ (rows 1, 2, 4) | n/a | n/a | n/a | n/a | ✓ (rows 8, 9, 12, 14) | ✓ (§3.4, §3.8) |
| 0042 PlatformError + ErrorLocation | n/a | ✓ (row 13) | ✓ (row 15) | n/a | n/a | ✓ (rows 1, 2) | n/a | ✓ (rows 27, 28) | ✓ (§4.5) |
| 0043 runtime split | ✓ (Reads) | n/a | ✓ (rows 8, 9, 10, 11) | ✓ (entire slice) | ✓ (entire slice) | ✓ (row 4 verify) | ✓ (entire retirement) | ✓ (rows 17, 18, 19, 31) | ✓ (§4.8) |

**Result.** Every active Decision is reflected in every slice where it is in-scope. No substantive gaps. D27 is no-op for S66 (sequencing-only / historical). Each slice's own concerns map cleanly to its decision register.

### 2.2 Principle × slice (focused)

| Principle | frontend | typecheck | backend | primitives | intrinsics | platform | int | qa |
|---|---|---|---|---|---|---|---|---|
| 14 — FFI layout discipline | n/a | n/a | — | ✓ (row 8 ABI consciousness) | ✓ (D2 layout preservation) | ✓ (row 4 ABI_VERSION-governed reads) | n/a | n/a |
| 15 — facade types live with behavior | ✓ (rows 9, 10) | ✓ (rows 6, 9, 20) | ✓ (rows 3, 5) | n/a | n/a | ✓ (row 1 inline-exception) | ✓ (rows 10, 47) | ✓ (§1) |
| 16 — punctuation symbols not special | n/a | n/a | ✓ (rows 8, 9) | ✓ (rows 9, 11) | n/a | n/a | n/a | ✓ (§4.8) |

**Principle 16 finding.** Principle 16 was filed `a5a9339` AFTER all 9 W4a slices were authored. None of the slices cite it by name. **Substantive content is fully reflected** in operator-shaped slices via D43 — backend rows 8 + 9 (delete trait-knowledge maps + rename `operators.rs` → `primitives_inline.rs`); primitives rows 9 + 11 (delete `cranelisp_op_*` duplicates); qa §4.8 (stdlib trait-impl audit as the regression guard). The architectural commitment Principle 16 elevates is operationally tracked. **Not flagged for slice edits** — the substance is present; the principle citation is editorial. Future slice authoring (S67+) cites Principle 16 directly.

---

## 3. Resolved W4a questions (recorded)

### 3.1 D38 / D39 status (int slice OQ-1)

**Resolution.** D38 + D39 stay LEGACY. Their architectural commitment is settled: outcomes are embodied in facades + per-crate design docs; the Decisions move to `design/arch/legacy/decisions/`. The int slice's deeper question — struct extraction vs decomposition for `SharedState` — is **FIXME 0109** (deferred to S67+). S66 adopts the contract D38 commits to (worker-shareable subset is identifiable in source; per-symbol mutability discipline) without performing the physical struct extraction. No CLAUDE.md edits needed; the legacy classification is correct. Int slice's Wave C (`SharedState` formal extraction) remains in S66 scope as "shape pivot" — the *full* `session_v4.rs` decomposition defers to S67+.

### 3.2 `not` primitive (primitives slice OQ-3)

**Resolution.** Spec is authoritative (`spec/appendix-a-builtins.md:79` lists `not` as `(Fn [Bool] Bool)`). Source has a gap: backend special-cases via inline substitution (`crates/cranelisp-backend/src/operators.rs:64`) but no primitive entry exists. **FIXME 0150 reshape** (`a5a9339`) closes the gap by directing /qa to spec authority for primitive coverage; every spec primitive requires both inline-path + mappable-path test. The `not` gap surfaces naturally during the test pass. No spec audit work required in S65; FIXME 0150 + Principle 16 cover the future shape. No slice edits.

---

## 4. Concurrency / atomicity / ordering at slice level

The W3 sweep + follow-up `b93b34f` encapsulated the IO and GOT observer registration concurrency contracts behind their APIs. Verification: slice-level concurrency questions surfaced by W4a authoring.

| Slice | Concurrency surface | Status |
|---|---|---|
| intrinsics D8 | `register_io_observer` last-writer-wins under happens-before | Encapsulated by API per `b93b34f`; slice acceptance criteria (test 3 — concurrency) names the contract. Acceptable. |
| backend row 6 | `register_got_observer` atomic-replace; OQ-1 raises ordering-with-emission question | OQ-1 is implementation-internal (relaxed-load semantics at emission site); the facade-level contract is encapsulated. Implementation question for S66, not facade gap. Acceptable. |
| qa §3.6, §4.2, Q3 | loom/shuttle stress test for both observers | Test infrastructure question; /dev (intrinsics + backend) chooses. Not a facade contract gap. Acceptable. |
| int row 1, 2 | `Arc<SharedState>` shared across worker threads | Shape is settled at facade (`facades/int.md` §"SharedState"); slice's Wave C executes. No concurrency contract question; embodiment work. Acceptable. |
| int row 6 | Phase 0 brief-window discipline (`entry().or_default()` followed by RefMut drop before scheduler dispatch) | Documented per master-design §6.1; slice Wave C row 6 executes. Acceptable. |

**Result.** No facade-level contract gaps. All concurrency surfacing in W4a slices is implementation-question class, encapsulated by APIs, or already settled at master-design level. **No STOP-class concurrency findings.**

---

## 5. Substantive findings

**None STOP-class.** The slice-level cross-check is clean.

Editorial / informational notes (non-blocking):

1. **Principle 16 is filed AFTER slice authoring.** Slices substantively comply via D43 reflection but do not cite Principle 16 by name. S67+ slice authoring should cite directly.
2. **Pair #24 (TracedFnInfo) is "P with verify"** — implementation may surface a duplicate type that the backend slice doesn't enumerate today; int slice OQ-5 carries the verification question forward to S66 enactment. Not a substantive gap.
3. **D38/D39 + `not` primitive resolutions are recorded** in §3 above per /sprint determination.
4. The backend slice's W4a commit (`5e03453`) accidentally absorbed `design/intrinsics/implementation-slice-s66.md` into a parallel `git add` race; the intrinsics file IS on HEAD and the user accepted the misattribution. Not a substantive issue; recorded for provenance.

---

## 6. Verdict

**W4b cross-cutting check passes.** Bilateral dependency coverage is complete; cross-Decision / cross-Principle audit confirms full reflection across in-scope slices; D38/D39 + `not` resolutions recorded; concurrency contracts encapsulated. No STOP-class gaps. No re-entry to Phase 2 needed. The 9 W4a implementation slices are coherent as a sprint-input bundle for /sprint's S66 wave plan.

---

## Cross-references

- Each W4a slice — bilateral dependency tables verified
- `design/arch/principles/16-punctuation-symbols-are-not-special.md` (`a5a9339`)
- `design/arch/decisions/{0010,0011,0027,0030,0031,0035,0040,0041,0042,0043}.md`
- `design/arch/principles/{14,15}-*.md`
- `design/arch/sprint-65-reshape-phase-2-review.md` §3 — slice template authority
- `sprints/SPRINT.md` Wave Phase 4 W4b — this artefact's authoring wave
- W3 sweep `5b25663` — facade-level cross-check (this W4b's predecessor)
- W3 follow-up `b93b34f` — observer registration concurrency contract encapsulation
