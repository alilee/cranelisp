# Sprint 71 Wave 5 — `/review platform` on Wave 4 facade-fold + cross-reference sweep

**Reviewer**: `/review` narrow-deployed to `cranelisp-platform`.
**Date**: 2026-05-28.
**Inputs**: 11 Wave 4 commits (`dac0baa` precursor FIXME 0237 fix, then `91ae2e9 → 5582154 → 8daa029 → 1d3c163 → 7cf0769 → 453ac08 → 8fbfcfc → 1ad0100 → 55c815b`); `design/platform/sprint71-redesign.md` §10 destination table + §8 audit-fold mapping; pre-Wave-4 `design/arch/facades/platform.md` (via git history, since deleted); `crates/cranelisp-platform/src/{lib.rs, adt.rs, schema.rs}` post-fold; `design/arch/bounded-contexts.md` §5; `design/arch/CLAUDE.md` canonical-documents exception line; `design/arch/reviews/sprint-71-wave-2-review.md` (the prior verdict riding into this wave).

## Verdict

**PASS — Sprint 71 may close at Phase 7.**

56/56 platform tests pass (one more than Wave 2's 55, accounting for FIXME 0237's resolution test). Every chunk of the retired 337-line facade has a documentation home in source rustdoc + BC §5. Zero orphaned cross-references in current canonical docs. The exception list in `design/arch/CLAUDE.md` correctly enumerates the three retired facades with sprint references and BC § anchors. Wave 3's F-D1 (FIXME 0236) + F-I1 (FIXME 0237) precursors are dispositioned and resolved. Two Suggestions logged (1 new clippy-doc-warning regression from the fold; 1 methodology-note opportunity); neither blocks close.

## Checklist verdicts (A–J)

### A — Every chunk of the old facade has a documentation home. PASS.

Walked the destination-table spot-checks from design §10 against the post-fold source:

- **Top preamble / target-stating + "owns no runtime state"** (facade lines 1–7) → `bounded-contexts.md` §5 opening paragraph names exactly this framing ("The crate owns no runtime state and no cadence"). ✓
- **§"Public surface (as-designed)" preamble** (facade lines 9–11) → `lib.rs:1–9 //!` preamble carries the dual-audience framing (host binary + platform DLL with named consumer responsibilities). ✓
- **§"Marshaling — CL value wrappers"** (facade lines 13–63) → per-item `///` on `CLInt`/`CLBool`/`CLFloat`/`CLString`/`CLIO` (lib.rs:493–539, 649–655); the CL wrapper family table is in the crate-root preamble (lib.rs:37–44). `CLType` trait rustdoc (lib.rs:585–607) carries the `to_raw` S67 W1 PFR narrowing context. ✓
- **§"Heap-typed values crossed" (CLHeap + CLOwned + CLString)** (facade lines 67–96) → per-item rustdoc on `CLHeap` (lib.rs:878–999 — F5 R3 disposition documented), `CLOwned` (lib.rs:1003–1032 — F1 + F7 dispositions documented inline), `CLString::as_str` (lib.rs:504–521). ✓
- **§"Platform manifest and fn descriptor"** (facade lines 98–135) → `PlatformFn` rustdoc (lib.rs:226–307) with F3 expanded narrative (Principle 18 grounding + BC §5 invariant 6 + IO-trampoline cross-thread context per Decision 0043); `PlatformManifest` rustdoc (lib.rs:443–486) with F4(c) auto-projection `!Send + !Sync` note. ✓
- **§"Host-side descriptors"** (facade lines 137–159) → `OwnedPlatformFnDescriptor` rustdoc (lib.rs:1140–1174) with F4(b) `!Send + !Sync` projection note; `manifest_to_descriptors` rustdoc (lib.rs:1176–1212) with the FIXME 0155 resolution narrative (parse_type_sig / load_manifest are int-side). ✓
- **§"Host context"** (facade lines 161–172) → `HostContext` rustdoc (lib.rs:1060–1094) with F2 source-move documented inline ("Default — deliberately absent"; per audit F2 / design §8) + F4(a) `Send + Sync` annotation. ✓
- **§"Host callbacks"** (facade lines 176–197) → `HostCallbacks` rustdoc (lib.rs:315–354) with per-field rustdoc on `alloc_with_tag` + `validate_schema`; Decision 0031 callback-support forward commitment lands in BC §5 invariant 3 (the cross-surface home). ✓
- **§"declare_platform! macro"** (facade lines 203–216) → `declare_platform!` rustdoc (lib.rs:1314–1448) with the rewritten F6 narrative folded above the existing example block — DLL-author entry point framing, current 5-key + optional schema arm, four-phase emission body, two worked examples. ✓
- **§"Errors" (PlatformError re-export)** (facade lines 218–231) → `pub use cranelisp_types::PlatformError` rustdoc (lib.rs:189–211) with Decision 0042 grounding + Principle 15 external-audience exception note. ✓
- **§"Public consts"** (facade lines 233–244) → `ABI_VERSION` rustdoc (lib.rs:140–162) carries the §6.1 bump-rule enumeration with v1 → v2 history. The `IO_TAG_*` + `HEAP_HEADER_SIZE` + `STRING_HEADER_BYTES` rustdocs are narrow per the design §10 prescription. ✓
- **§"Re-exports from cranelisp-types"** (facade lines 257–269) → F9 disposition in crate-root `//!` (lib.rs:20–29) names Principle 15's narrow scope; per-item `///` on each `pub use` records grounding. ✓
- **§"Bounded-context invariants" 1–7** (facade lines 322–337) → `bounded-contexts.md` §5 "Bounded-context invariants" subsection (BC lines 246–264) carries all seven invariants with one addition (invariant 8 — FQTypeName zero-hit per Decision 0047). The 7 originals are present and grounded per audit-fold map. ✓

Audit `F1–F9` dispositions all have homes — checked separately in H below.

### B — Zero orphaned cross-references. PASS.

`grep -rn "facades/platform.md"` against canonical-document set (facades/, principles/, decisions/, sequences/, bounded-contexts.md, principles.md, per-crate design/, Cargo.toml, README.md):

- `design/arch/bounded-contexts.md:174` — names the retirement event itself ("Sprint 71 retired the standalone `design/arch/facades/platform.md`"). Acceptable historical context. ✓
- `design/arch/CLAUDE.md:15` — the exception-list line. Required and correct. ✓
- `design/arch/decisions/0042-…md:35` — historical reference to "specified, unimplemented" gap (the original context of D42's resolution). Line 46 acknowledges retirement. Acceptable. ✓
- `design/arch/facades/cranelisp-platform-audit-s69.md:3,45,345,348,352,578,607` — the audit document itself; references are the consultation record (Wave 4 commit `1ad0100` deliberately marked this file as historical-by-definition). Acceptable. ✓
- `design/platform/sprint71-redesign.md:7,825,851,855,859,887` — the binding design doc grounding this sprint; references describe Wave 4's source material. Acceptable. ✓
- `design/platform/implementation-slice-s66.md:5,7,152` — historical implementation slice; cross-refs annotated with "retired S71 Wave 4 — canonical surface now …". Acceptable. ✓
- `design/int/implementation-slice-s66.md:376` — annotated with "post-S71 W4 facade retirement". Acceptable. ✓
- `sprints/SPRINT.md` — sprint planning document for this sprint; references describe the work in progress. Acceptable. ✓
- `tests/facade_compliance.rs:46`, `crates/cranelisp-platform/src/lib.rs` (7 `// spec:` test comments via commit `55c815b`), `tests/plan/sprint71-platform.md` — all annotated as retired/historical. ✓
- `design/arch/sprint-65-{phase-2,reshape-phase-2}-review.md`, `design/arch/sprint-66-types-authoring-plan.md` — historical sprint records (Wave 4 commit `1ad0100` explicitly listed as untouched). ✓
- `legacy/`, `archive/` — historical-by-definition, untouched. ✓

**Live citations in current canonical docs that should be redirected**: none found. The post-Wave-4 sweep is complete.

### C — Exception list in `design/arch/CLAUDE.md`. PASS.

`design/arch/CLAUDE.md:15` (the canonical-documents table) reads:

> **Exceptions**: `facades/types.md` is retired (S69 Sub 42); `facades/frontend.md` is retired (S70 Phase B group B3-C); `facades/platform.md` is retired (S71 Wave 4). For all three, source rustdoc (crate-root `//!` + per-item `///`) is the canonical surface; cross-surface narrative lives in `bounded-contexts.md` (§7 for types, §1 for frontend, §5 for platform).

All three retired facades enumerated with correct sprint citations + BC § anchors. The cross-surface-home pointer (BC §5 for platform) is correct.

### D — Tests still passing. PASS.

`cargo nextest run -p cranelisp-platform` → **56 / 56 passed, 0 skipped, 0 failed, 0 ignored** in 0.095s. Up by 1 from Wave 2's 55 — the additional test is the FIXME 0237 fix's exercise (multi-line schema with bad reference reporting correct ParseLoc). No `#[ignore]` per spot-grep.

T23 (workspace-relocated to crate-integration per Option A) still present in `tests/baseline.rs` and passing. Workspace caveat per J below.

### E — 3rd data point in the facade-retirement pattern documented. PASS WITH SUGGESTION.

- `design/arch/CLAUDE.md:15` records the 3-data-point pattern (the exception line itself).
- `design/arch/bounded-contexts.md:174` records "3rd data point of the facade-retirement pattern after `types.md` S69 + `frontend.md` S70".
- `crates/cranelisp-platform/src/lib.rs:22–26` (the `//!` preamble) records "3rd data point of the facade-retirement pattern after `types.md` (S69) and `frontend.md` (S70)".
- `sprints/SPRINT.md` §"Architecture" item 6 + Wave 4 description names the 3-data-point milestone.
- The retirement commit (`453ac08`) message names this explicitly.

**Suggestion**: a methodology-level reflection on what the 3-data-point pattern means for *future* facade work could ride into Phase 7's outcome statement — e.g., "the external-audience-exception case (Principle 15) is now the established trigger for facade-fold; further per-crate facade retirements should follow only when the same criterion is met." Not a finding; methodology folklore opportunity. Logged as S-1 below.

### F — FIXME 0237 fix verification. PASS.

Commit `dac0baa` (the precursor before Wave 4's fold). Verified:

- `schema.rs:175` introduces `let mut field_type_locs: Vec<Vec<Vec<ParseLoc>>>` — pass-1 shadow capture indexed identically to `schema.types[i].variants[j].fields[k]`.
- `schema.rs:199` `parse_type_decl` now returns `(TypeShape, locs, loc)` (3-tuple); locs accumulated into `field_type_locs`.
- `schema.rs:239` pass-2 lookup `let at = field_type_locs[ti][vi][fi];` — uses real captured ParseLoc, not synthetic.
- `schema.rs:226` rustdoc updated: "Errors carry the original ParseLoc captured in pass-1 via `field_type_locs` (FIXME 0237 resolution)."
- `ParseLoc::start()` helper removed entirely (`grep -c "ParseLoc::start" → 0`).
- New test added (counted in the 56 total): the multi-line schema with bad reference on non-first-line reports correct (line, col) per the FIXME body's acceptance criterion.
- `design/arch/fixmes/0237-*.md` deleted (`ls fixmes/ | grep 0237 → empty`).

Clean precursor; the fold then reads the corrected schema source.

### G — FIXME 0236 fix verification. PASS.

The /design platform precursor work corrected design §5.1 / §4.3. Verified:

- `design/platform/sprint71-redesign.md:437–440` now reads: "Returns the **alloc base pointer** as i64 (matches the `CLString` convention — `CLString` stores `payload - HEAP_HEADER_SIZE`; `CLAdt<T>::from_raw` likewise expects alloc base; `read_tag` / `read_field` add `HEAP_HEADER_SIZE` to reach the payload)." The self-contradictory "(NOT the alloc base)" text is gone.
- `design/platform/sprint71-redesign.md:345` also corrected: "the i64 stored in `CLAdt` is the alloc base, matching `CLString`'s convention — see §5.1".
- The Wave 4 fold reads the corrected design and produces correct per-item rustdoc — `lib.rs:367–376` `HostCallbacks::alloc_with_tag` field rustdoc says "Returns the **alloc base pointer** as i64 (matching `CLString`'s base-pointer convention — `CLAdt<T>::from_raw` expects alloc base)" rather than the prior misleading text.
- `design/arch/fixmes/0236-*.md` deleted (`ls fixmes/ | grep 0236 → empty`).

### H — Audit F1–F9 dispositions all closed. PASS.

| F# | Disposition | Verification |
|---|---|---|
| F1 | `CLOwned::into_inner` absent | `grep into_inner lib.rs` → only lines 1017, 1022 (rustdoc records the audit decision; no implementation). `CLOwned` impl block (lib.rs:1037–1043) exposes only `pub fn new`. Drop + Deref only. ✓ |
| F2 | `impl Default for HostContext` deleted | `grep "impl Default for HostContext" lib.rs` → line 1091 (rustdoc reference) + line 1999 (test-string reference). The actual impl block is gone. ✓ |
| F3 | `unsafe impl Send/Sync for PlatformFn` annotated | `lib.rs:267–280` rustdoc has the expanded paragraph covering: read-only-static data; BC §5 invariant 6 (no DLL unloading mid-session); IO trampoline (cranelisp-intrinsics per Decision 0043) cross-thread dispatch. The Principle 18 grounding could be more explicit but the safety reasoning is sound. ✓ |
| F4 | `Send`/`Sync` projections annotated | (a) `HostContext` rustdoc (lib.rs:1080–1086) names the Send + Sync auto-projection via `AtomicPtr<HostCallbacks>` + BC §5 invariant 5. (b) `OwnedPlatformFnDescriptor` rustdoc (lib.rs:1150–1158) names the `!Send + !Sync` auto-projection from `*const u8`. (c) `PlatformManifest` rustdoc (lib.rs:464–472) names `!Send + !Sync` by auto-projection + read-then-discard convention. ✓ |
| F5 | `CLHeap` method names R3 | `lib.rs:929, 949` — `fn inc_rc` / `fn dec_rc` with `&self` receiver. Per F5 R3 rationale in rustdoc (lib.rs:890–899): asymmetric spelling matches `cranelisp-intrinsics` historical names; renaming deferred to a future sprint with consumer-cascade analysis. ✓ |
| F6 | `declare_platform!` macro rustdoc | `lib.rs:1314–1448` carries the rewritten F6 narrative: DLL-author entry point; macro emission contract; S67 W1 PFR + S71 historical refinements; macro arm structure table (7 keys with required/optional/shape/purpose); per-fn 5-required-field enumeration; emission-body 4-phase walk (Phase 0 schema, Phase 1 capture, Phase 2 derive, Phase 3 leak); two worked examples (basic + with-schema). ✓ |
| F7 | `CLOwned` `#[non_exhaustive]` absent | `lib.rs:1024–1032` (`CLOwned` rustdoc) explicitly names "`#[non_exhaustive]` — deliberately absent" and records the audit F7 rationale (single-field RAII; private inner; `#[non_exhaustive]` would add no semantic protection). `#[non_exhaustive]` does not annotate `CLOwned`. ✓ |
| F8 | `CLHeap: CLType + Copy` super-bound | `lib.rs:920` — `pub trait CLHeap: CLType + Copy` unchanged. ✓ |
| F9 | Principle 15 external-audience scope narrow | `lib.rs:20–29` (crate-root preamble) names the exception's narrow scope: `SchedulingClass` + `PlatformError` are the only re-exports, both grounded. BC §5:174 also names the F9 scope-health verification. ✓ |

All audit findings have lived narrative homes in source + BC. Source-move count: 1 (F2). Documentation-fold count: 8 (F1, F3, F4, F5, F6, F7, F8, F9).

### I — Departure verdicts from Wave 3 still hold. PASS.

- **CLAdt alloc-base convention** — Wave 4 reads the post-FIXME-0236 corrected design; per-item rustdoc on `HostCallbacks::alloc_with_tag` (lib.rs:369), `CLAdt` (adt.rs:91–100), `CLString` (lib.rs:504–518) all consistently document "alloc base pointer matches CLString convention". ✓
- **declare_platform! schema_types: parallel ident list** — `lib.rs:1378–1383` rustdoc names "the proc-macro upgrade is feasible — tracked by FIXME 0238 as a future refinement". FIXME 0238 exists (correct frontmatter, `target: /dev platform`). The Wave 3 ask is met. ✓
- **schema/adt module visibility** — `lib.rs:134, 137` declare `mod schema;` + `mod adt;` (private); `lib.rs:135, 138` `pub use` at crate root. Unchanged from Wave 2; baseline regen confirms `--simplified` emission is stable. ✓
- **T25 panic-message verification (source-text contract)** — Wave 4 did not touch tests/contracts; T25 still passes. The Wave 3 Suggestion F-D4 (amend FIXME 0235 to include integration-time R1-gate-fires verification) was not actioned in Wave 4 — but Wave 3 recommended this could ride to Phase 7 or amend in-place. Logged as S-2 below.

### J — Workspace caveat handling. PASS.

- `src/platform.rs:182–192` — HostCallbacks initializer extended with `alloc_with_tag: cranelisp_platform::null_alloc_with_tag` + `validate_schema: cranelisp_platform::null_validate_schema` + multi-line `// FIXME(0229)` comment. Unchanged from Wave 2; Wave 4 did not touch this surface.
- `crates/cranelisp-exe-bundle/src/lib.rs:94–104` — same shape; same FIXME comment.
- Workspace-wide `cargo build` not run per the brief's narrow exit gate + FIXME 0222 (S70 typecheck cascade carry blocks workspace build).
- `cargo check -p cranelisp-platform` and `cargo nextest run -p cranelisp-platform` and `cargo clippy -p cranelisp-platform` all green/expected (clippy carry below).

**Build posture**: verified `-p cranelisp-platform`; workspace-wide build deferred per FIXME 0222.

## Findings

### Blocker
None.

### Important
None.

### Suggestion

**S-1 — Methodology reflection on the 3-data-point facade-retirement pattern.**

The three retirements (`types.md` S69 / `frontend.md` S70 / `platform.md` S71) all share one trigger: the crate's facade is structurally equivalent to its public Rust API + per-item rustdoc. For `types.md` the trigger was "facade types live with behaviour" (Principle 15); for `frontend.md` and `platform.md` it was the same plus the external-audience case (DLL authors, in platform's case).

A methodology-level reflection — perhaps a single paragraph in the Phase 7 outcome statement, or filed as a small `/sprint` methodology note — could codify when *future* facade-fold work is appropriate vs. when a facade should be kept. The criterion seems to be: when the audience of the facade is the same audience that reads the source rustdoc (no separate cross-crate-mediator audience). Logged as a methodology opportunity, not a finding.

**S-2 — FIXME 0235 amendment for integration-time R1-gate verification.**

Wave 3's F-D4 recommendation: amend FIXME 0235 body to include "verify R1 gate fires with documented message at integration time" as an acceptance criterion. Wave 4 did not touch FIXMEs (its scope was facade fold + sweep), so this carries forward. Phase 7 close is the natural moment to action this — or `/sprint` may relay to the host-wiring sprint when it's planned. Not blocking.

**S-3 — 2 new clippy `doc list item without indentation` warnings introduced by the Wave 4 fold.**

`cargo clippy -p cranelisp-platform` now reports 3 warnings (up from Wave 2's 1):

- `crates/cranelisp-platform/src/lib.rs:898:5` — `doc list item without indentation` (in `CLHeap` rustdoc, the F5 R3 explanation paragraph)
- `crates/cranelisp-platform/src/lib.rs:899:5` — same; adjacent line
- `crates/cranelisp-platform/src/lib.rs:1214:6` — pre-existing S65-vintage `result_large_err` on `manifest_to_descriptors` (the Wave 2 carry)

The two new warnings are cosmetic — multi-line continuation of a list item that clippy expects indented. The fix is trivial (4-space indent the continuation lines). Not blocking; not worth a FIXME; suggest `/dev platform` ride this with the next cosmetic pass on the file. Logged here for visibility.

## FIXMEs filed by this review

None.

The two open Suggestions (S-1 methodology reflection, S-2 amend 0235) and one cosmetic (S-3 clippy doc-indent) do not warrant durable FIXME records — they ride into Phase 7 outcome naturally and `/sprint` can dispose at close.

## Configuration consistency

Post-Wave-4 documentation state is internally consistent:

- Source rustdoc carries the per-item narrative the design §10 destination table prescribed.
- BC §5 carries the cross-surface narrative (audience, RC discipline, schema mechanism, ABI versioning, future host-wiring story, conformance triad coverage holes, 8 bounded-context invariants).
- The retirement event is named exactly once in BC §5:174 ("Sprint 71 retired the standalone `design/arch/facades/platform.md`") and once in the CLAUDE.md exception line (§"Canonical documents").
- Audit document (`facades/cranelisp-platform-audit-s69.md`) is left intact as historical-consultation-record per Wave 4 commit message.
- The 3-data-point pattern is named in 4 places (CLAUDE.md, BC §5, lib.rs preamble, SPRINT.md).

## Sprint outcome readout — for Phase 7

**Sprint 71 deliverable posture**: complete. The platform crate's audit is drained (F1–F9 closed); the new ADT-marshaling surface (`CLAdt<T>` + marker-type pattern + schema parser + grown HostCallbacks + ABI v1 → v2 bump) is implemented and tested (56/56 platform tests pass); the facade is retired (3rd data point of the pattern); the cross-reference sweep is complete; documentation cohesion is strong (source rustdoc + BC §5 carry the entire narrative).

**Phase 7 outcome should specifically note**:

1. **3rd data point in the facade-retirement pattern landed cleanly** — S-1 above is the opportunity to codify methodology forward.
2. **Workspace-wide build remains deferred** per FIXME 0222 (S70 typecheck cascade carry); the platform-crate-only exit gate held. The host-wiring sprint (FIXMEs 0229–0235) will land on workspace-wide-green ground once 0222 resolves.
3. **R1 wired-or-panic gate is in place** but the production verification is "construction-path call into a wired host" — only verifiable at FIXME 0229 / 0235 integration time. S-2 above (amend 0235 to include the gate-fires verification) is the close-time follow-up.
4. **FIXME 0238 (`declare_platform!` proc-macro upgrade)** carries forward the macro shape's "tracked future refinement" claim — durable record, no urgency.

Sprint may close at Phase 7.

## Verdict — Sprint 71 may close at Phase 7

**PASS.** No Blockers. No Important findings. Three Suggestions logged (1 methodology, 1 close-time follow-up, 1 cosmetic). Phase 7 close can begin immediately.
