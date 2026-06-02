# Sprint 75: `cranelisp-backend` alignment + facade retirement (7th + 8th data points)

**Status**: COMPLETE — Phase 6 waived (no language-visible change); Phase 7 close user-approved 2026-06-02 (commit on main)

**Goal**: Run `cranelisp-backend` — the heaviest crate (19.3k LOC, 23 files,
2008-line baseline) — through the full four-step alignment: absorb the
types(S69)+frontend(S70) input cascade, conform both facades exactly, streamline
the interior the narrowing exposes, and retire `facades/backend.md` +
`facades/backend-cache.md` into source rustdoc + `bounded-contexts.md §3` (7th +
8th retirement data points). All four steps this sprint, **organized into more
waves than S69–S74** to keep the heaviest crate reviewable. This is the
dependency-correct prerequisite that unblocks `int` (the last crate).

## Why backend (crate selection — forced by the rule)

The alignment rule: *the crate with no unconformed dependencies.* Backend's only
Cranelisp deps are `cranelisp-types` (conformed+retired S69) and
`cranelisp-intrinsics` (conformed+retired S74) — both done. `cranelisp-primitives`
is **already dep-banned** from backend's `Cargo.toml` (S68 structural invariant,
Decision 0048; enforced by `tests/no_primitives_dep.rs`). So backend is the only
newly-eligible crate, and conforming it unblocks int's host-wiring.

Unlike S73 (primitives, doc-only) and S74 (intrinsics, mostly doc), this is **real
source work**: a known **41-error lib cascade / 202-error lib+tests cascade** plus
the heaviest facade-conform + retirement fold yet.

## The four-step alignment (S69–S74 pattern), with corrected terminology

| Step | Work | Notes |
|---|---|---|
| 1. **Absorb** input-crate changes | Fix the 41/202-error types+frontend cascade; new `Expr::ConstrADT` lowering arm + absorb the S70 `ResolvedCall` payload reshape (4 existing variants, not a new one — Phase-2 Rev 1) | Real source work; gets the crate compiling |
| 2. **Conform** the facade(s) | Public surface matches the documented facade **exactly** — nothing beyond it. Rotate the boundary to the documented shape (D41 — FIXME 0221) AND narrow away every `pub` item the facade doesn't document (§6 ABI guardrail governs externs). 0244 backend half; `:407` doc fix. Baseline regen. | Two facades: `backend.md` + `backend-cache.md` |
| 3. **Streamline** the interior | Remove dead code + duplication **inside** the crate that becomes visible once the surface is narrowed by Step 2 (e.g. a now-`pub(crate)` fn with no callers; two paths that were both `pub` now clearly duplicate). Clippy. | Distinct from Step 2 — interior, not surface |
| 4. **Retire** the facade(s) | Fold `backend.md` + `backend-cache.md` → source rustdoc (`//!` + per-item `///`) + `bounded-contexts.md §3`; drop both from `facade_compliance.rs` (source = definition; rustdoc = rationale) | 7th + 8th data points |

## Wave organization (sizing — the heaviest crate, more waves)

Backend is 19.3k LOC vs intrinsics' 215-line baseline; the per-wave granularity of
S69–S74 won't contain it. Provisional wave shape (refined in Phase 4 after `/arch`
+ `/design backend`):

- **W1 — Absorb (Step 1).** `/dev backend` fixes the 41 lib + ~161 test cascade
  errors + the two new-codegen arms. Gate: `cargo check -p cranelisp-backend
  --tests` green; `cargo nextest -p cranelisp-backend` green standalone.
- **W2 — Conform boundary (Step 2a).** `/dev backend` rotates the boundary to the
  documented shape: D41 `compile_to_module` (FIXME 0221) + `produce_disasm`; free
  `load_object`; `Linker::get_symbol → Result` (D37); 0244
  backend-half `Code::Primitive` deletion. Baseline regen #1.
  **`compile_to_object` DELETES** (not "free `compile_to_object`") — the `lib.rs:821`
  stub (returns `unimplemented!()`, cites the never-filed FIXME 0184) is removed; the
  object path is `compile_to_module::<ObjectModule>` + caller `finish().emit()` (the
  three-entry codegen boundary, per the /arch re-ruling below + `compile-to-module.md` §2 + D23).
- **W3 — Conform surface (Step 2b).** `/dev backend` narrows every `pub` not
  documented in the two facades to `pub(crate)` **under the §6 ABI guardrail**.
  Backend has **zero** Rust externs of its own (grep-confirmed), so the §6 guardrail
  is moot for backend-owned emitted-call symbols. **Per the /arch final-state re-ruling
  below, additionally NARROW → `pub(crate)`:** `jit::intrinsic_symbols`,
  `exe::generate_startup_object`, and `compiler::got_data_symbol_name` (the duplicate /
  internal naming primitive — `cache::object::got_data_symbol_name` is its re-export;
  collapse to one `pub(crate)` home). Each of the three names a linker symbol by string →
  **document its symbol-name + relocation ABI in `///` before the visibility drop** (see the
  re-ruling's "Linker-symbol-ABI documentation owed" list). All three leave int red (S77).
  Cache root re-export narrowing (near-free — int uses only submodule paths). Baseline
  regen #2. `/design backend` keeps the facades exactly matched (incl. `:407` fix).
- **W4 — Streamline (Step 3).** `/dev backend` removes dead code + duplication the
  narrowing exposed. Clippy clean.
- **W5 — Retire (Step 4).** `/design backend` + `/arch` fold both facades →
  rustdoc + BC §3; `/qa` drops both crates from `facade_compliance.rs`.
- **W6 — Review.** `/review backend` change-set review against facades + §6
  guardrail + Phase-2 rulings.

*(W2/W3 may merge or re-split per /arch's Phase-2 read; gated with the user.)*

## Architecture review (Phase 2)

**Reviewer:** `/arch` · **Date:** 2026-06-01 · **Verdict: APPROVE-WITH-REVISIONS.**

The four-step alignment is technically coherent, the wave decomposition is sound, and the scope is genuinely deliverable as crate-narrow-green with int red. Eleven enumerated revisions below sharpen the boundary-rotation accounting, the §6 narrow set, and two stale-facade fixes. None is a blocker; all are W1–W5 instructions, not pre-implementation arch edits. One arch-doc edit was made now (the `decisions/` drain on D41/0244 is named as W5, not enacted). No `cranelisp-types` change is owed — the DAG check (Q2) passes: every type the two new codegen arms need already exists in `cranelisp-types`.

### Verdict per the nine review questions

**Q1 — Four-step coherence + wave structure: SOUND. Keep 6 waves; do NOT merge W2+W3.**
Absorb → conform-boundary → conform-surface → streamline → retire is the correct ordering for the heaviest crate, and it is the established S69–S74 pattern applied at larger scale. The W2/W3 split (conform-boundary vs conform-surface) MUST be kept distinct, not merged, for a structural reason specific to backend: W2 is a *shape rotation* (signatures change — `compile_to_module` return type, `Code` variant slimming, `Linker::get_symbol` → `Result`, `Code::Primitive` deletion) that produces baseline regen #1 and is reviewed as semantic edge evolution; W3 is *visibility narrowing* (`pub` → `pub(crate)`) that produces baseline regen #2 and is reviewed under the §6 ABI guardrail. These are different review lenses on different diffs. Collapsing them would bundle a signature-semantics diff with a visibility diff into one baseline regen, defeating the side-by-side facade-diff discipline (`design/arch/CLAUDE.md` §"Baseline-diff discipline"). The two-regen plan is correct. All four steps in one sprint is deliverable **because the acceptance bar is crate-narrow green** (int stays red, re-wires in S77) — that is what makes the boundary rotation landable without a cross-crate cascade this sprint. No descope required.

**Q2 — The two "new codegen arms": absorb-step work, NOT a hidden feature. DAG check PASSES.**
Verified against source. `Expr::ConstrADT { type_name, tag, fields, span, inferred_type }` exists in `cranelisp-types/src/ast.rs:267` and its semantics are fully specified in `facades/backend.md` §"Constructor codegen" (lines 536–544): it lowers to alloc+tag+stores via the single handler `compile_constr_adt`, replacing the four-function family (`compile_data_constructor_call`, `compile_data_constructor_as_value`, `nullary_constructor_tag`, `data_constructor_info`) still present in source at `compiler/literals.rs:126/190` + `compiler/apply.rs:343/558`. This is the constructor-as-Def collapse (D47 + Decision 44/45 ctor shape) landing in backend — **absorb work**, not a new feature; the emission target is documented. The "new `ResolvedCall` variant" framing in the Step-1 table is **imprecise and must be corrected** (Revision 2): `ResolvedCall` has exactly four variants (`TraitMethod`, `SigDispatch`, `AutoCurry`, `BuiltinFn` — `cranelisp-types/src/check.rs:106`) and backend already matches all four (`compiler/apply.rs:126/255/281/288`). The E0004 the cascade cites is a *non-exhaustiveness* error surfaced when the S70 reshape changed variant *payloads* (e.g. `TraitMethod.impl_type: FQTypeName`, `mangled_name: JitSymbol`) — the arm exists but its bindings no longer typecheck, OR a sibling `Expr`/`Pattern` match lost exhaustiveness. It is binding-level absorb work against an existing variant, not a new emission path. **DAG check:** every type the arms consume (`Expr`, `Pattern`, `MatchArm`, `DefKind::Constructor`, `ResolvedCall`, `FQTypeName`, `JitSymbol`) is already in `cranelisp-types`. No new cross-crate interface is owed; `cranelisp-types` is not touched this sprint.

**Q3 — D41 rotation (FIXME 0221): SOUND to land now; does NOT strand int. Backend-authored confirmed. S70 Phase B amendment operative.**
`CompilationArtifacts` and `produce_disasm` are **backend-authored** — `facades/backend.md` §"Types originated here" (line 465) places `CompilationArtifacts` in `crates/cranelisp-backend/src/artefact.rs`, and `produce_disasm` is a backend free function (§"Free functions", lines 24–27). Neither is a `cranelisp-types` type; the DAG is not inverted (backend never names int's `Introspection` — confirmed §"Return shapes" line 55 + BC §3 "What crosses the boundary"). The S70 Phase B amendment (Introspection stays in int; D41 #3 Introspection direct-write retracted; backend returns artefacts *by value* and the caller composes) **is operative** in both the facade (lines 45–47, 55, 351, 373) and BC §3 ("a value-returned `CompilationArtifacts` … backend does not name the integration-layer `Introspection` type"). Landing the rotated boundary while int's `worker.rs` call sites stay red is the *intended* sequencing: int re-wires the conformed shape once in S77 against a stable target, incurring no churn — the alternative (a transitional shim) would violate Principle 8. The rotation is correct now.

**Q4 — 0244 `Code::Primitive` deletion: backend CAN delete the variant while int is red. Cascade is contained in backend + (red, deferred) int — but with a caveat the plan must absorb (Revision 4).**
Trace of every `Code` match site (verified): backend constructs/matches `Code::Jit`, `Code::Linker`, `Code::Primitive` only within `crates/cranelisp-backend/src/code.rs` (constructors at :126/:132, the `ptr()` accessor at :150–151, Debug at :104–106, unit tests at :244–305) and in artefact.rs/lib.rs/jit.rs *doc-comments*. **int matches `Code::Jit { ptr, .. }` and `Code::Linker { ptr, .. }` at `src/code.rs:114/120` but NEVER matches `Code::Primitive`** — so deleting the `Primitive` variant does not break any int match arm. The 0244 backend-half is therefore contained: backend deletes the variant, its `ptr()` null-arm, and the unit-test arms; no int match arm references it. **Caveat (Revision 4):** the SAME W2 wave also slims the `Code::Jit { jit, ptr }` / `Code::Linker { linker, ptr }` variants to the facade target `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)` (no per-variant `ptr` — GOT is single source of truth; §"Code" lines 95–111 + BC invariant 3). That slim DOES reach int — `src/code.rs:114/120` destructures `{ ptr, .. }`. int is red, so this is fine, but the wave plan must EXPLICITLY note that the `Code` variant-payload rotation (not just the `Primitive` deletion) is part of W2's red-leaving boundary change int re-wires in S77. Do not let W2 land a half-rotation that keeps `ptr` to "avoid touching int" — that would be a Principle-8 interim shape. Both the `Primitive` deletion and the `ptr`-field removal land together in W2.

**Q5 — §6 emitted-call-ABI guardrail: binary guidance below. The honest narrow set is the cache root re-export duplicates + internal codegen helpers, NOT externs. Backend has ZERO Rust externs of its own.**
Source check refines the brief: `grep` for `#[export_name]` / `#[no_mangle]` / `pub extern` in `crates/cranelisp-backend/src/` returns **nothing**. Backend produces/consumes linker symbols by exactly three mechanisms, and their Rust visibility is independent of the linker symbols they name:
- `jit::intrinsic_symbols()` (jit.rs:99) — enumerates *intrinsic* targets by string for `JITBuilder::symbol` registration. **int consumes it by Rust path** at `worker.rs:3545`.
- `exe::generate_startup_object` (exe.rs:31) — the `--link` `_main`-exporting `.o`. **int consumes it by Rust path** at `exe.rs:20` (re-export) + `session_v4.rs:3991`.
- `compiler::got_data_symbol_name` (compiler/mod.rs:43) — `__cranelisp_got_{M}` naming. **int consumes it by Rust path** at `exe.rs:163`, `worker.rs:3004`, `worker.rs:3590`.

**Binary guidance for W3 (the §6 inversion):**
- **MUST STAY `pub`** (real cross-crate Rust consumer — int, even while red, re-wires against these in S77; narrowing them is wrong, not deferred): the four codegen free fns (`compile_to_module`, `produce_disasm`, `load_object`, `compile_to_object`); `register_got_observer` (got_trace.rs:25/138) + its type contract (`GotEvent`, `GotEventTag`, `GotProvenance`, `GotObserver`); `jit::intrinsic_symbols`; `exe::generate_startup_object`; `compiler::got_data_symbol_name` (the canonical `cache::object` home — see Revision 6 on the duplicate); `Code` / `Jit` / `Linker` and the error types (`CompilationError`, `LinkerError`, `CranelispError` flow-through); the cache types int reads (`CachedModule`, `CacheMetadata`, `CacheStale`, `CacheManifest`, `ObjectCompileInput`, `CacheWritePacket`, `ProcessedPacket`, root orchestration helpers `module_cache_path` / `try_load_cached_module` / `load_cached_object`, consts `BUILD_ID` / `CACHE_FORMAT_VERSION` / `CACHE_SCHEMA_VERSION`); the heap-layout structs intrinsics agrees on the ABI for (`HeapAdt`, `HeapClosure`, `HeapVec` + offset consts).
- **SAFE to narrow to `pub(crate)`** (no Rust-path cross-crate consumer; for the externs/harvest there are none of their own, so visibility is orthogonal to the linker symbols): the **cache root re-export duplicate layer** (the ~25 items in `backend-cache.md` §"Wave 4 checklist" — int uses only submodule-qualified paths; /sprint confirmed 9 call sites, all qualified) — this is the dominant honest narrow set; plus genuinely-internal codegen helpers with no out-of-crate caller (`compiler::FnCompiler`/`CompileContext`/`MatchContext` internals, the `compiler::*` submodule `pub`s, `primitives_inline::*`, the `heap::emit_*` per-call-site primitives, `compiler::resolve_func_arity`/`resolve_got_target` if W3 confirms no int caller).
- **Rule for any narrowed item that names a linker symbol by string:** document the linker-symbol ABI (the exact symbol name + signature it relocates against) in the item's `///` rustdoc before narrowing, so the ABI contract survives the visibility drop. This applies to `compiler::got_data_symbol_name` IF the `compiler::` duplicate is narrowed (the `cache::object::got_data_symbol_name` canonical home stays `pub` for int).

The §6 inversion holds: narrow-by-default is correct for the cache duplicates and internal helpers; the boundary externs/harvest stay `pub` because int is their real consumer.

**Q6 — Public-API trajectory: 2008 → ~1850–1900. Two regens. Nothing that must NOT change beyond the §6 stay-pub set.**
Baseline regen #1 (W2) is roughly net-neutral on line count (signatures rotate; `Code` slims by removing two `ptr` fields and the `Primitive` variant — a small reduction; `Linker::get_symbol` return type changes; `CompilationResult`/`FunctionArtifacts` removed but `CompilationArtifacts`/`produce_disasm`/free `load_object`/`compile_to_object` added). Baseline regen #2 (W3) is the real shrink: the cache root re-export layer (~25 lines per `backend-cache.md` §"Acceptance signal") + internal codegen-helper narrowing. Estimate landing ~1850–1900 (a ~100–150 line reduction), dominated by the cache duplicate removal. Both regens use `--omit blanket-impls,auto-derived-impls` per the baseline-diff discipline; the narrowing wave regenerates in the same change-set (`/dev backend`), facade updated alongside (W3 `/design backend`). **Must NOT change:** the heap-layout `#[repr(C)]` structs' field order/offsets (Principle 14 — ABI contract, governed by layout discipline not `#[non_exhaustive]`); the §6 stay-pub set above.

**Q7 — Retirement (Step 4): TWO facades, ratified. Rustdoc homes + BC fold structure below. Both DROP OUT of facade_compliance.rs.**
- **Rustdoc homes:** `backend.md` (545 lines) folds to `crates/cranelisp-backend/src/lib.rs` crate-root `//!` (the bounded-context narrative + the seven bounded-context invariants + the "what crosses the boundary" surface) + per-item `///` on the four free fns, `Code`, `Jit`, `Linker`, error enums, `CompilationArtifacts`, the GOT-observer surface, and the heap-classification/layout surface (`heap.rs` module `//!` + per-item). `backend-cache.md` (377 lines) folds to a `cache/mod.rs` (or `cache.rs`) module `//!` preamble (the four-submodule architectural-shape table + the five cache bounded-context invariants + the three forbidden patterns) + per-submodule `//!` on `linker`/`manifest`/`object`/`serialize` + per-item `///`.
- **BC §3 fold:** `backend-cache` folds as a **subsection of BC §3** (`### 3a. Cache — crates/cranelisp-backend/src/cache/`), NOT a new top-level section — cache is the persistence half of the *same* bounded context (backend), and `backend-cache.md` itself states this (its BC citation defers to `bounded-contexts.md §3`). A peer top-level section would assert a separate bounded context that does not exist.
- **Invariants that MUST survive into BC §3:** backend.md's seven (lines 519–531: single compilation entry point per mode; uniform consuming convention; lifecycle-owner-on-`code`/ptr-in-GOT; `defined_symbols()` predicate; per-symbol reclaim safety; two-GOT-one-CLIF; bare-name+Local linkage) + backend-cache.md's five (lines 314–322: `Linker` is the only mmap-holder; `CacheManifest` is the single index; cache-validity checked at every hit; `CACHE_FORMAT_VERSION`/`CACHE_SCHEMA_VERSION` independent; no re-codegen on cache-hit). Twelve invariants total; none may be dropped in the fold.
- Both crates **DROP OUT** of `tests/facade_compliance.rs` per the S74 correction (source = definition; baseline + compiler = guard; rustdoc = rationale; NOT a rustdoc-restating self-documentation check). 7th + 8th retirement data points. The `design/arch/CLAUDE.md` exception-list edit (→ 8 retired) is a W5 `/arch` edit, not part of this review.

**Q8 — Validate-against-source-first (S74 lesson): phantom/stale facade items the fold must NOT carry.**
- **CONFIRMED stale (known one):** `facades/backend.md:407` and `:402–409` + §"Code" line 102/109 + `#[non_exhaustive] DTOs` describe `code: Some(Code::Primitive)` and the `Primitive` variant as live. Post-0244 this is `code: None` + variant deleted. The `:407` fix is W3 `/design backend` (facade still binding until retired); the fold (W5) must carry the **post-0244** statement (`code: None`, primitive-ness from `kind: DefKind::Primitive`), NOT the facade's current `code: Some(Code::Primitive)` text.
- **FOUND additional (Revision 8):** the facade's §"Code" (lines 97–116), §"Return shapes" `LinkerArtefact`/`ObjectArtefact` (lines 81–93), and §`#[non_exhaustive]` DTOs all state the *target-slimmed* `Code::Jit(Arc<Jit>)` shape — but source still carries `Code::Jit { jit, ptr }`. That is correct facade behaviour (target-stating), but the **fold must occur AFTER W2 lands the slim**, so the rustdoc reflects as-built reality. Folding the target shape into rustdoc before W2 rotates the source would create a rustdoc-vs-source drift on day one. **Sequencing constraint: W5 retire must follow W2/W3 conform — already the wave order; just flagging that the `Code` rustdoc fold reads the post-rotation source, not the pre-rotation source.**
- **`CompilationResult`/`FunctionArtifacts`** (facade §"transitional", lines 345–351): these are explicitly transitional and DELETE in W2; the fold must NOT carry them into rustdoc.
- **`primitive_for_trait_method`** (facade lines 357, 381): already a tombstone (deleted from source S67 W4); the fold carries it only if a "removed patterns" note is useful — recommend dropping it from rustdoc (git history is the record), keeping only the live "operator special-casing forbidden" forbidden-pattern note.

**Q9 — FIXME dispositions: RATIFIED with one sharpening (Revision 9).**
- **0221 in-scope (W2):** ratified — the D41 rotation; backend-authored `CompilationArtifacts` + `produce_disasm`; resolved when W2 lands the signature.
- **0244 backend-half in-scope (W2):** ratified — `Code::Primitive` deletion contained per Q4; substance preserved (primitive-ness reads from `kind: DefKind::Primitive`, already the source-of-truth per Decision 0048 A2-reversal). Deletion loses nothing.
- **0191 + 0182 verify+delete:** ratified. Premise (backend consumes primitives by Rust path via `ring0_jit_symbols()`) is **confirmed dead in source**: `ring0_jit_symbols` has zero live callers (only two comment references at `primitives/src/ring0.rs:211` + `primitives_inline.rs:21`); `intrinsic_symbols()` (jit.rs:99) is intrinsics-only; backend is dep-banned from primitives (`tests/no_primitives_dep.rs`). Substance embodied in the dep-ban structural invariant (Decision 0048) + `facades/backend.md:328` already records "Closes FIXME 0191 + FIXME 0182 (S68 close)." Deletion loses nothing. `git rm` both in W1.
- **0099 verify+delete:** ratified. **Confirmed embodied in source**: `got_observer.rs` carries the full contract (`GotEventTag` incl. `Redefinition` at :68, `GotEvent`, `register_got_observer` at :156, `emit` at :175); int's `got_trace.rs:270–273` emits the `Redefinition` tag from int's symbol-table-write site (the exact split 0099 specified — backend publishes the tag, int owns the emit; `got_observer.rs:172` documents this). Both backend emit sites (JitWrite, LinkerWrite) present. Verify in W1/W6, then `git rm`. Loses nothing.
- **0223 subsumed by W5:** ratified — only live-facade citations are `ConstructorInfo` in `backend.md` (472/482/542), corrected by the W5 fold to the ctor-as-Def shape; PrimitiveKind lives only in historical `*-audit-s69.md` (non-canonical). `/arch` closes + deletes 0223 when `backend.md` folds (W5).
- **0096 opportunistic W5:** ratified — mechanical archival of 6 stale `design/backend/` docs; `/design backend` filler.
- **0232 → S77:** ratified — platform-as-module cache `schema_literal` is a forward feature, pairs with platform host-wiring (0233), not backend-alignment.
- **0122 defer + re-test after W1:** ratified — 4 `mode_equiv_*` `--link` GOT-alignment failures are out of alignment scope; re-run once W1 makes backend build. **Sharpening (Revision 9):** if W2's `Code` `ptr`-rotation + `compile_to_module` rotation changes GOT-slot population timing, 0122 may shift; re-test after W2 as well as W1, and if still failing at W6, the handoff to a future `/backend` defect sprint must carry a minimal repro (`memory/feedback_cross_skill_minimal_repro.md`), not just the four test names.

### Enumerated revisions (all W1–W5 instructions; none blocks Phase 3)

1. **(W1, doc)** Correct the Step-1 table's "new `ResolvedCall` variant" wording — there is no new variant. `ResolvedCall` has four variants, all already matched in `compiler/apply.rs`; the E0004 is a payload-reshape non-exhaustiveness, not a new emission path. Reframe as "absorb the S70 `ResolvedCall` payload reshape (`impl_type: FQTypeName`, `mangled_name: JitSymbol`) + the `Expr::ConstrADT` lowering arm."
2. **(W1)** `Expr::ConstrADT` absorb work lands `compile_constr_adt` per `facades/backend.md` §"Constructor codegen"; delete the four-function family it replaces is **W4 streamline** (not W1) — W1 may stub `compile_constr_adt` minimally to clear E0004, full replacement + deletion in W4. (Keeps W1 to "get it compiling.")
3. **(W2)** State explicitly in the wave plan that W2 rotates the **full `Code` variant payload** (`{ jit, ptr }` → `(Arc<Jit>)`, `{ linker, ptr }` → `(Arc<Linker>)`) AND deletes `Code::Primitive` — both leave int red, both re-wired in S77. No half-rotation that retains `ptr` to spare int (Principle 8).
4. **(W2)** Confirm `CompilationResult` + `FunctionArtifacts` DELETE in W2 (not deferred to streamline) — they are the pre-rotation return tuple the D41 rotation removes.
5. **(W3)** Apply the §6 binary guidance above: the four codegen free fns, `register_got_observer` + GOT types, `jit::intrinsic_symbols`, `exe::generate_startup_object`, `cache::object::got_data_symbol_name`, `Code`/`Jit`/`Linker`/error types, the int-consumed cache types, and the heap-layout `#[repr(C)]` structs all STAY `pub` (int is the real consumer, red now, re-wires S77). Narrow set = cache root re-export duplicates + internal codegen helpers with no out-of-crate caller.
6. **(W4 streamline)** `compiler::got_data_symbol_name` (compiler/mod.rs:43) duplicates `cache::object::got_data_symbol_name` — int calls `cranelisp_backend::compiler::got_data_symbol_name` at three sites (exe.rs:163, worker.rs:3004/3590). The duplicate cannot simply narrow while int routes through it. Streamline either (a) routes int's three call sites to the `cache::object` canonical home (an int change — defer to S77) and narrows the `compiler::` form to `pub(crate)`, OR (b) keeps the `compiler::` re-export `pub` with rustdoc naming `cache::object::got_data_symbol_name` as canonical. Since int is red and re-wires in S77, prefer (a) but DEFER the int-side reroute to S77; for S75 keep the `compiler::` form `pub` (documented as a convenience re-export of the canonical `cache::object` home). Do not narrow it this sprint — int still names it.
7. **(W3, rustdoc-before-narrow)** For any string-emitting linker-symbol fn that IS narrowed, document the exact linker-symbol name + relocation signature in `///` before the visibility drop, so the ABI contract survives. (In practice none of the three externs/harvest fns narrow this sprint per Revision 5/6 — this rule binds future narrowing.)
8. **(W5 fold sequencing)** The `Code` rustdoc fold reads **post-W2** source (slimmed variants, no `Primitive`, `code: None` for primitives). Carry the post-0244 statement, NOT the facade's current `code: Some(Code::Primitive)` text. Fix `backend.md:407` in W3 first (facade still binding), then fold the corrected text in W5.
9. **(W5 BC fold)** `backend-cache` folds as **BC §3 subsection 3a**, not a peer top-level section — same bounded context. Carry all twelve invariants (7 backend + 5 cache); drop none. **[SUPERSEDED at W5b by the user-confirmed distinction: `backend-cache` is an IMPLEMENTATION DETAIL, not a BC surface → its 5 invariants fold to the cache submodule rustdoc ONLY; BC §3 carries the 7 backend invariants, NO §3a, NO cache content. See the W5b subsection.]**
10. **(W5)** Drop `primitive_for_trait_method` tombstone from the rustdoc fold (git history is the record); keep only the live "operator special-casing forbidden" forbidden-pattern note in the `lib.rs` `//!` or `primitives_inline.rs` `//!`.
11. **(W6 / 0122 handoff)** Re-test the four `mode_equiv_*` `--link` failures after **both** W1 and W2 (the `Code` ptr-rotation may shift GOT-slot timing). If still failing at W6, the handoff to a future `/backend` defect sprint carries a minimal repro per the cross-skill-minimal-repro rule, not just the test names.

### Scope adjustment
None. Scope is correctly sized; all four steps deliverable crate-narrow-green with int red. The only sequencing sharpenings are Revisions 2 (ConstrADT deletion is W4 not W1), 8 (fold reads post-rotation source), and 6 (`compiler::got_data_symbol_name` reroute deferred to S77).

### DAG / interface finding
No `cranelisp-types` change owed. Every type the two new codegen arms consume already exists in `cranelisp-types` (`Expr::ConstrADT`, `DefKind::Constructor`, `ResolvedCall` 4-variant, `FQTypeName`, `JitSymbol`). `CompilationArtifacts`/`produce_disasm`/`LinkerArtefact`/`ObjectArtefact` are backend-authored (no DAG inversion; backend never names int's `Introspection`). DAG stays acyclic; Principle 3 intact.

### Wave-structure ruling
**Keep 6 waves. Do NOT merge W2+W3** — they are distinct review lenses (signature-semantics rotation + baseline regen #1 vs visibility narrowing + baseline regen #2 under the §6 guardrail) and bundling them would defeat the side-by-side baseline-diff discipline.

### What changed in `design/arch/` (this review)
Nothing enacted pre-implementation. The `decisions/` drain for D41 (0221) and 0244 backend-half, the `backend.md:407` fix, the two-facade fold into BC §3, and the `design/arch/CLAUDE.md` exception-list bump (→ 8 retired) are all named as **W3/W5 work**, not enacted now, per the Phase-2 "name cascades, don't pre-enact" boundary. This review section in `sprints/SPRINT.md` is the only edit made.

## Phase 2 re-scope — backend to FINAL state, not int-deferential (user directive 2026-06-01)

**Directive (user):** *"Forget everything we are doing to make things easier for int,
at the expense of backend. We will fix int later — it is broken and can stay broken.
We want backend in its final state."*

**Governing principle for S75 (supersedes the int-deferential parts of the Phase-2
review above):** backend's final public surface = **what backend's own bounded context
legitimately exposes as boundary**, as defined by its facade — NOT what int's current
(red, in-flux) call sites happen to reach. Any item that is `pub` *only because int
reaches in by Rust path* is narrowed to `pub(crate)` this sprint; int breaks further and
is re-wired in S77. Grounded in `memory/feedback_callee_api_for_caller_only.md` (a callee
API kept only because int calls it is NOT justified by int; dead-code-on-demotion is the
expected signal) + `memory/feedback_facade_definitive_not_consumer_source.md` (canonical
surface defined by the facade, not the consumer's call sites).

**What this overturns in the Phase-2 review:**
- **Rev 5** — the test "MUST STAY `pub` because int is the real consumer" is **wrong**.
  Correct test: *is this backend's legitimate bounded-context boundary?* GENUINE boundary
  stays (the codegen entry points; `Code`/`Jit`/`Linker` + error types; the cache
  read/write contract int legitimately drives; `register_got_observer` extension point;
  the heap-layout ABI structs intrinsics agrees on). The **internal-but-exposed-for-int**
  items — `jit::intrinsic_symbols`, `exe::generate_startup_object`, and the
  `compiler::got_data_symbol_name` duplicate — are re-judged boundary-vs-leak on their own
  merits and narrowed if they are leaks, **regardless of int's reach-in**.
- **Rev 6** — REVERSED. `compiler::got_data_symbol_name` is a convenience duplicate of the
  canonical `cache::object::got_data_symbol_name` (the facade says so) → **narrow now**;
  do NOT keep it `pub` / defer the int reroute to S77.
- The "no churn for int / don't strand int / int re-wires against a stable target"
  framing throughout the Phase-2 review is **moot** — backend goes to final state and int
  breaks as much as it breaks.

**Unchanged:** acceptance is still crate-narrow green (backend builds + its own tests pass);
the §6 guardrail still protects genuine *emitted-call linker symbols* (backend has none of
its own, so it is moot for backend-owned symbols); 0244 / `Code` payload rotation were
already "let int break"; 0232 (→S77) + 0122 (defect) unaffected. Re-ruling of the
boundary-vs-leak dispositions is `/arch`'s call (re-tasked under this principle).

### Codegen-entry finding — `compile_to_module<M>` is the single entry; `compile_to_object` DELETES (facade + sequences correction owed to /arch)

Investigation (Explore sweep, 2026-06-01) confirmed: the single-codegen-entry design is
**normative**, not inferred — `design/backend/compile-to-module.md:29–31` ("`compile_to_module<M>`
is the ONLY compilation entry point in the backend crate"), `:59` ("This section is normative…
MUST be implemented exactly as written"), `:124–126` (no internal fork; byte-identical CLIF;
mode lives in the `Module` impl at finalize) — grounded in Decision 23 + `jit-object-convergence.md §1.1`.

- **`compile_to_object` (`lib.rs:821`) DELETES.** It is a Sprint-67 facade-compliance **scaffold**
  that returns unimplemented and cites **FIXME 0184 — which does not exist as a file** (dangling
  source citation). The real object path already IS `compile_to_module::<ObjectModule>` +
  caller-side `obj_module.finish().emit()` (`cache/object.rs:263–268`) — and that finalization is
  the object caller's job **by the normative design** (`compile-to-module.md §2.5`), symmetric to
  int holding the `JITModule` for `Arc<Jit>` reclaim in JIT mode. NOT a leak; the documented contract.
- **`load_object` STAYS** — the genuine answer to "why isn't `compile_to_module` sufficient": it
  isn't, for **cache-hit**, which does NO codegen (maps a prebuilt `.o` via the `Linker`).
  `compile_to_module<M>` cannot express it (requires `ast: Some(_)`, emits CLIF). Two distinct
  kernels per `jit-object-convergence.md §3.2`.
- **Final codegen boundary = `compile_to_module<M>` + `load_object` + `produce_disasm`.**

**Facade-vs-design-doc conflict → /arch arbitration (design doc wins).** `facades/backend.md` PIF
**Row 4** target-states `compile_to_object` as a free function to build — contradicting the
normative `compile-to-module.md`. Per configuration-grounds-the-facade, Row 4 is ungrounded
Sprint-67 accretion. **/arch corrects (user-directed 2026-06-01):** (1) retract Row 4 + drop
`compile_to_object` from `facades/backend.md` §"Free functions"; affirm the 3-entry boundary
grounded in the normative doc + D23; (2) **correct the sequence diagrams** (`design/arch/sequences/`)
that show or imply a separate object-compile entry → single `compile_to_module::<ObjectModule>` +
caller `finish().emit()`. Source stub deletion is W2 `/dev backend`; the dangling FIXME-0184
citation goes with it (never filed; no separate action).

### /arch re-ruling (2026-06-01) — final-state narrowing + facade/sequence corrections

`/arch` re-tasked under the FINAL-state principle above. This subsection (a) records the
Task-A facade + sequence corrections enacted now, and (b) re-rules the surface-narrowing
dispositions, reversing the int-deferential parts of Rev 5 and Rev 6.

#### Task A — corrections enacted (facade + sequences)

**A.1 — `facades/backend.md` (+ `facades/backend-cache.md` consistency sweep).**
- §"Free functions" now states the codegen boundary is **exactly three** free fns
  (`compile_to_module<M>` + `load_object` + `produce_disasm`); added a prose paragraph
  "There is no separate object-compile entry" grounding the object path as
  `compile_to_module::<ObjectModule>` + caller `finish().emit()` in `compile-to-module.md`
  §2 (normative; §2.5 caller-finalize contract) + D23, with a tombstone note (Sprint-67
  scaffold; dangling FIXME 0184 never filed; retracted).
- PIF **Row 4** marked **RETRACTED** with the same grounding.
- Reconciled every other live `compile_to_object` reference inside `backend.md` (the
  free-fn prose, §"Object file contract" header, §"Function symbol naming", §"Sidecar",
  §"Return shapes" closing prose, bounded-context invariant 3) → the object-path phrasing.
- `backend-cache.md` consistency: the `object` submodule role row, `ObjectCompileInput`
  comment, and the PFR disposition row no longer name a `compile_to_object` free fn.
- No baseline regen (the stub is removed in source by W2; the facade states the as-designed
  surface). Both facades are still binding until W5 retirement.

**A.2 — sequence diagrams.** Only **`exec-flow-compilation.mmd`** depicted a separate
object entry (the OBJECT CODEGEN PHASE: `NW ->> Backend: compile_to_object(...)`). Corrected
to: nice worker constructs the `ObjectModule`, calls
`compile_to_module::<ObjectModule>(...) -> Result<CompilationArtifacts, CompilationError>`,
then finalises caller-side (`obj_module.finish()` + `product.emit()?`), packaging the bytes +
sidecar into the `ObjectArtefact` it persists. Added a Note grounding the single-entry contract
(D23 + §2 + §2.5). **`exec-flow-link.mmd` and `exec-flow-repl.mmd` were already correct** —
link already states "the same `compile_to_module<M: Module>` ... with an `ObjectModule` instance"
and delegates object cadence to the compilation diagram; repl only shows the JIT
`compile_to_module`. SVG regenerated with `mmdc` (clean; first attempt hit the S74 `;`-in-text
trap on a self-message — semicolons removed, re-rendered green; `exec-flow-compilation.svg`
updated). *(Note: the diagram's `compile_to_module` arrow still carries the pre-S70-Phase-B
`introspection: Option<...>` / `-> Result[(), ...]` signature in the JIT arms at :212/:132 — a
separate, broader signature-drift not in scope for this object-entry correction; left untouched.)*

#### Task B — boundary-vs-leak re-rulings (final-state principle; reverses Rev 5/6 int-deference)

Binary ruling per item. Ground = backend's own bounded context (codegen / RC / JIT lifecycle /
caching / linking), NOT int's reach-in. Leak = `pub` only because int names it by Rust path →
`pub(crate)`. int breaks; re-wired S77.

| Item | Ruling | Grounds (backend BC, not int) |
|---|---|---|
| **`compile_to_module<M>` + `load_object` + `produce_disasm`** | **STAY `pub`** | The three genuine codegen entry points — the boundary `compile-to-module.md` §2 makes normative. Backend's reason to exist as a crate. |
| **`Code` / `Jit` / `Linker` + error types** (`CompilationError`, `LinkerError`, `CranelispError` flow-through) | **STAY `pub`** | Lifecycle-owner + typed-result vocabulary the codegen entries return; backend originates them (Principle 15). |
| **Cache read/write contract** a driver legitimately needs (`CachedModule`, `CacheMetadata`, `CacheStale`, `CacheManifest`, `ObjectCompileInput`, `CacheWritePacket`, `ProcessedPacket`, `module_cache_path` / `try_load_cached_module` / `load_cached_object`, consts `BUILD_ID` / `CACHE_FORMAT_VERSION` / `CACHE_SCHEMA_VERSION`) | **STAY `pub`** | Caching is inside backend's BC; the persistence contract is a legitimate boundary a session driver consumes, not an int reach-in. |
| **`register_got_observer` + event types** (`GotEvent`, `GotEventTag`, `GotProvenance`, `GotObserver`) | **STAY `pub`** | A designed extension point (peer of intrinsics' `IoObserver`); backend defines the taxonomy + registration API by design. |
| **Heap-layout `#[repr(C)]` structs** (`HeapAdt`, `HeapClosure`, `HeapVec` + offset consts) | **STAY `pub`** | The intrinsics-agreed ABI contract (Principle 14). A genuine cross-crate layout boundary, governed by `ABI_VERSION`, not by int. |
| **`jit::intrinsic_symbols`** (`jit.rs:99`) | **NARROW → `pub(crate)`** | **Leak.** This enumerates intrinsic JIT-symbol *registration* targets for `JITBuilder::symbol` — that is **JIT-setup plumbing that belongs encapsulated behind the codegen entries**, not a boundary backend's BC legitimately exposes. int calls it at `worker.rs:3545` only because int currently hand-rolls JIT-builder setup; that registration is backend's own concern (backend owns JIT lifecycle). Names linker symbols by string → **document the intrinsic-symbol ABI in `///` before the drop** (see below). int breaks; acceptable (S77). |
| **`exe::generate_startup_object`** (`exe.rs:31`) | **NARROW → `pub(crate)`** | **Leak.** The `--link` `_main`-`.o` assist is **link-orchestration the `--link` driver owns**; backend produces user `.o`s with bare-Local linkage uniformly (BC invariant 7 — "the `--link` `_main` alias is int's job, not backend's"). A backend free fn that emits the `_main` startup `.o` is int's link step leaking into backend's surface. int calls it (`exe.rs:20` re-export + `session_v4.rs:3991`) — but by backend's own invariant 7 this is int's job; the fn body may stay in backend as an internal helper, but it is not a boundary. Names `_main` + relocation symbols by string → **document the ABI in `///` before the drop**. int breaks; acceptable (S77). |
| **`compiler::got_data_symbol_name`** (`compiler/mod.rs:43`) | **NARROW → `pub(crate)`** | **Leak (duplicate / internal naming primitive).** Source ground-truth reverses the facade's framing: the `fn` is **defined** in `compiler/mod.rs:43` (canonical), and `cache::object::got_data_symbol_name` (`object.rs:298`) is the `pub use` re-export — every internal backend call site routes through the `compiler::` form. Either way it is a **codegen-internal relocation-symbol naming primitive** (`__cranelisp_got_{M}`), not a backend boundary: int names it (`exe.rs:163`, `worker.rs:3004/3590`) only to construct the same relocation name int-side, which is int reaching into backend's codegen-naming internals. Narrow the surface to **one** `pub(crate)` home; int breaks; re-wired S77. Names a linker symbol by string → **document the `__cranelisp_got_{M}` ABI in `///` before the drop.** *(This REVERSES Rev 6, which kept it `pub` to spare int's three call sites — explicitly overturned by the final-state directive.)* |

**Linker-symbol-ABI documentation owed (rustdoc-before-narrow, per the §6 rule applied to
string-naming fns being narrowed).** All three NARROW items name linker symbols by string; each
MUST carry its exact symbol name + relocation signature in `///` before the visibility drop:
- `jit::intrinsic_symbols` — the intrinsic extern symbol names + the `IntrinsicSymbol { name, ptr, param_count, is_runtime, has_return }` registration contract (`JITBuilder::symbol(name, ptr)`).
- `exe::generate_startup_object` — `_main` (`Linkage::Export`) + the relocation against `__cranelisp_got_{entry_module}` at the entry module's `main` GOT slot.
- `compiler::got_data_symbol_name` — the `__cranelisp_got_{M}` data-symbol naming scheme (the per-module GOT export/import symbol).

**Cache root re-export duplicate layer** (backend-cache.md Wave-4 checklist, ~25 items):
**NARROW → `pub(crate)`** regardless — already settled (int uses only submodule-qualified
paths). Unaffected by this re-ruling; restated for completeness.

**Net effect vs the Phase-2 review:** Rev 5's "MUST STAY `pub` because int is the real consumer"
set shrinks by three items (`jit::intrinsic_symbols`, `exe::generate_startup_object`,
`compiler::got_data_symbol_name`), all re-judged leaks on backend's own BC merits. Rev 6 reversed.
The genuine-boundary set (codegen entries; `Code`/`Jit`/`Linker` + errors; cache contract;
GOT-observer extension point; heap-layout ABI) stays `pub` because each is backend's legitimate
boundary — *which happens to coincide with* int being a consumer, but the grounds are backend's BC,
not int's reach. Baseline regen #2 (W3) shrinks by these three plus the cache duplicates. All three
NARROW items leave int **red** (re-wired S77) — acceptable per the directive.

### /arch JIT-setup target locked (2026-06-02)

`/arch` locked the agreed JIT-setup / intrinsic-catalog target into the canonical docs
(`facades/backend.md`, `bounded-contexts.md §3` + `§4b`), source-validated against
`jit.rs`, `worker.rs`, `pipeline.rs`, `session_v4.rs`, and `primitives/src/lib.rs` first
(the facade had been wrong 3× this sprint). Summary of what landed and what is forward-only:

**(a) S75-ACTIONABLE — `Jit`-orchestration narrowing (W3-follow / W4).** The `Jit` boundary
shrinks to **construct + handoff + reclaim**: the constructor(s), `jit_module()` (the handoff
accessor int passes into `compile_to_module`, confirmed `worker.rs:3296`), and `Drop` stay
`pub`. **Reclassified from "internal-but-exposed boundary" to INTERNAL (`pub(crate)`):** the
JIT-orchestration methods (`declare_intrinsics`, `declare_functions{_prefixed}`,
`declare_imported_functions`, `compile_defn`, `finalize{_and_get_ptr}`, `get_finalized_ptr`,
`get_ptr_by_name`, `build_compile_context`, `build_shared_isa`), the module-level free fns
(`build_isa`, `declare_intrinsics_generic`, `intrinsic_symbols`), and the JIT-setup DTOs
(`IntrinsicSymbol`, `IntrinsicFuncIds`, `IntrinsicIds`, `CompileArtifacts`). These are the
surface ONLY int's PARALLEL hand-rolled REPL path uses (`pipeline.rs:137–169` + `:276–306`),
which collapses into `compile_to_module` in S77. `CodeFinalizer` STAYS `pub` — it is the
`compile_to_module<M: Module + CodeFinalizer>` generic bound (named in the entry signature, not
driven internally). **Source note:** `intrinsic_symbols()` is *already* `pub(crate)` in source
(`jit.rs:122`, with the linker-symbol-ABI `///` box) — the facade now matches; the rest of the
narrowing is W3-follow/W4 `/dev backend`.

**(b) TARGET-STATED-S77 — `Jit::new(symbol_tables)` + `INTRINSICS_TABLE`.** Target constructor
`Jit::new(symbol_tables)` derives the entire JIT symbol set itself (int assembles nothing):
GOT data symbols from `symbol_tables[M].got().base_ptr()` for every module M including the
`primitives` synthetic module (preserving the Decision-0048 dep-ban — backend reaches primitives
only through the type-erased mount, never names `cranelisp_primitives::`), and intrinsic `Import`
targets from the intrinsics-published `cranelisp_intrinsics::INTRINSICS_TABLE`. `INTRINSICS_TABLE`
applies the `PRIMITIVES_TABLE` precedent (Decision 0048) to intrinsics — but as a **flat catalog,
NOT a mounted GOT-module** (CRUCIAL ASYMMETRY: intrinsics are Import-dispatched, not GOT-dispatched;
BC §4b invariant 9/11), consumed at three resolution points (JIT construct / cache-hit load /
`--link`), never at codegen. The current `Jit::new_with_symbols(extra)` is transitional. Neither
`Jit::new(symbol_tables)` nor `INTRINSICS_TABLE` exists in source today; both are S77 (int + intrinsics
source). `Jit::new(symbol_tables)` repurposes the `new` name (collides with today's zero-arg
`Jit::new()`; the trio `new`/`new_with_symbols`/`new_with_isa` + `build_shared_isa` collapse into it).

**(c) FLAGGED OPEN (forward / undecided — NOT baked).**
- **trace-as-observer** — promoting the 12 `cranelisp_trace_*` hooks to stable intrinsics + a
  `register_trace_observer` (removing them from int's JIT injection) would **amend Decision 40**.
  NOTED as a future option only; **not amended** this fire. For S75, trace stays int-owned per
  Decision 40 (the 12 `cranelisp_trace_*` symbols + `cranelisp_trace_format` in `int_intrinsics()`,
  `session_v4.rs:4938`).
- **`discover-tests` / `run-test` residual** — the 2 session-returning int-owned symbols in
  `int_intrinsics()` (14 total) are NOT derivable by `Jit::new(symbol_tables)`. Whether the S77
  collapse keeps a `Jit::register` escape-hatch or composes them via stdlib is an **open forward
  decision** — not resolved here.

**Source-grounded corrections made to the target as stated:** (1) the boundary accessor that stays
`pub` is `jit_module()` — the brief said "`module()`/`jit_module()`", but `module(&self)` is already
private in source (`jit.rs:330`); only `jit_module(&mut self)` is `pub`. (2) `Jit::new(symbol_tables)`
collides with the existing zero-arg `Jit::new()` — flagged for S77 as a name-repurpose, not a new
method alongside the trio. (3) `build_shared_isa` added to the narrow set (its only out-of-crate use
is int's pre-build-ISA pattern, which folds into `Jit::new(symbol_tables)`).

## Scope detail (S75)

### Step 1 — Absorb the input cascade (`/dev backend`)
41 lib errors (202 with `--tests`), all tracing to S69 types lock + S70 frontend reshape:

- **`HeapCategory` import repointing (E0432 ×5)** — relocated `cranelisp-types` →
  `cranelisp-backend::heap` (S69 Sub 38, already in `facades/backend.md §"Heap
  classification"`); import sites still say `use cranelisp_types::HeapCategory`.
- **Constructor-as-Def shape (`ConstructorInfo` gone E0425/E0432; `ModuleEntry::
  Constructor` E0599; `.fields` on `Symbol` E0609 ×9)** — S70/D47 collapse. Includes
  the stubbed `heap.rs::classify_from_type_def_info` rebuild (per-ctor `field_count`
  via symbol-table lookup — named pending-cascade in the facade).
- **`ModuleFullPath` newtype opacity (E0616 ×5)** — field `.0` private (S69); use accessor.
- **`ModDecl.visibility` (E0027 ×4)** — `ModuleEntry` patterns must mention `visibility`.
- **`ModuleEntry::Reexport` collapse (E0599 ×2)** + **`ConstrainedFn { variant:
  DefnVariant }` (E0308 `Defn`→`DefnVariant` ×9)** + **`Expr::Lambda.param_annotations`
  (E0559)** — S70 narrows.
- **New codegen / non-exhaustiveness (E0004 ×2)** — `Expr::ConstrADT` is a real new
  lowering arm (`heap.rs` + `compile_constr_adt`, replacing the 4-fn ctor family — full
  replacement is W4 streamline per Rev 2). The `compiler/apply.rs` E0004 is NOT a new
  `ResolvedCall` variant (it has exactly 4, all already matched) but a **payload-reshape
  non-exhaustiveness** from S70 (`TraitMethod.impl_type: FQTypeName`, `mangled_name:
  JitSymbol`) — Phase-2 Rev 1. **Validate against spec/source first.**

### Step 2 — Conform both facades exactly (`/dev backend` + `/design backend` + `/arch`)

- **FIXME 0221 (Important)** — rotate `compile_to_module` to
  `-> Result<CompilationArtifacts, CompilationError>` + `module_aliases` param; author
  on-demand `produce_disasm(fq, symbol_tables)`; retire `CompilationResult`/
  `FunctionArtifacts`. (int-side `worker.rs` call-site update is S77 host-wiring; int
  stays red.)
- **Free-function carve-outs** — `load_object` free function;
  `Linker::load_object` → `pub(crate)`; `Linker::get_symbol` → `Result<*const u8,
  LinkerError>` (D37). **`compile_to_object` DELETES** (per the /arch re-ruling + Codegen-entry
  finding): the `lib.rs:821` stub goes; the object path is `compile_to_module::<ObjectModule>`
  + caller `finish().emit()`. Codegen boundary = the three entries `compile_to_module<M>` +
  `load_object` + `produce_disasm`.
- **FIXME 0244 backend half** — delete `Code::Primitive` from `code.rs` (`:98`);
  primitive-ness read from `kind` post-S73. Cascade `Code` enum + match sites.
- **`facades/backend.md:407` doc fix** — stale `code: Some(Code::Primitive)` →
  `code: None`. `/design backend` (facade still binding).
- **Surface-exact narrowing** — every `pub` not documented in `backend.md`/
  `backend-cache.md` → `pub(crate)`, **under the §6 ABI guardrail** (verify
  `#[export_name]`/fn-ptr-harvest consumers; rustdoc the linker-symbol ABI for any
  narrowed extern). The facades' own §"Internal-but-exposed" + Wave-3/Wave-4 PIF lists
  + backend-cache Wave-4 checklist are the documented narrowing plan.
- **FIXMEs 0191 + 0182 (stale orphans — verify+delete, NOT deferrable work)** — both
  describe backend consuming `cranelisp-primitives` by Rust path via
  `ring0_jit_symbols()`. **That premise is dead in current source**: `intrinsic_symbols()`
  (jit.rs:99–126) is intrinsics-only; `ring0_jit_symbols` has zero live refs workspace-wide;
  backend is dep-banned from primitives. Resolved at **S68** by the dep-ban + GOT-indirect
  dispatch (NOT the `PRIMITIVES_TABLE`-walk migration 0191 proposed — that approach was
  abandoned, so its "two blockers" are moot). `facades/backend.md:328` already records
  *"Closes FIXME 0191 + FIXME 0182 (S68 close)."* Both files should have deleted at S68
  close. **Action: targeted skill verifies premise-dead + `git rm`s both (trivial; W1).**

### Step 3 — Streamline the interior (`/dev backend`)
Dead code + duplication made visible by Step 2's narrowing (e.g. `compiler::
got_data_symbol_name` duplicate of `cache::object::got_data_symbol_name`; transitional
`CompilationResult`/`FunctionArtifacts` once the D41 rotation lands; any now-unreferenced
`pub(crate)` helper). Clippy clean.

### Step 4 — Retire both facades (`/design backend` + `/arch` + `/qa`)
7th + 8th data points of the stable retirement pattern (types §7 → frontend §1 →
platform §5 → typecheck §2 → intrinsics §4b → primitives §4a):
- Fold `backend.md` (545 lines) + `backend-cache.md` (377 lines) → `lib.rs` + cache
  submodule `//!` preambles + per-item `///` rustdoc; cross-surface narrative +
  bounded-context invariants → `bounded-contexts.md §3` (+ a cache subsection).
- `git rm` both facades; update `design/arch/CLAUDE.md` exception list → 8 retired.
- `/qa` drops both crates from `facade_compliance.rs` (the S74 correction: retired
  crates DROP OUT — source = definition, baseline+compiler = guard, rustdoc =
  rationale; NOT a rustdoc-restating self-documentation check).
- 0 dangling canonical refs to either file.

### Acceptance (S75)
- `cargo check -p cranelisp-backend` + `--tests` GREEN; `cargo nextest run -p
  cranelisp-backend` green standalone — **independent of the workspace red state**
  (int still red). Same shape as S72/S73/S74. **(User-confirmed: workspace-wide
  green out of scope until int conforms, S77.)**
- `clippy` + `cargo doc` clean on the crate.
- `public-api.txt` regenerated under `--omit blanket-impls,auto-derived-impls`;
  every baseline line named in source rustdoc post-retirement; 0 orphans.
- Both facades retired; cross-refs swept; exception list → 8 retired; 0 dangling refs.

## Out of scope (deferred, with rationale)
- **int host-wiring** (FIXMEs 0242 incl. S74 Revision-C mount-comment reconciliation,
  0098, 0187, 0214) + platform host-wiring set (0229–0235) → **S77** (int, last
  crate). Wires against S75's conformed/retired boundary.
- **Workspace-wide green** — blocked on int (red); confirmed out of scope.

*(FIXMEs 0191 + 0182 are NOT deferred — they are stale orphans, resolved at S68;
verified premise-dead and `git rm`'d in-sprint. See Step-2 detail + FIXME table.)*

## Skill plans (Phase 3)

Collated from `/design (backend)` + `/qa`, both source-validated 2026-06-01. Full per-step
detail lives in `design/backend/compile-to-module.md` (S75 normative banner + §2.6
`compile_constr_adt`) + `tests/plan/sprint-75-plan.md`.

### /design (backend) → ordered `/dev (backend)` work-steps

Design docs refined: `compile-to-module.md` (S75 banner pinning the 3-fn D41 boundary +
new §2.6 `compile_constr_adt` lowering design), `backend.md` (§2.1/2.3/2.6/3.2/3.3/6.1/8
rewrites), `jit-object-convergence.md` + `ring2-rc.md` (cross-ref repoint). **0096 archival
DONE** (5 firmly-stale docs → `design/backend/archive/` + README; 2 partially-stale kept —
the FIXME's "six docs" was a miscount, §8 had exactly 5 firmly-stale rows).

- **W1 — Absorb** (gate: `cargo check -p cranelisp-backend --tests` green + `nextest -p
  cranelisp-backend` green standalone):
  1. `HeapCategory` import repoint `cranelisp_types::` → `crate::heap::` (5 sites: apply.rs:10,
     control_flow.rs:10, match_codegen.rs:11, vec_codegen.rs:15, mod.rs:23).
  2. `ConstructorInfo`-gone → `DefKind::Constructor { type_name, tag, field_count, internal }`:
     rebuild `CompileContext::lookup_constructor` (mod.rs:335/394); fix `.fields`-on-`Symbol`
     E0609s (mod.rs:902/911/1450, heap.rs:339/340, match_codegen.rs:519, vec_codegen.rs:819/833/842,
     910/978) — `TypeDefInfo.constructors` is now `Vec<Symbol>`, walk each name's Def.
  3. `ModuleFullPath` `.0` opacity → accessor (manifest.rs:75/85/90/151, cache/mod.rs:113).
  4. `ModuleEntry` `visibility` field in patterns (cache/mod.rs:173, mod.rs:92/170/354);
     `Reexport`/`Constructor` variant collapse (mod.rs:92/170/396, control_flow.rs:42).
  5. `Defn`→`DefnVariant` (ConstrainedFn) E0308s (mod.rs:662–722, lib.rs:510);
     `Expr::Lambda.param_annotations` reshape (control_flow.rs:138).
  6. `heap.rs::classify_from_type_def_info` rebuild (per-ctor `field_count` via symbol-table walk);
     rebuild in-crate heap tests with Def fixtures.
  7. **`compile_constr_adt`** — land the `Expr::ConstrADT` arm **FULLY in W1** (/design ruling: ~50
     LOC, the existing `compile_data_constructor_call` body re-keyed off the node; a stub would
     make the W1 nextest gate hollow). 4-fn-family *deletion* defers to W4.
  8. `compiler/apply.rs:125` E0004 — rebind the existing 4 `ResolvedCall` arms to the S70 reshaped
     payloads (`impl_type: FQTypeName`, `mangled_name: JitSymbol`); NOT a new variant.
  9. `git rm` FIXMEs **0191 + 0182 + 0099** (premise-dead / fully-embodied — verified).
- **W2 — Conform boundary** (baseline regen #1): D41 rotation (0221) — `compile_to_module` →
  `Result<CompilationArtifacts, CompilationError>` + `module_aliases` param; author
  `CompilationArtifacts` + `produce_disasm`; **delete `CompilationResult`+`FunctionArtifacts`**.
  **Delete `compile_to_object` stub** + dangling FIXME-0184 citation. `Code` slim
  (`{jit,ptr}`→`Jit(Arc<Jit>)`, `{linker,ptr}`→`Linker(Arc<Linker>)`) **+ delete `Code::Primitive`**
  together (Rev 3/4). `Linker::load_object`→`pub(crate)`; `Linker::get_symbol`→`Result<_, LinkerError>`
  (D37). Re-test 0122. Regen baseline.
- **W3 — Conform surface** (baseline regen #2): narrow undocumented `pub`→`pub(crate)`; per the
  /arch re-ruling additionally NARROW `jit::intrinsic_symbols`, `exe::generate_startup_object`,
  `compiler::got_data_symbol_name` (**document each one's linker-symbol + relocation ABI in `///`
  BEFORE the drop**); cache root re-export narrowing (backend-cache Wave-4 checklist). `/design
  backend` keeps facades exactly matched incl. `:407` `code: Some(Code::Primitive)`→`code: None`.
- **W4 — Streamline**: delete the 4-fn ctor family (`compile_data_constructor_call`/`_as_value`/
  `nullary_constructor_tag`/`data_constructor_info`) + `lookup_constructor`; remove now-unreferenced
  helpers. Clippy clean.
- **W5 — Retire**: fold both facades → rustdoc + BC §3 (**backend = 7 BC invariants; cache = impl
  detail → cache submodule rustdoc ONLY, NO §3a, NO cache content in BC** — user distinction, W5b);
  `Code` fold reads post-W2 source. **W6 — Review**.

**Source-grounded corrections from /design (refine the plan):** (a) `Code` ALREADY lives in
`backend/src/code.rs` — W2 is slim-only, not a move (facade PIF Row 1 already landed). (b) current
sig is already `Result<CompilationResult, CompilationError>` with `<M,C,L>` — W2 rotates the
*return type + adds `module_aliases`*, not the error type (FIXME 0221's "verify on pickup" guess
was stale). (c) free `load_object` already exists — W2 only narrows the `Linker::load_object`
*method*. (d) Rev 1/2 confirmed against source.

### /qa

- **No new e2e owed** — conform/cascade/retirement only; the behaviour-adjacent items
  (`compile_constr_adt` ctor-as-Def collapse = same emission; D41 = internal signature) are
  covered by existing `build_confidence::mode_equiv_*`/`spec_03_types`/`spec_06_pattern_matching`.
- **W5 `facade_compliance.rs` re-anchor (the main /qa deliverable):** backend + backend-cache are
  the last two binding facades; on retirement they **DROP OUT** (NOT replaced by a rustdoc-restating
  check — the S74 correction). `facade_pairs() → vec![]` (preserves the sentinel's
  `split_once("fn facade_pairs()")` anchor); grep test → documented tombstone (8 facades retired).
  **`s68` sentinel flip** (`s68_primitives_uniform.rs:176–214`): drop the backend positive assertion
  (:193); extend the MUST-BE-ABSENT array (:204) to add `"cranelisp-backend"` — mirroring S74's
  primitives/intrinsics. Pure `std::fs` → authorable independent of the red binary; gated on W5.
- **e2e replay BLOCKED-by-red-binary** (not a gap; same as S72/S73/S74) — all `tests/*.rs` link the
  red root binary; runnable evidence = crate-narrow `nextest -p cranelisp-backend` (/dev-owned).
  S77 replay guard set named: `build_confidence`, `cache`, `spec_03_types`, `spec_06_pattern_matching`,
  `spec_12_runtime`, `spec_10_io`.
- **0122 re-test** after W1 AND W2 (W2 touches the exact `__cranelisp_got_{M}` symbol the defect
  names — most likely incidental-fix point); stays failing-not-ignored, ledger `out-of-scope
  (owner=/backend)`; minimal repro on any W6 handoff. No new FIXME to file.

## FIXME debt (Phase 1 triage)

| FIXME | Target | Status | Disposition this sprint |
|---|---|---|---|
| 0221 | /dev backend | open | **In scope** — D41 `compile_to_module` rotation + `produce_disasm` (W2). |
| 0244 | /arch + /dev backend | open (primitives half S73) | **In scope (backend half)** — delete `Code::Primitive` from `code.rs` (W2). |
| 0191 | /dev backend (re-targeted /dev primitives) | open (STALE) | **Verify+delete** — premise dead (backend dep-banned from primitives; `ring0_jit_symbols` gone; `intrinsic_symbols()` intrinsics-only). Resolved S68; facade:328 records it. |
| 0182 | /dev primitives, int | partially-resolved (STALE) | **Verify+delete** — same dead premise (`partial_residue` false); sibling of 0191. S73 claimed deleted but file survived. |
| 0223 | /arch | open (STALE) | **Subsumed by W5 retirement** — only live-facade citations are `ConstructorInfo` in backend.md (472/482/542), corrected by the fold; PrimitiveKind lives only in historical `*-audit-s69.md` (not canonical). /arch closes+deletes when backend.md folds. |
| 0099 | /dev backend+int | open (STALE) | **Verify+delete** — already implemented: `got_observer.rs` full contract + both emit sites (`lib.rs:706` JitWrite, `cache/linker.rs:284` LinkerWrite) + int `got_trace.rs` registration. Verify `Redefinition` emit in W1/W6, then delete. NOT new work. |
| 0096 | /sprint (work = /design backend) | **DONE (Phase 3)** | `/design backend` did the archival: `design/backend/archive/` + README created; 5 firmly-stale docs `git mv`'d; 2 partially-stale kept (FIXME's "six" was a miscount — §8 had 5). `git rm` the FIXME file at close. |
| 0232 | /backend | open (VALID, forward) | **Defer → S77** — `.meta.json` `schema_literal` for platform-as-module caching; pairs with 0233 (platform host-wiring). Future feature, not backend-alignment. |
| 0122 | /backend | open (LIVE defect) | **Defer; re-test after W1** — 4 `mode_equiv_*` `--link` GOT-alignment failures (build_confidence.rs:156–219, NOT ignored). Out of alignment scope; re-run once W1 makes backend build. |

## Notes

- 2026-06-01: Phase 1 scope drafted. Crate selection forced (backend only
  newly-eligible; deps types S69 + intrinsics S74 conformed; primitives dep-banned).
  Empirical: 41 lib / 202 lib+tests errors; 19.3k LOC / 23 files / 2008-line baseline
  — heaviest crate. **User decision (2026-06-01): all four steps in S75, broken into
  more waves; crate-narrow green, workspace red OK.** Terminology pinned: *conform* =
  surface matches facade exactly (boundary rotation + narrow-everything-undocumented);
  *streamline* = interior dead-code/duplication removal exposed by the narrowing.
- 2026-06-01: **FIXME 0191 investigated at user request — found stale.** Premise
  (backend consumes primitives by Rust path via `ring0_jit_symbols()`) is dead in
  current source: `intrinsic_symbols()` is intrinsics-only, `ring0_jit_symbols` has
  zero live refs, backend dep-banned from primitives. Resolved at S68 via dep-ban +
  GOT-indirect (NOT the migration 0191 proposed). Sibling **0182** is the same orphan
  (`partial_residue` false; S73 claimed deleted but file survived). Both → verify+delete
  in-sprint, not deferrable work. Re-scoped from "assess; likely defer."
- 2026-06-01: **Carried-FIXME staleness sweep (user request).** Five checked against
  source: **0099** substantially RESOLVED (got_observer contract + both emit sites +
  int got_trace registration all present) → verify+delete, not new work. **0223**
  subsumed by W5 retirement (only live citations are ConstructorInfo in backend.md;
  PrimitiveKind lives only in historical audit docs). **0096** VALID housekeeping (6
  stale docs, no archive/) → opportunistic W5. **0232** VALID but genuinely forward
  (platform-as-module cache) → S77, not backend-alignment. **0122** LIVE `--link`
  GOT-alignment defect (4 tests, not ignored) → defer + re-test after W1 makes backend
  build. Net: 2 stale (0099, 0223) join the verify+delete set with 0191/0182.
  Awaiting go for Phase 2 (/arch).

- 2026-06-01: **Phase 3 (Design) complete.** `/design (backend)` refined 4 `design/backend/`
  docs (compile-to-module.md S75 banner + §2.6 `compile_constr_adt`; backend.md rewrites),
  produced the per-wave `/dev` work-steps (collated above), and **did the 0096 archival** (5
  docs → archive/). `/qa` authored `tests/plan/sprint-75-plan.md`: no new e2e (conform/cascade);
  the W5 `facade_compliance.rs` drop-out + `s68` sentinel flip is the /qa deliverable; e2e
  BLOCKED-by-red-binary; 0122 re-test after W1+W2. Source-grounded corrections folded (Code is
  slim-only not a move; sig already returns CompilationError; load_object already exists;
  compile_constr_adt lands FULLY in W1). **Phase-3 exit gate met**: /arch interface set complete
  (Phase 2 + re-ruling); /qa has its plan; design docs current. Wave structure (Phase 4) already
  settled at 6. Ready for Phase 5 (Stage 1 QA-first N/A — no new failing tests; Stage 2 = W1
  `/dev backend`). Awaiting user go to fire W1.

- 2026-06-01: **W1 (Absorb) DONE — crate-narrow GREEN.** `/dev (backend)`: `cargo nextest
  run -p cranelisp-backend` **166/166 pass**; `cargo check --tests` 0 err / 0 warn. All 9
  work-steps done + ~7 extra S69/S70 renames (all test-code absorb, no scope creep). W1 stayed
  in scope (untouched: `compile_to_module` sig, `compile_to_object`, `Code::Primitive`,
  visibility, 4-fn ctor family). **Findings:** (a) `apply.rs:125` E0004 was NOT a payload reshape
  (corrects Rev 1 + /design) — the 4 arms already bound S70 payloads; real cause is `ResolvedCall`
  `#[non_exhaustive]` needing a wildcard arm (added `_ =>` codegen-error arm; **W6 confirm it masks
  nothing**). (b) ctor-as-Def needed per-field TYPES not just counts → backend-internal `CtorMeta`
  reconstructed from `DefKind::Constructor` + ctor `Def.scheme`; product-type (ctor name == type
  name → `TypeDef`) subtlety caught by 2 failing tests. (c) `compile_constr_adt` landed FULLY
  (nullary→`iconst tag`; data→consuming-arg-list per D24 + `emit_alloc`). FIXMEs 0099/0182/0191
  `git rm`'d (premise-dead, verified). **W2 feed:** codegen still round-trips `DefnVariant`→`Defn`;
  W2 may consume `DefnVariant` directly. Working tree uncommitted (review at W6). **Wave-gate: no
  open FIXME targeting /dev backend blocks W1→W2** (0221 IS the W2 work).

- 2026-06-01: **W2 (Conform boundary) DONE — crate-narrow GREEN.** `/dev (backend)`:
  166/166 pass, 0 warnings. `compile_to_module` → `Result<CompilationArtifacts, CompilationError>`
  + `module_aliases` param + direct GOT-slot write (D41 #2); `produce_disasm` added;
  `compile_to_object`/`CompilationResult`/`FunctionArtifacts`/`Code::Primitive`/`Code::ptr()`
  deleted; `Code` → `Jit(Arc<Jit>)`/`Linker(Arc<Linker>)`; `Linker::load_object`→`pub(crate)`;
  baseline regen #1. **Baseline correction:** the committed 2008-line baseline was noise-inflated
  (~624 lines of blanket/auto-derived impls from a pre-`--omit` cargo-public-api). Correct regen
  under the canonical `--omit` command = **~700 lines** — backend's TRUE surface. (Sizing narrative
  "2008→~1850" was off the noisy baseline; real target is ~700.)
- 2026-06-01: **W2 findings needing /arch (facade-vs-reality gaps surfaced by source):**
  - **Finding A — D41 #1 (`write_code` Code::Jit) NOT embodiable crate-narrow.** Facade
    target-states backend constructing `Code::Jit` directly. Source reality: int creates the `Jit`,
    passes `jit.jit_module()` (a `&mut M`) into `compile_to_module`, then `Arc::new(jit)` AFTER the
    call (`worker.rs:3296/3322`). Backend never owns the `Arc<Jit>`. /dev did the source-correct
    split: **backend does D41 #2 (GOT-slot store); D41 #1 (Code::Jit construction) stays in int.**
    Facade §53/§345-371 "backend constructs Code directly" is target-stating ahead of an ownership
    rotation int (S77) would need (relinquish `Jit` into the call + a `SymbolTable::write_code` API).
    → /arch ruling owed: final state (i) backend #2-only / #1-int, or (ii) ownership rotation.
  - **Finding C — `produce_disasm` made REAL (user-directed 2026-06-02).** Initial /dev finding:
    can't implement as specified (facade says reads `code_size` "from persisted entry metadata" —
    but `ModuleEntry::Def` doesn't persist it, and backend has no raw-bytes disassembler). **User
    correction:** int has no disassembler of its own (its `/disasm` handler just reads a backend-
    supplied string — `worker.rs:3461`, now red post-W2); the real blocker is the disassembler, NOT
    `code_size`. **capstone(+capstone-sys) is ALREADY in the dep tree** (`Cargo.lock:63/73`, via
    cranelift's `disas` feature) → backend takes it as a direct dep at ~zero build cost.
    **Resolution — make it real:** `produce_disasm(fq, code_size, symbol_tables) -> Result<String, _>`
    — **caller passes `code_size`** (it has it from the compile-time `CompilationArtifacts`; backend
    never sees int's `Introspection`); body resolves `fq` → GOT ptr → reads `ptr..ptr+code_size` →
    **capstone-disassembles** (works JIT + cache-hit). No entry-persistence, no `cranelisp-types`
    change. Honors the S70 on-demand intent (batch pays nothing). → /arch fixes the facade text
    ("caller-supplied `code_size` param", not "persisted entry metadata") + signs off the capstone
    direct dep; /dev completes the body (W3).
  - **Finding B — `module_aliases` now GENUINELY wired (good).** Facade target-stated the resolvers
    taking `module_aliases` but source did ad-hoc qualified-name parsing. /dev threaded it AND wired
    real §8.6.6 alias-prefix substitution (+ new test `resolve_got_target_follows_module_alias_prefix`)
    — not a dead param. Small behavioral conformance enhancement.
  - **Finding D — `CompilationArtifacts` in `lib.rs` not `artefact.rs`** (trivial; /design W5-fold call).
  - 0122 unaffected by W2 (GOT-slot write is JIT-mode only; the object `__cranelisp_got_{M}` Export
    path the defect names is unchanged). Re-test still owed W6.

### /arch corrections (2026-06-02) — Findings A + C enacted

`/arch` enacted the two user-approved W2 facade/Decision corrections (same class as the
`compile_to_object` retraction earlier this sprint: facade text target-stating something
incompatible with how the code actually works). Validated against source first
(`lib.rs:667–701` confirms backend writes the GOT slot but the `Code::Jit` construction stays
in int because backend only borrows `&mut M`; `artefact.rs` doc confirms the caller composes
`Code::Linker`; `jit.rs:486–513` confirms disasm is codegen-time `vcode` only; `Cargo.lock:63/73`
confirms capstone present via cranelift's `disas` feature).

**Finding A — who constructs `Code` (caller, both variants).** Corrected every facade/Decision/BC
passage that said backend constructs `Code::Jit` via `write_code`. New canonical statement:
**backend writes the GOT slot (`got().store_slot`, D41 #2); the caller composes the `Code`
lifecycle owner — `Code::Jit` from its owned `Arc<Jit>`, `Code::Linker` from the `LinkerArtefact`
— and installs it via `write_code` (D41 #1, the caller's).** No `SymbolTable::write_code`
requirement at backend's boundary. This makes the facade internally consistent with the symmetric
Linker path it already specified. Files: `facades/backend.md` §"Free functions" (new "Who constructs
`Code`" paragraph), §"Return shapes", §"`Code`", §"GOT-population observation" (+register_got_observer
rustdoc), §`#[non_exhaustive]` DTOs, BC-invariant-3, PIF Row 2, the CompilationResult Wave-3 prose;
`bounded-contexts.md` §3 "what crosses the boundary"; `decisions/0041*` (title + new S75-correction
box + §3 body); `interfaces.md` (Backend-hosted-`Code` narrative + the 3 boundary-summary rows at
1367/1878/1898); `design/arch/CLAUDE.md` D41 drain-backlog line (marked `[→ facades/backend.md]`).

**Finding C — `produce_disasm` is real (caller-supplied `code_size` + capstone).** Corrected the
signature to `produce_disasm(fq, code_size, symbol_tables)` and the prose: the **caller passes
`code_size`** (received in the compile-time `CompilationArtifacts`); backend does NOT read it from
"persisted entry metadata" (`ModuleEntry::Def` doesn't carry it; backend never sees int's
`Introspection`). Body resolves `fq` → GOT ptr → reads `ptr..ptr+code_size` → capstone-disassembles
(works JIT + cache-hit). Disasm correctly NOT in `CompilationArtifacts` (on-demand only; honours
S70 batch-pays-nothing intent). Files: `facades/backend.md` §"Free functions" (signature + prose),
`CompilationArtifacts.code_size` doc; `bounded-contexts.md` §3; `decisions/0041*` + CLAUDE.md
drain line; `interfaces.md` 1898 row.

**Capstone direct-dependency sign-off (/arch-authorised, /dev enacts W3).** `capstone = "0.12"`
(pulling `capstone-sys = "0.16"`) is blessed as a **direct** dependency of `cranelisp-backend`.
Already transitive via cranelift's `disas` feature (`Cargo.lock:63/73`) → ~zero incremental build
cost, no new transitive surface, no ABI implications. Recorded in `facades/backend.md` §"Consumed
surface". `/dev (backend)` adds the `capstone = "0.12"` line to `crates/cranelisp-backend/Cargo.toml`
in W3 under this sign-off (`/arch` does NOT edit Cargo.toml).

**/dev W3 follow-through.** (1) caller-constructs-`Code` is already W2's source split (int stays red;
re-wired S77 — no further W3 source change owed for Finding A beyond what W2 landed); (2) complete the
`produce_disasm` body (currently a typed-error stub at `lib.rs:839`) — add the `code_size: usize`
param, add `capstone` to the manifest, and implement the GOT-ptr → raw-bytes → capstone path.

**Sequence-diagram cascade.** Three diagrams asserted backend-constructs-`Code` via `write_code`:
- `exec-flow-compilation.mmd` — JIT + Linker arms corrected to "backend writes GOT slot; caller
  composes `Code` via `write_code`"; JIT arm also modernized off its pre-S70 `introspection`-param /
  `Result[(), ...]` / backend-writes-Introspection shape (it was stale on that axis too). **SVG
  re-rendered clean** with `mmdc`.
- `exec-flow-repl.mmd` (temp-closure eval Note) + `concurrency-symbol-table-entry.mmd` (PHASE 3 write
  Note + arrows + internals Note) — `.mmd` sources corrected to the caller-composes-`Code` split.
  **SVG re-render BLOCKED by a pre-existing parse trap** unrelated to this correction
  (`non-(begin)` paren at `exec-flow-repl.mmd:99`; similar at `concurrency-symbol-table-entry.mmd:63`)
  — the committed HEAD `.mmd` versions already fail to render at those lines; my edits (downstream of
  the trap) introduce no new error. The `.mmd` (canonical edit) is corrected; the stale `.svg`
  re-render needs the unrelated trap fixed first (separate cleanup, not in this correction's scope).
  `exec-flow-link.mmd` was already correct (delegates object cadence; no `Code`-construction claim).

- 2026-06-02: **W3 (Conform surface) DONE — crate-narrow GREEN.** `/dev (backend)`: nextest
  **167/167** (+1 = new `produce_disasm` test), check --tests 0-warning, baseline **700→650** (−50).
  Narrowed **49** `pub`→`pub(crate)`: the 3 /arch-ruled fns (`jit::intrinsic_symbols`,
  `exe::generate_startup_object`, `compiler::got_data_symbol_name` — each with linker-symbol ABI
  `///` before the drop; `got_data_symbol_name` canonical home = `compiler::`, the `cache::object`
  re-export removed) + internal codegen helpers (`FnCompiler`/`MatchContext`/the 6 `compiler::*`
  submodules/`resolve_func_arity`/`resolve_got_target`/`primitives_inline::*`/9 `heap::emit_*` fns).
  **`produce_disasm` made REAL** — capstone 0.12 added to Cargo.toml (arch-blessed); body resolves
  GOT ptr → reads `code_size` bytes → host-arch capstone disasm; new test passes. **Cache root
  re-export layer: already retired S67 W4** (verify-only, nothing to narrow). **W4 carries (noted):**
  `MATCH_EXHAUSTION_TRAP` is dead (zero consumers — match-exhaustion panics, not traps) → delete;
  `CompileContext` narrow is coupled to the pub `Jit::build_compile_context`/`compile_defn` → W4
  cascade; 2 pre-existing rustdoc warnings (`cache/serialize.rs:209` broken intra-doc link,
  `cache/mod.rs:48` unclosed HTML tag — W1/W2 diffs, not W3) → fix in W4/W5 (cargo doc clean is
  acceptance). **Stay/narrow judgment surfaced (for W6 /review + user):** agent held the `Jit`
  method-set / `TracedFnInfo` / `IntrinsicSymbol`/`IntrinsicFuncIds`/`IntrinsicIds` / `CompileArtifacts`
  / `CodeFinalizer` `pub` (int-consumed, facade Row 9/13/15 internal-but-exposed) rather than
  narrowing-everything-int-touches — defensible as boundary (the single-generic-entry design REQUIRES
  the caller to own + drive the `Module`/`Jit`, §2.5), but to be confirmed at W6 under the final-state
  principle.
- 2026-06-02: **JIT-setup target locked into facades by /arch** (subsection above). The W3
  judgment call is now RESOLVED toward narrowing: the `Jit` **orchestration** (`declare_intrinsics`/
  `declare_functions{_prefixed}`/`declare_imported_functions`/`compile_defn`/`finalize{_and_get_ptr}`/
  `get_finalized_ptr`/`get_ptr_by_name`/`build_compile_context`/`build_shared_isa` + module-level
  `build_isa`/`declare_intrinsics_generic`) + `IntrinsicSymbol`/`IntrinsicFuncIds`/`IntrinsicIds`/
  `CompileArtifacts` → **internal `pub(crate)`** (S75-actionable, a **W3-follow `/dev` pass**). Boundary
  `Jit` stays: constructor(s) + `jit_module()` + `Drop` + `jit_free_memory_call_count`; `CodeFinalizer`
  stays (generic bound). `intrinsic_symbols()` already `pub(crate)` (W3). **Target-stated S77:**
  `Jit::new(symbol_tables)` (derives GOT-from-symbol_tables + intrinsic-Imports-from-`INTRINSICS_TABLE`;
  collapses the `new*` trio — name-repurpose since it collides with the existing zero-arg `Jit::new()`);
  `intrinsics::INTRINSICS_TABLE` (published flat Import-catalog, Decision-0048-for-intrinsics);
  int's `pipeline.rs` parallel path collapses into `compile_to_module`. **Flagged open:** trace-as-observer
  (amends D40), `discover-tests`/`run-test` residual. **Next: W3-follow `/dev backend`** narrows the
  orchestration set (int `pipeline.rs` breaks → S77).
- 2026-06-02: **W3-follow (Jit orchestration narrow) DONE — crate-narrow GREEN.** `/dev (backend)`:
  167/167, check --tests 0-warning. All 17 items → `pub(crate)` (11 Jit methods + `build_isa`/
  `declare_intrinsics_generic` + 4 DTOs; `intrinsic_symbols` already pub(crate)). Baseline 650→584
  (−66). Boundary held: `Jit::new*`/`jit_module()`/`Drop`/`CodeFinalizer` stay pub. **Validate-first
  catch:** int's `build_isa` use is the 1-arg `cache::object::build_isa(is_pic)` (re-exported, NOT
  narrowed) — the 0-arg `jit::build_isa()` narrowed has zero external callers. Only int `pipeline.rs`
  breaks (S77). **W4 dead-code list** (now-`pub(crate)` no in-crate caller; `#[allow(dead_code)]`+note
  applied): `Jit::build_shared_isa` (delete), `Jit::declare_functions_prefixed` (delete),
  `IntrinsicSymbol::is_runtime` field (delete-or-wire-for-INTRINSICS_TABLE-S77); `Jit` fields /
  `CompileArtifacts` / `IntrinsicIds` are **fold candidates** (read only inside the narrowed methods
  whose driver is int's pipeline.rs — gain in-crate readers when S77 folds that path), NOT deletions.
  **Baseline-vs-HEAD note:** the committed git-HEAD baseline predates the sprint, so the working-tree
  584 reflects the full W1–W3-follow surface (correct current source); the large HEAD-diff is the
  accumulated sprint change, reviewed at W6/commit. **W4 clippy decision owed:** 126 endemic pre-existing
  `result_large_err` (every `CranelispError`-returning fn; not introduced this sprint) — box the
  workspace error variant (cross-crate, /arch) vs `#[allow]`-with-rationale (pre-existing) — W4 assess + /review.

- 2026-06-02: **W4 (Streamline) DONE except the ctor collapse — crate-narrow GREEN.** `/dev (backend)`:
  167/167; clippy + check --tests + `cargo doc` all clean; baseline stable 584. Deleted
  `Jit::build_shared_isa`, `declare_functions_prefixed`, `MATCH_EXHAUSTION_TRAP` (confirmed dead).
  `IntrinsicSymbol::is_runtime` KEPT for S77 (`INTRINSICS_TABLE` runtime/primitive split needs it; allow
  moved to the field). **`result_large_err`**: crate-scope `#![allow]` in `lib.rs` with rationale
  (pre-existing endemic; `CranelispError` is the `cranelisp-types` workspace error; boxing = separate
  cross-crate /arch decision; user-decided allow-not-box). +6 unmasked clippy lints fixed; 2 rustdoc
  warnings fixed (`cache/serialize.rs:209`, `cache/mod.rs:48`).
  **VALIDATE-FIRST CATCH — step 1 (4-fn ctor family deletion) BLOCKED:** the W1 premise (`compile_constr_adt`
  replaced the family) is FALSE — 3 live callers: `compile_constr_adt` DELEGATES to
  `compile_data_constructor_call` (apply.rs:599); `compile_var_apply` (constructor-as-call, apply.rs:334/353);
  `compile_var` (constructor-as-VALUE → closure, literals.rs:119/125/126). W1 added the `Expr::ConstrADT`
  arm but never finished the construct-path collapse the facade target-states (`backend.md:570`). This is
  **design-grade** (reroute constructor-as-call + decide the constructor-as-value closure path's fate),
  NOT mechanical streamline — and the constructor-as-value-closure path may legitimately NOT collapse into
  one handler. **Disposition (recommend B):** DEFER the collapse to a named backend-codegen slice (S77 /
  follow-on); the 4-fn family is all `pub(crate)` internal (off the boundary) so the alignment is unaffected;
  W5 folds the HONEST current state + corrects `backend.md:565/570` (single-handler = forward target, not
  done-claim — avoid the S74 phantom-claim trap). Second time the ctor-codegen area proved under-converged
  (W1 also). **Awaiting user call: defer (B) → W5, or collapse now (A).**

- 2026-06-02: **Constructor-collapse dig (/design backend) — precondition is a CROSS-CRATE GAP; facade
  "single handler" claim is FALSE.** User chose (A) "find the streamlined design." `/design backend`
  formalized the two-path model (one core `emit_adt_construct` + Path 1 inline `(Some 3)` + Path 2
  GOT-as-value `(map Some xs)`, primitives-symmetric per D43/48) in `design/backend/compile-to-module.md
  §2.6 — BUT verified the **Path-2 precondition does NOT hold**: constructors are NOT got-slotted
  (typecheck `register_constructors` adt.rs:332 assigns none) and NOT compiled-as-callable (int
  `derive_codegen_batch` worker.rs:3040 never batches `TypeDef`-synthesised ctor Defs). So the bespoke
  as-value closure (`compile_data_constructor_as_value`/`compile_ctor_wrapper_body`) is **load-bearing**
  (the only way `(map Some xs)` works), NOT dead. The facade's "single handler / dead family / ~200 LOC"
  is wrong; deleting the closure now regresses ctor-as-value.
  - **W4-doable (backend-only):** core-op unification — `compile_data_constructor_call`→`emit_adt_construct`
    (+ nullary `iconst` arm); route the inline site (`compile_var_apply` ctor branch), the `ConstrADT`
    Def body (`compile_constr_adt`), and the nullary site through it; KEEP `data_constructor_info`
    (path-1 recognition) + KEEP the as-value closure. RC-neutral core (consuming stays in callers,
    Decision 24 — no double-inc). Dedups 2 of 3 construct copies; names the core for S77.
  - **S77 (cross-crate enablement — the real collapse):** `/arch` Decision + typecheck got-slots ctor
    Defs + int batches them (constructors become callable got-slotted Defs, symmetric w/ primitives
    Decision 0048) → delete the as-value closure, route as-value through normal fn-as-value → the
    single-handler / ~200 LOC end state.
  - **W5 facade fold (/arch):** correct `backend.md` §"Constructor codegen" false claim → two-paths-over-
    one-core, ~200 LOC marked post-S77.
- 2026-06-02: **User correction — backend designs for FINAL state (constructors like primitives);
  the closure DELETES now.** The "int gap blocks backend / keep the closure" disposition was the
  int-deference this sprint rejects. Directive: *design backend to work like primitives and EXPECT
  GOT entries; int produces them at S77 — not backend's concern.* `/design backend` rewrote §2.6
  accordingly. **Validated clean:** the facade (`backend.md:567/570`) ALREADY target-states this
  (ctor-as-value via the `got_slot` address, no closure synthesis) — the W4 dig had diverged from the
  facade; this RESTORES coherence. Path 2 needs nothing new: `compile_operator_as_value`/
  `compile_fn_as_value` build the same GOT-indirect closure; `is_known_function` gates on
  `resolve_got_target`; arity works for ctors (field names = `param_names`). As-value = "delete the
  special branch, fall through to fn-as-value." **W4 collapse (full, backend-only, fire now):** unify
  core → `emit_adt_construct`; DELETE `compile_data_constructor_as_value` + `compile_ctor_wrapper_body`
  + the `compile_var` ctor-as-value branch (fall through) + fold `nullary_constructor_tag`; keep
  `data_constructor_info` (path-1 inline recognition); RC-neutral core. **Crate-narrow green via
  harness-populated GOT slots** (`make_def_entry_slot` pattern proves both paths incl. as-value). **One
  pending-S77 carry:** real-pipeline e2e `(map Some xs)` (needs int's GOT-entry production) → /qa
  authors failing-not-ignored in `tests/` with `FIXME(/arch)`. **S77 handoff (FIXME target /arch):**
  typecheck got-slots `DefKind::Constructor` + int `derive_codegen_batch` enumerates ctor Defs (mirrors
  primitives Decision 0048). **W5 facade fold:** §2.6 now realigned TO the facade — no contradiction;
  "single handler / ~200 LOC" achieved in backend this sprint, int got-entries = S77 runtime-completeness.

- 2026-06-02: **W4 (Streamline) COMPLETE — incl. the constructor collapse.** `/dev (backend)`:
  **168/168** (+1 closure-deletion guard), 0 warnings, clippy + `cargo doc` clean, baseline unchanged
  584, **net −76 LOC**. Constructor collapse done the FINAL-STATE way: bespoke as-value closure
  (`compile_data_constructor_as_value` + `compile_ctor_wrapper_body`) DELETED; constructor-as-value
  falls through to `compile_fn_as_value` (the generic GOT/fn-as-value path, same as operators); all 3
  construct sites unified through `emit_adt_construct` (RC-neutral, Decision 24 stays in callers);
  `nullary_constructor_tag` folded; `data_constructor_info` kept (path-1 inline recognition). As-value
  proven crate-narrow via the `make_def_entry_slot` two-stage harness (got-slot ctor Def + compile its
  `ConstrADT` body + run fn-as-value over it). Earlier W4 deletions (build_shared_isa,
  declare_functions_prefixed, MATCH_EXHAUSTION_TRAP) + `result_large_err` allow + rustdoc fixes also done.
  **S77 carries (named, not backend's concern):** (1) int-enablement — typecheck got-slots
  `DefKind::Constructor` + int `derive_codegen_batch` enumerates ctor Defs (mirrors primitives D0048);
  documented `compile-to-module.md §2.6.5`; **W5 /arch files the FIXME (target /arch)**. (2) pending e2e
  `(map Some xs)` real-pipeline → /qa authors failing-not-ignored in `tests/` (Phase 6). Backend now at
  conformed+streamlined final state.

- 2026-06-02: **W5 (Retire) plan + the backend-vs-cache distinction (user-confirmed).** `backend-cache`
  is a backend **submodule** (`crates/cranelisp-backend/src/cache/`, the persistence half — `Linker`
  mmap/object loading is Cranelift-adjacent per Principle 3; int orchestrates via `src/cache.rs::ObjectCache`,
  backend provides the mechanism). The separate `facades/backend-cache.md` was a **Sprint-67
  doc-manageability sub-facade** (~60 pub items the parent was silent on), **NOT a bounded context.**
  **User directive: maintain the distinction — backend IS a bounded context; backend-cache is an
  IMPLEMENTATION DETAIL.** So the W5 fold:
  - `backend.md` → `lib.rs` `//!` boundary + per-item `///`; cross-surface narrative + backend's
    bounded-context invariants → `bounded-contexts.md §3`.
  - `backend-cache.md` → **cache submodule rustdoc ONLY** (`cache/mod.rs` `//!` + per-submodule `//!`
    + per-item `///`); the 5 cache invariants are **internal implementation invariants** documented
    there — **NOT** promoted into `bounded-contexts.md` (no §3a, no BC-level cache entry). The
    bounded-contexts doc stays backend's bounded-context statement.
  - Both facade FILES `git rm`'d (one crate's retirement; the 7th data point); `design/arch/CLAUDE.md`
    exception list → 8 retired-facade-files; /qa drops both from `facade_compliance.rs` + s68 sentinel
    (backend → MUST-BE-ABSENT). The W5 rustdoc folds **post-W4 current source**; S77 targets
    (`Jit::new(symbol_tables)`, `INTRINSICS_TABLE`, ctor GOT-entries) fold as **forward notes/FIXMEs,
    NOT current-state claims** (S74 phantom-claim discipline).
  - **W5 fires:** W5a `/design backend` (fold mapping) → `/dev backend` (write rustdoc); W5b `/arch`
    (git rm + BC §3 + CLAUDE.md + S77 int-enablement FIXME + cross-ref sweep); W5c `/qa` (compliance
    drop-out + sentinel). User approved proceeding with W5a.

- 2026-06-02: **W5a (retirement rustdoc fold) DONE.** `/design backend` authored
  `design/backend/w5-retirement-fold-mapping.md` (source-validated; 14 phantom/stale facade items
  flagged DROP, 5 S77-forward marked forward, BC-vs-impl-detail distinction held). `/dev backend` wrote
  the rustdoc: `lib.rs //!` boundary narrative + cache submodule rustdoc (5 cache invariants, impl-level)
  + `artefact.rs`/`ObjectArtefact` honest rewrite + S77 forward notes. **Gates: `cargo doc` 0 warnings,
  nextest 168/168, check/clippy 0, `public-api.txt` byte-identical (doc-only proof).** Most per-item ///
  was already correct in source; net new = lib.rs //! + cache //! + artefact rewrite. Rustdoc is now the
  canonical surface → ready for W5b. **Flag (non-blocking):** `got_data_symbol_name` canonical home is
  `compiler`, not `cache::object` (facade implied otherwise) — future /design note.

### /arch W5b retirement (2026-06-02)

**Both backend facades retired — 7th + 8th facade-retirement data points (one crate, two facade files).**

- **Verify-before-delete (S74 discipline) — PASSED.** Spot-checked the W5a rustdoc carries the
  facade substance before deleting: `crates/cranelisp-backend/src/lib.rs //!` carries the boundary
  narrative (the three codegen entries + "who composes `Code`" + persistence pointer);
  `crates/cranelisp-backend/src/cache/mod.rs //!` carries the 4-submodule shape + all **5 cache
  invariants** (lines 36–59) + the version-bump forbidden-pattern note. Confirmed the rustdoc
  correctly **dropped the phantom/stale facade claims**: source `Code` has no `Primitive` variant
  (the `///` notes it deleted; primitive-ness reads from `kind: DefKind::Primitive`), `compile_to_object`
  is a tombstone comment only (no live fn; NOTE at `lib.rs:1016`), `ObjectArtefact` is honestly
  documented as "not currently produced" (phantom shape kept as a typed shape with an honest `///`).
- **`git rm`** `design/arch/facades/backend.md` + `design/arch/facades/backend-cache.md` (both had
  in-flight W2/W3 local edits — superseded by retirement; removed with `-f`, recorded in git history).
- **BC §3 authored** (`bounded-contexts.md`): backend's **7 bounded-context invariants** (single-entry-per-mode
  D23; uniform consuming convention D24; lifecycle-owner-on-`.code` + ptr-in-GOT D25+41 with **caller
  composes `Code` both variants**; `defined_symbols()` predicate D22; per-symbol reclaim safety D41;
  two-GOT/one-CLIF D23; bare-name+Local linkage D36) + a **"what crosses the boundary" cross-surface
  summary** (the 3 codegen entries + `Code`/`Jit`/`Linker` + the cache contract a driver drives + the
  GOT-observer extension point + the heap-layout ABI) + the Per-surface-documentation retirement note.
  **NO cache content in BC, NO §3a, NO BC-level cache entry** — the user-confirmed governing distinction
  (backend = bounded context; backend-cache = implementation detail of backend) held. The 5 cache
  invariants live in the cache submodule rustdoc (W5a), not in BC §3 — a closing paragraph in §3 states
  this explicitly. **This overrides the pre-W5b SPRINT.md plan (lines 112, 142: "cache as §3a; carry all
  twelve invariants") per the user-confirmed W5b brief.**
- **`design/arch/CLAUDE.md` → 8 retired.** Facade-line updated (`backend.md` → BC §3 + source rustdoc;
  `backend-cache.md` → cache submodule rustdoc, **impl-detail, NOT BC**); the only remaining live facade
  is `facades/int.md` (int, the last crate). Also repointed the D41 drain-backlog entry and the
  baseline-diff-discipline note off the deleted files.
- **S77 int-enablement FIXME filed: 0249** (`target: /arch`) — backend's constructor-as-value (Path 2) +
  the `Jit::new(symbol_tables)`/`INTRINSICS_TABLE` targets assume constructor `Def`s are got-slotted
  callable; the S77 enablement is (a) typecheck got-slots `DefKind::Constructor` entries
  (`register_constructors`, currently no `got_slot`), (b) int `derive_codegen_batch` enumerates the
  `TypeDef`-synthesised ctor `Def`s into the compile batch. Mirrors primitives Decision 0048; points at
  `design/backend/compile-to-module.md §2.6.5`. (Number 0249 chosen because 0245–0248 are consumed by
  S73/S74 history — 0244 is the highest extant file, but the safe non-colliding next is 0249.)
- **Cross-ref sweep → 0 dangling canonical refs.** Repointed **12 canonical references** across 5 docs
  to the new homes (`lib.rs`/`code.rs`/`got_observer` rustdoc / cache submodule rustdoc / BC §3):
  `interfaces.md` (4), `facades/int.md` (2), `sequences/exec-flow-compilation.mmd` (3 — Notes; `.svg`
  re-rendered via mmdc, no `;`-trap), `CLAUDE.md` (2 — D41 drain entry + baseline-diff discipline),
  `decisions/0041` correction-box (1 — archive-style "retired S75 → BC §3 + source rustdoc" pointer).
  Historical/draining docs (`archive/`, `legacy/`, `*-audit-s69/s70`, `settled-verdict-s70`, `sprint-65/66`,
  draining `decisions/0048`, the fixmes register) retain their refs per the S74 precedent (only the
  canonical set must be clean). **Closed + deleted FIXME 0223** (facade-text-retired-but-cited) — its only
  live citation site was `facades/backend.md` (ConstructorInfo), now gone with the facade; remaining
  `PrimitiveKind`/`ConstructorInfo` cites are all in historical `*-audit-s69.md` docs (acceptable to retain).
- **Phantom/stale text the rustdoc fold correctly dropped (W5a cross-check confirmed):** `Code::Primitive`
  variant + `ptr` field (gone from source — `code: None` + `kind`-derived); `compile_to_object` free fn
  (retracted S75 W2 — tombstone comment only); `ObjectArtefact` as a live return shape (no producer —
  honest "not currently produced / delete-candidate" `///`); `CompilationResult` (does not exist); the
  `<M>`-over-`&SymbolTables<Code,()>` signature (source is `<M,C,L>` over raw `&DashMap`); `load_object`
  4-arg-with-`module_aliases` (source 3-arg); `operators.rs` (file gone); the `primitive_for_trait_method`
  / REV-5 / PIF-Row-1-8 tombstones (git history). All correctly folded as forward-notes or dropped, not
  carried as current-state claims.
- **Note (`/qa` W5c carry):** backend + backend-cache DROP OUT of `tests/facade_compliance.rs` per
  `feedback_retired_facade_drops_compliance` — that's /qa's W5c deliverable, not this fire.

- 2026-06-02: **W5b + W5c DONE — W5 (Retire) COMPLETE; 7th retirement data point.** **W5b (/arch):**
  `git rm` both `facades/backend.md` + `backend-cache.md`; `bounded-contexts.md §3` authored with the
  **7 backend BC invariants, 0 cache content (NO §3a)** — the user distinction enacted (overrode the
  earlier "§3a/12-invariants" plan text, now annotated superseded at lines 142/500); `design/arch/CLAUDE.md`
  → **8 retired facade files**; **FIXME 0249** filed (target /arch — S77 ctor-got-slot enablement:
  typecheck got-slots `DefKind::Constructor` + int `derive_codegen_batch` enumerates ctor Defs; mirrors
  D0048); FIXME 0223 closed (citation died with the facade); **12 canonical refs repointed, 0 dangling**;
  `exec-flow-compilation.svg` re-rendered. **W5c (/qa):** `facade_compliance.rs` → empty `facade_pairs()`
  tombstone (sentinel anchor preserved; orphan test vacuously green); `s68` sentinel → primitives/
  intrinsics/backend all MUST-BE-ABSENT. Dry-run validated (8 facades absent, int.md only live);
  LIVE run blocked-by-red-binary (not a gap). No new e2e; `(map Some xs)` e2e → Phase-6 /qa carry.
  **Carry (non-blocking):** `interfaces.md:957/1231` still defines retired `ConstructorInfo` (pre-existing
  S70 staleness; future /arch interfaces cleanup). **Next: W6 — /review backend** (whole-sprint change-set).

### /review (backend) W6 (2026-06-02)

**Reviewer:** `/review`, narrow-deployed to `cranelisp-backend`. **Scope:** whole-sprint
W1–W5 change-set (uncommitted working tree) against the retired-facade-substance-now-source-rustdoc
+ `bounded-contexts.md §3` + `design/backend/compile-to-module.md` (incl. §2.6) + the SPRINT.md
Phase-2 rulings/corrections.

**VERDICT: PASS-WITH-FINDINGS** (2 Suggestions, 0 Blocker, 0 Important). The change-set is
sound and at conformed+streamlined final state; the only findings are stale doc-comment
function-name inventories, fixable-not-carried per the S74 lesson — but `/review` flags, does
not fix.

#### Gate verification (read-only cargo, sole active agent)

| Gate | Expected | Actual | Result |
|---|---|---|---|
| `cargo nextest run -p cranelisp-backend` | 168/168 | **168 passed, 0 skipped** (0.24s) | PASS |
| `cargo clippy -p cranelisp-backend --all-targets` | clean modulo `result_large_err` allow | **0 warnings in `crates/cranelisp-backend/src`** (the surfaced lints are all in dep crates `cranelisp-types`/`cranelisp-platform`, built incidentally) | PASS |
| `cargo doc -p cranelisp-backend --no-deps` | clean | **0 warnings** | PASS |
| `public-api.txt` accuracy | 584, accurate to source | regen under canonical `--omit blanket-impls,auto-derived-impls` is **byte-identical** to the committed baseline (584 lines) | PASS |

int-side breakage confirmed all expected/S77; no accidental backend regression — the
constructor-as-value end-to-end guard (`constructor_as_value_falls_through_to_fn_as_value`)
runs the JIT-compiled consumer and reads back the constructed ADT field; inline `(Some 3)`
path covered by existing `test_compile_adt_data_constructor`.

#### Per-checklist findings

1. **§6 emitted-call-ABI guardrail — HELD.** `grep` for `#[no_mangle]`/`#[export_name]`/`pub extern`
   in `src/` returns nothing — backend has zero own emitted-call symbols, so §6 is moot for
   backend-owned symbols (as the Phase-2 review established). The 3 named narrows
   (`jit::intrinsic_symbols`, `exe::generate_startup_object`, `compiler::got_data_symbol_name`)
   each carry their linker-symbol + relocation ABI in `///` before the visibility drop (confirmed
   in the W3 done-note + spot-checked `compile_operator_as_value`'s `got_data_symbol_name`
   consumer). Orchestration narrows (`Jit::declare_*`/`compile_defn`/`finalize*`/`build_compile_context`)
   correctly `pub(crate)` — only int's parallel `pipeline.rs` reaches them out-of-crate; int
   breaks S77 (expected). CONFIRM.
2. **Boundary correct — CONFIRM.** `compile_to_module` writes only the GOT slot via
   `table.got.store_slot(slot, ptr)` (D41 #2, `lib.rs:768`); `Code::Jit` construction stays in
   the caller (D41 #1) — matches BC inv 3 + the Finding-A correction (backend borrows `&mut M`,
   never owns `Arc<Jit>`). Mode-agnostic: object-mode short-circuits when
   `try_get_finalized_function` returns `None` (`lib.rs:753–757`); reads bodies/slots from
   `symbol_tables`. `produce_disasm` is REAL — caller-supplied `code_size` param, resolves GOT
   ptr → `from_raw_parts(ptr, code_size)` → capstone `disasm_host` (`lib.rs:909–962`); SAFETY
   documented; no fabricated output. `Code` slimmed to `Jit(Arc<Jit>)`/`Linker(Arc<Linker>)` —
   no `Primitive`, no `ptr` field, no `ptr()` accessor; `#[non_exhaustive]`; both ctor assoc fns;
   manual `Debug`; SAFETY on the unsafe `Send`/`Sync` impls. `Jit` minimal boundary
   (`new*`/`jit_module()`/`Drop`) + `CodeFinalizer` stay `pub`.
3. **Constructor two-path collapse — SOUND.** One `emit_adt_construct` core (`apply.rs:622`),
   RC-NEUTRAL — nullary→`iconst tag`, data→`emit_alloc`+tag store+field stores; the consuming
   convention (Decision 24) stays in callers, no double-inc, with an explicit `/dev`-must-preserve
   note in the `///`. Path-1 inline `(Some 3)` (`compile_var_apply`, `apply.rs:353`) + the
   `compile_constr_adt` ConstrADT Def body (`apply.rs:606`) + the nullary `compile_var` reference
   (`literals.rs:123`) all route through it. Path-2 as-value: the dedicated data-ctor-as-value
   branch is DELETED; `compile_var` falls through to `is_known_function → compile_fn_as_value`
   (`literals.rs:152`), with an honest NOTE on the S77 GOT-entry dependency. `compile_data_constructor_as_value`
   + `compile_ctor_wrapper_body` + `compile_data_constructor_call` confirmed gone from source.
   `nullary_constructor_tag`/`data_constructor_info` kept as Path-1 *recognition* (emission folded;
   recognition stays — matches §2.6.3). The `ResolvedCall` `#[non_exhaustive]` wildcard arm
   (`apply.rs:315`) masks NOTHING — all 4 real variants (BuiltinFn/TraitMethod/SigDispatch/AutoCurry)
   are handled explicitly above it; the wildcard is a codegen-error-naming-the-variant arm. CONFIRM.
4. **Rustdoc fold clean — 0 phantom claims.** `lib.rs //!` + `cache/mod.rs //!` (5 cache invariants,
   labelled "internal implementation invariants") document current source. S77 items marked forward
   (`jit.rs`: `FIXME(S77 INTRINSICS_TABLE)`, `target (S77)` notes for `Jit::new(symbol_tables)`),
   NOT current-state. `artefact.rs`/`ObjectArtefact` honest "**not currently produced** /
   delete-candidate" `///`; header rewritten (no `compile_to_object → ObjectArtefact` phantom).
   BC §3 carries the 7 backend invariants and EXPLICITLY states there is no §3a / no BC-level cache
   entry; the 5 cache invariants live in cache submodule rustdoc only — user distinction held. CONFIRM.
5. **Gate — verified above (all PASS).** No accidental backend regression.
6. **S77 carries properly deferred — CONFIRM.** FIXME 0249 (`target: /arch`) names the ctor
   got-slot enablement (typecheck `register_constructors` got-slot + int `derive_codegen_batch`
   enumeration), mirrors Decision 0048, points at `compile-to-module.md §2.6.5`. The `(map Some xs)`
   Phase-6 e2e named as /qa carry (failing-not-ignored). `interfaces.md:957/1231` `ConstructorInfo`
   staleness named (pre-existing S70, future /arch cleanup). None silently dropped.

#### Findings

- **Suggestion 1 (`target: /dev backend`)** — `crates/cranelisp-backend/src/compiler/mod.rs:9`:
  the module `//!` rustdoc still lists `MATCH_EXHAUSTION_TRAP` as a "`pub` codegen primitive", but
  the const was DELETED in W4 (confirmed: only this comment references it). Stale inventory in a
  doc-comment — no behaviour impact, but a future reader is misled. *Recommendation:* drop the
  `MATCH_EXHAUSTION_TRAP` mention from the `//!`. Trivial; fix-not-carry per the S74 lesson.
- **Suggestion 2 (`target: /dev backend`)** — `crates/cranelisp-backend/src/compiler/apply.rs:4`:
  the file header comment lists `compile_data_constructor_call` among the file's functions, but it
  was renamed to `emit_adt_construct` in W4 (confirmed gone). Stale function-name inventory.
  *Recommendation:* update the header comment to `emit_adt_construct` (+ `compile_constr_adt`).
  Trivial; fix-not-carry.

Both Suggestions are doc-comment-only stale-inventory drift (not phantom *behaviour* claims — the
S77/ObjectArtefact phantom-claim discipline is clean). No FIXME filed for Suggestions per `/review`
classification; surfaced here for `/dev backend`'s next pass. `code.rs` test-comment staleness
(`Code::Jit { jit, ptr }` struct-form at `code.rs:131,138`) is a third instance of the same class —
folded into the same recommendation (test-comment, even lower stakes).

**No Blocker, no Important.** Backend is at the conformed + streamlined + retired final state;
crate-narrow green; int red is expected and S77-tracked. Sprint may proceed to close pending the
two trivial doc-comment fixes (`/sprint` + user decide fix-this-sprint vs carry).

## Outcome (Phase 7 — DRAFT, pending user close approval)

S75 brought **`cranelisp-backend`** — the heaviest crate — to a sound, conformed, streamlined,
self-documenting final state via the four-step alignment, and **retired both `facades/backend.md`
+ `facades/backend-cache.md`** (the **7th retirement data point**; one crate, two facade files).
Crate-narrow green independent of the backend-downstream `int` red cascade (same shape as S72–S74).

### Delivered
- **W1 Absorb** — the 202-error (41 lib) S69-types-lock + S70-frontend-reshape cascade absorbed:
  `HeapCategory` import repoint (→ `crate::heap`); `ConstructorInfo`→`DefKind::Constructor`/`CtorMeta`
  (per-field types, product-type subtlety); `ModuleFullPath` newtype opacity; `ModDecl.visibility`;
  `ModuleEntry::Reexport`/`Constructor` collapse; `Defn`→`DefnVariant`; `Expr::Lambda` reshape;
  `compile_constr_adt` arm; `ResolvedCall` `#[non_exhaustive]` wildcard. **3 stale-orphan FIXMEs
  (0099/0182/0191) deleted** (premise-dead, verified).
- **W2 Conform boundary** — D41 rotation (`compile_to_module → Result<CompilationArtifacts,
  CompilationError>` + `module_aliases`; `produce_disasm`; `CompilationResult`/`FunctionArtifacts`
  deleted); **`compile_to_object` stub deleted** (the single-parameterised-entry design affirmed —
  user-surfaced); `Code` slim (`Jit(Arc<Jit>)`/`Linker(Arc<Linker>)`; `Primitive` + `ptr()` removed;
  **caller composes `Code`**, backend writes only the GOT slot — D41 #1/#2 split, symmetric Jit/Linker);
  `Linker::get_symbol → Result`; `Linker::load_object → pub(crate)`. **Baseline correction:** the
  committed 2008-line baseline was ~624 lines of pre-`--omit` noise; true surface ~700.
- **W3 + W3-follow Conform surface** — 3 emitted-call-ABI narrows (`jit::intrinsic_symbols`,
  `exe::generate_startup_object`, `compiler::got_data_symbol_name`) each with linker-symbol ABI `///`
  before the drop; ~66 internal items → `pub(crate)` incl. the **Jit orchestration** (the W3
  "keep-pub-for-int" judgment call **reversed** to narrow — final-state, not int-deferential);
  **`produce_disasm` made real** (capstone + caller-supplied `code_size`). Baseline 700→584.
- **W4 Streamline + constructor collapse** — dead-code deletes (`build_shared_isa`,
  `declare_functions_prefixed`, `MATCH_EXHAUSTION_TRAP`); `#![allow(clippy::result_large_err)]`
  with rationale (pre-existing endemic; `CranelispError` types-owned; boxing = separate /arch);
  2 rustdoc fixes. **Constructor two-path collapse** (primitives-symmetric): one RC-neutral
  `emit_adt_construct` core; bespoke as-value closure (`compile_data_constructor_as_value`/
  `compile_ctor_wrapper_body`) **deleted**; constructor-as-value falls through to `compile_fn_as_value`
  (GOT/fn-as-value path). Net **−76 LOC**.
- **W5 Retire (7th data point)** — rustdoc fold (`lib.rs //!` boundary + cache submodule rustdoc +
  `artefact.rs`/`ObjectArtefact` honest rewrite + S77 forward-notes; 14 phantom/stale facade items
  dropped); both facades `git rm`'d; **`bounded-contexts.md §3` = 7 backend BC invariants, NO cache
  content** (`backend-cache` is an IMPLEMENTATION DETAIL → cache submodule rustdoc only — user
  distinction); `design/arch/CLAUDE.md` → **8 retired facade files**; `facade_compliance.rs`
  drop-out + `s68` sentinel (backend MUST-BE-ABSENT); **FIXME 0249** filed (S77 enablement); FIXME
  0223 closed; 12 cross-refs repointed, 0 dangling canonical.
- **W6 Review** — **PASS-WITH-FINDINGS** (0 Blocker, 0 Important; 2 trivial stale-doc Suggestions
  fixed-not-carried in-sprint). All 6 checklist items CONFIRM.
- **Acceptance met:** `cargo nextest run -p cranelisp-backend` **168/168** standalone; clippy +
  `cargo doc` clean; `public-api.txt` 584 (under the `--omit` convention); both facades retired,
  0 dangling canonical refs. Workspace-wide green explicitly NOT in scope (int red until S77).

### Deferred (with rationale)
- **S77 int host-wiring + cross-crate enablement** — **FIXME 0249**: typecheck got-slots
  `DefKind::Constructor` + int `derive_codegen_batch` enumerates ctor Defs (→ constructors callable,
  mirrors primitives D0048); the `Jit::new(symbol_tables)` collapse; `intrinsics::INTRINSICS_TABLE`;
  int's parallel `pipeline.rs` JIT path collapsing into `compile_to_module`. All **target-stated in
  rustdoc as forward** (not current-state claims), realized S77. Plus int FIXMEs 0242/0098/0187/0214
  + platform host-wiring 0229–0235.
- **`(map Some xs)` real-pipeline e2e** — Phase-6 `/qa` carry (needs int's S77 GOT-entry production).
- **0122** (`--link` GOT-alignment defect) — re-test blocked-by-red-binary; not alignment work.
- **`interfaces.md` `ConstructorInfo` definition staleness** (pre-existing S70) — future /arch interfaces cleanup.
- **Workspace-wide green** — int red until S77.

### Findings / lessons
- **Validate-against-source-first earned its keep repeatedly** — the facade/plan was wrong ≥5×:
  the "new `ResolvedCall` variant" (actually `#[non_exhaustive]`); the W1 "`compile_constr_adt`
  replaced the 4-fn family" premise (false — 3 live callers); the "single handler / dead family /
  ~200 LOC" claim (false — constructors aren't callable Defs; the as-value closure was load-bearing);
  14 phantom facade items at retirement; the 2008 noise-baseline. The discipline prevented deleting
  load-bearing code and folding phantom claims.
- **Final-state-not-int-deferential (user-driven)** — the recurring correction: backend goes to its
  bounded-context final shape; int's red/in-flux state is NOT a reason to preserve surface or carry
  scaffolding. Reversed the W3 Jit-orchestration "keep-pub" call; deleted the constructor as-value
  closure (backend expects GOT entries like primitives; int produces them S77).
- **Single-entry codegen affirmed** — `compile_to_module<M>` is THE entry; `compile_to_object` was
  accretion (user's "single entry point, that's why the type param exists" probe). `load_object`
  (cache-hit, no codegen) + `produce_disasm` (on-demand) are the genuinely-separate entries.
- **Constructors are primitives-symmetric** — GOT-dispatched Def + inline-substitution + as-value
  via the generic GOT path; the cross-crate enablement (constructors-as-callable-Defs) mirrors D0048.
- **backend-cache is an implementation detail, not a bounded context** (user distinction) — folded
  to the cache submodule rustdoc only; BC §3 stays backend's bounded-context statement.
- **Principles check (for Phase 7 review):** Principle 8 (interim-architecture) honoured — S77
  deferrals are target-stated, not half-built; the §6 emitted-call-ABI guardrail held (backend has
  no own externs; honest narrow set was internal + 3 ABI-documented); facade-retirement pattern now
  at 7 data points; manifestation-site + decision-cascade disciplines held. No principle gap surfaced.

### Phase 6 — recommend WAIVE
No language-visible change (internal conform/retire; the constructor collapse is behaviour-preserving,
verified by the crate-narrow guard; the `(map Some xs)` runtime is an S77 e2e carry). Same posture as
S69–S74. **User to confirm waiver.**

### Close (pending user approval — NOT yet enacted)
Whole sprint is **uncommitted** (standing rule). On approval: archive `SPRINT.md` → `sprints/archive/sprint-75.md`,
update `sprints/ROADMAP.md`, commit. **User confirms close + commit explicitly** (+ branch-vs-main per preference).
