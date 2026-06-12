# Sprint 80: Phase G closeout — platform-ADT round-trip + `main : IO _` conformance sweep

**Status**: ~~PHASE 1 SCOPE DRAFT~~ → ~~PHASE 2 ARCH REVIEW~~ → ~~PHASE 3 DESIGN~~ → ~~PHASE 4 WAVE ORG~~ → **PHASE 5 LANGUAGE (READY — awaiting go)** | PHASE 5 LANGUAGE (ACTIVE) | PHASE 6A ASSESSMENT | PHASE 6B ACTION | PHASE 7 CLOSE | COMPLETE

**Goal**: Retire the 7 standing reds by finishing the two pillars S79 deferred — complete the platform-ADT round-trip (pillar A) and enforce `main : IO _` suite-wide with an output-coverage reshape (pillar B) — leaving the suite fully green.

## Scope

S79 closed at **1196 passed / 7 failed / 8 skipped**, the 7 reds being *exactly* the two deliberately-carried FIXMEs (no stragglers). S80 drives both to green. We remain in **Phase G (Ring 4 — Effects/platforms)**; this is its closeout. The two pillars are largely disjoint (platform/backend/qa vs typecheck/qa/examples) → parallelizable across pillars; both converge on `/qa` for the green-up.

### Pillar A — Platform-ADT round-trip completion (clears 6 reds + adds drift coverage)

The platform-ADT-round-trip *machinery* landed S79 (R1 `--link` wiring, 0318 platform-fn-IO, the `shapes` fixture, the product-ctor-as-`Def` correction making `read_field("w")` reachable). The 6 `tests/spec_platforms_adt.rs` tests ride RED on one remaining layer: the test program defines `Rectangle` in its **entry module**, but the platform sig is FQ `shapes/Rectangle`, so module `shapes` has no `Rectangle` to resolve.

- **0323** — make `Rectangle` a loadable `shapes` `.cl` module the program imports (`(import [shapes [Rectangle]])`), per `platform-interface.md` §2 (q-assoc-discovery); ensure the `shapes` ADT module is loaded/resolvable during `register_platform_in_tc` sig checking; regenerate `platforms/shapes/src/shapes.platform-schema` (real `w`/`h` field names post-0319) + rebuild the dylib → round-trip + dual hash-gate + cache-restore go green. **Discovery-shaped**: this path has never run e2e and has surfaced one layer per exercise (FQ-split → resolve_named → arity → display → module-loading); budget a triage step.
- **0289 items 4-5** — on the same fixture: perturbed-ABI DLL e2e (`AbiVersionMismatch { expected, found }`) + dispatch-error-with-fn-name e2e (`DispatchError { fn_name }`). The e2e companions to the already-unit-proven drift paths. (Items 1-3 — clean round-trip + build-load-embed walk + dual hash-gate — overlap 0323 and complete with it.)

### Pillar B — `main : IO _` enforcement + suite-wide conformance sweep (clears 1 red)

The spec MUSTs (`02-grammar.md:25`, `10-io.md:244`, `12-runtime.md:173`) that a batch `main` returns `IO _`; the compiler leniently accepts bare-`Int`, and existing tests positively certify the violation. `batch_main_pure_int_return_is_rejected` rides RED as the forcing guard.

- **0317** — (1) `/spec` confirms the MUST stands as enforceable + upgrades the three stale `[R4 S10]` annotations; (2) **`/dev` (int — `src/exe.rs`)** rejects a batch `main` whose return type is not `IO _`, with a clear `(Fn [] (IO _))` error — a one-arm deletion in `classify_main_return_type` (the `Type::Int` accept arm); **NOT typecheck** (Phase-2 arch correction — typecheck has no clean batch-vs-REPL signal; the REPL-exemption lives at the int execution boundary); (3) `/qa` suite-wide sweep — ~125 batch bare-`Int` mains across ~11 test files → `IO` (`(pure 0)` smoke / `(print …)` observable), fix the 3 test-design defects that certify the violation, rework the examples exit-code-checksum convention; (4) **output-coverage reshape** — `run_through_all_modes_output` stdout harness + convert the mode-equivalence corpus so the majority of programs produce + assert observable output verified byte-equivalent across REPL/`--run`/`--link` (today 3 of 911); (5) `/examples` (~22 files) + `/port` (exemplar inline repros) rewrap their mains; (6) the RED guard flips green.

### Out of scope (deferred, with rationale)

- **0316** — import-ambiguity model decision + `resolve_with_fallback` unification (collapses the S78 5×-duplicated prelude-fallback retry). Design-led, blocks nothing, no red rides on it. Deferred to a focused S81 design increment alongside any other module-resolution debt. *(User chose "both pillars" over the import-model rider.)*
- **Multi-platform `--link`** — the `cranelisp_platform_manifest` symbol collision (single-platform fully wired S79). Future item; not on any S80 red.

## FIXME debt

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0323 | /qa | open | Pillar A — platform-ADT round-trip: `shapes` module loading + schema regen (6 reds). Discovery-shaped. |
| 0289 | /qa | open | Pillar A — perturbed-ABI + dispatch-error e2e (items 4-5); items 1-3 complete with 0323. Stage 2. |
| 0317 | /spec | open | Pillar B — `main : IO _` enforcement + suite-wide sweep + output-coverage reshape (1 red). Largest workstream. |
| 0318 | /spec | open | **Compiler-side enforcement already landed S79** (`require_io_return`, `src/platform.rs:560`, passing tests — Phase-2 arch). Residual = `/spec` text (`08-modules.md:783` conditional→unconditional) + the `shapes` `area`→`(IO Int)` fixture (Pillar A delivers). |
| 0316 | /spec | deferred → S81 | Import-ambiguity model + `resolve_with_fallback`. Out of scope (see above). |

*(Wave-gate scan of `design/arch/fixmes/` for `target: /skill-in-wave` + `status: open` runs before each Phase-5 wave advance.)*

## Architecture review (Phase 2)

**Verdict: SIGN-OFF** — scope is technically coherent, no cross-crate interface is needed, both pillars are terminal-shaped and cleanly separable. One scope correction (the 0317 enforcement seam is `src/exe.rs`/int, NOT typecheck) and two "already-landed" reconciliations below. `/arch` made **no** `cranelisp-types` change — no baseline regen.

### Decisive public-API questions (answered against source, not FIXME prose)

**Pillar A (0323) — NO `cranelisp-types` / public-API change. Pure `src/` (int) load-path wiring on top of S79 work.** Validated:
- FQ type resolution for `shapes/Rectangle` already works through existing APIs — `parse_and_check_platform_type_sig` (`src/platform.rs:507`) → `fqize_type_expr` (re-partitions the parser's under-qualified `{module:None, name:"shapes/Rectangle"}` into `{module:Some("shapes"), name:"Rectangle"}`) → `cranelisp_typecheck::check_type_expr` → `cranelisp_types::resolve`. The S79 `resolve_named` product-ctor-as-type fix is landed and confirmed at `crates/cranelisp-typecheck/src/resolve.rs:80–114` + test `test_resolve_product_ctor_as_type` (resolve.rs:450). Once `Rectangle` is *reachable in module `shapes`*, it resolves.
- The remaining blocker is purely **module-load ordering**: `shapes.cl` must be in the symbol tables before the platform sig naming `shapes/Rectangle` is checked. `platform-interface.md §7.2` (line 1012) already specifies this as the design target ("resolve + compile associated `.cl` type module(s) … BEFORE sigs"). As-built reaches the same end-state via the orchestrator's `ResolutionGap` auto-load retry (`drive_module_dep`, the FIXME-0268 FQ-autoload path) rather than an inline pre-resolve step — when the sig check hits an unloaded `shapes`, the gap drives `register_dep`+`register_module`+retry-from-top. So the fixture just needs `shapes.cl` resolvable on the ordinary module search path (`resolve_module_file`, `src/pipeline.rs:27` — project tree + `CRANELISP_LIB`, NOT `CRANELISP_PLATFORM_PATH`) and the program/sig to name `shapes/Rectangle`. **No new type, no new public fn.** All resolution machinery exists.
- 0289 items 4-5 (perturbed-ABI + dispatch-error e2e) consume already-landed `PlatformError::{AbiVersionMismatch, DispatchError}` variants (unit-proven in `src/platform.rs`); the e2e just needs the new ADT-typed `shapes` test-DLL fixture. No interface work.

**Pillar B (0317) — NO `cranelisp-types` / public-API change. The enforcement seam is SETTLED, but it is `src/exe.rs` (int), NOT typecheck — FIXME 0317 prose is imprecise.** Validated against source:
- The `main : IO _` gate already exists: `validate_main` (`src/exe.rs:341`) → `classify_main_return_type` (`src/exe.rs:359`). It is called in **both** batch modes — `--link` via `link_by_name` (`session_v4.rs:3911`) and `--run` via `lookup_main_return_type`→`trampoline` (`session_v4.rs:3695`). REPL never calls it (correctly exempt).
- **Enforcement is a one-arm deletion**: `classify_main_return_type` currently has `Type::Int => Ok(MainReturnKind::Int)` (exe.rs:362) — *this* is the lenient acceptance 0317 targets. Removing/tightening that arm (keep the `IO` arm, reject bare `Int` with the `(Fn [] (IO _))` diagnostic) IS the enforcement. `MainReturnKind` keeps both variants only if a transition wants `Int` to warn; for a hard reject the `Int` variant could even retire, but that is an int-internal enum (`src/exe.rs`), not a `cranelisp-types` boundary type — **no baseline impact either way**.
- **Scope correction for `/sprint`/Phase 4**: 0317 item (2) says "`/dev` (typecheck) rejects a batch `main`". That is the wrong owner. Typecheck has no clean batch-vs-REPL signal (it checks both identically; the REPL-exemption lives at the int execution boundary). The enforcement belongs to **`/dev` (int — `src/exe.rs`)**, paired with `/qa`'s sweep. Recommend re-labelling the workstream owner. (No interface decision needed — this is purely "which crate hosts the gate", and source already answers it: int.)

### Already-landed reconciliations (FIXME/source drift caught — flag to `/sprint`)

- **0318 item #2 (the enforcement check) is ALREADY DONE.** `require_io_return` (`src/platform.rs:560`, with the full FIXME-0318 rationale in its rustdoc) is already called in `register_platform_in_tc` (`platform.rs:378`) after `parse_and_check_platform_type_sig`, with passing unit tests (`platform.rs:694/711/729` — rejects `(Fn [Int] Int)`, accepts `stdio` IO sig). So 0318 reduces to: (1) `/spec` text edit at `08-modules.md:783` (conditional→unconditional) + annotation, and (3) the `shapes` fixture `area`→`(IO Int)` (which 0323/0289 deliver anyway). The compiler-side work is closed. 0318 is correctly folded into Pillar B `/spec` + Pillar A fixture — confirm the `/dev` cascade item is marked done-on-arrival.

### Interim-architecture risk (Principle 8)

Both pillars are **terminal-shaped** — no stepping-stones requiring later rework.
- Pillar A rides the already-settled `platform-interface.md` target (user-ratified 2026-06-07, cascaded S76); the load path is the §7.2 sequence; nothing here is provisional.
- Pillar B's enforcement is a permanent tightening of an existing gate, not scaffolding.
- **The output-coverage reshape (0317 item 4) is a `/qa` test-harness detail, NOT an architectural commitment.** `run_through_all_modes_output` is a test-side harness (lives in `tests/`, owned by `/qa`) that asserts byte-equivalent stdout across REPL/`--run`/`--link`. It does NOT change any crate's public surface, any `cranelisp-types` type, or any sequence diagram. The *invariant* it encodes ("observable output is identical across run modes") is real and already lives in `tests/plan/PLAN.md` + Principle 11; 0317 item 4 proposes also stating it normatively in `spec/10-io.md` (a `/spec` decision, precedent `spec/04-expressions.md:850`). `/arch` recommendation: that spec sentence is worth adding (it makes Principle 11's mode-equivalence axiom user-visible and traceable), but it is `/spec`-owned and gates nothing architecturally. The harness shape is `/qa`'s to own outright — no `/arch` artefact moves.

### Pillar separability (parallel D/D/R, serialized green-ups — as user-approved)

Cleanly separable. Pillar A touches `platforms/shapes/` (`/platform`) + `tests/spec_platforms_adt.rs` + `tests/platform_errors.rs` (`/qa`) + possibly `src/platform.rs`/`src/worker.rs` load wiring (`/dev` int, only if the auto-load needs a nudge). Pillar B touches `src/exe.rs` (`/dev` int) + `spec/{02-grammar,08-modules,10-io,12-runtime}.md` (`/spec`) + ~11 `tests/` files + `tests/plan/` (`/qa`) + `examples/` (`/examples`) + `exemplar/` (`/port`).

**Shared collision seams to manage (name them in Phase 4 wave org):**
1. **`/qa` / `tests/`** — both pillars converge on `/qa` for test authorship and the green-up. This is the intended single integration point; serialize the green-ups (already the approved sequencing).
2. **`src/` (int) — `/dev` narrow** — Pillar A *may* touch `src/platform.rs`/`src/worker.rs` (load ordering), Pillar B touches `src/exe.rs`. **Disjoint files**, same crate/skill (`/dev` int). If both fire `/dev` int in the same wave they share the working tree — sequence the two int fires or batch them into one int D/D/R, but they don't logically collide (different functions, different files). NOT a typecheck collision — Pillar B does **not** touch typecheck (correcting the 0317 mislabel removes the only apparent typecheck overlap).
3. **`tests/plan/`** — Pillar B reshapes `PLAN.md §"Mode canonicalisation"`; no Pillar A overlap.

No file is written by both pillars except via the shared `/qa` integration point, which the serialized-green-up discipline already covers.

### Crate-touch map (input for Phase 3/4)

**Pillar A:**
| File / surface | Skill | Note |
|---|---|---|
| `platforms/shapes/src/{lib.rs,shapes.cl,shapes.platform-schema}` | `/platform` | `area`→`(IO Int)` (0318 #3); `shapes.cl` as loadable module; schema regen (real `w`/`h`) + dylib rebuild |
| `tests/spec_platforms_adt.rs` | `/qa` | 6 round-trip/hash-gate/cache tests + the `(import [shapes [Rectangle]])` fixture |
| `tests/platform_errors.rs` (or sibling) | `/qa` | 0289 items 4-5 e2e (perturbed-ABI, dispatch-error) |
| `src/platform.rs`, `src/worker.rs` | `/dev` (int) | ONLY if the type-module auto-load needs wiring beyond the existing gap-retry (triage step; may be no-op) |
| _no_ `cranelisp-types` / _no_ typecheck source change | — | confirmed |

**Pillar B:**
| File / surface | Skill | Note |
|---|---|---|
| `src/exe.rs` (`classify_main_return_type`) | `/dev` (int) | remove the `Type::Int` accept arm; emit `(Fn [] (IO _))` reject — **the enforcement seam** |
| `spec/02-grammar.md §2.1`, `spec/10-io.md §10.6/§10.6.1`, `spec/12-runtime.md §12.6`, `spec/08-modules.md §8.11` | `/spec` | 0317 MUST-confirm + annotation upgrade; 0318 conditional→unconditional + rationale; optional `spec/10-io.md` mode-output-equivalence sentence |
| ~11 `tests/*.rs` (~125 mains) + `tests/plan/PLAN.md` | `/qa` | sweep bare-`Int` mains → `IO`; fix 3 violation-certifying test-design defects; `run_through_all_modes_output` harness; flip the RED guard |
| ~22 `examples/*.cl` | `/examples` | rewrap mains; rework exit-code-checksum convention |
| `exemplar/` inline repros | `/port` | rewrap mains |
| _no_ `cranelisp-types` / _no_ typecheck source change | — | confirmed |

### Scope adjustments for `/sprint`

1. **Re-own the 0317 enforcement workstream from `/dev` (typecheck) to `/dev` (int — `src/exe.rs`).** Source-confirmed; not a typecheck change.
2. **Mark 0318's compiler-side enforcement (item #2) as already-landed** (`require_io_return`, S79). 0318 residual = `/spec` text + the `shapes` `area` IO fixture (delivered by Pillar A).
3. No scope is added or cut otherwise; the 7-red target stands.

## Skill plans (Phase 3)

> **Two decision-grade findings surfaced (see Notes 2026-06-13 Phase-3):** (1) the Pillar-B sweep is **~200 mains across 21 files**, not the ~125/11 estimated; (2) Pillar A needs a **real `/dev` int change** (§7.2 associated-`.cl`-module pre-resolve) — the Phase-2 "gap-retry auto-loads it, may be no-op" assumption is source-corrected (unresolved platform sig type-ref → `ModuleError`, never a `ResolutionGap`).

### /spec — Pillar B semantics (DESIGN-COMPLETE; spec edits landed this phase)

- **Ruling (0317 fork)**: `main : (Fn [] (IO _))` MUST **stands as enforceable** — spec NOT relaxed. Rationale: a non-IO main that drives the program's effects is a category error against the §10.1.2 purity invariant (same principle 0318 enforces at the FFI boundary); exit code is already the *inner* Int of `IO Int` (§10.6.1/§12.6) — a bare-Int main would need special-casing. REPL exempt (§10.6.2) so ergonomic cost is nil. No spec-wording change needed for the ruling — the defect was enforcement + traceability, not wording.
- **Spec edits made (test-independent, applied)**: `08-modules.md §8.9.3` conditional→**unconditional** "Every platform function MUST return `IO _`" + soundness rationale (canonical 0318 site); `10-io.md §10.10.2` + `12-runtime.md §12.8` consistency tightening + cross-ref §8.9.3; **NEW `10-io.md §10.6.3` Mode-Output Equivalence** (byte-equivalent observable output across `--run`/`--link`/REPL — gives /qa's output-reshape a normative anchor; precedent §4.12.9). `03-types.md:71` left as-is (general fn rule, correct).
- **Annotation upgrades (close-time, NOT applied — earned by the passing test)**: `02-grammar.md:23` (§Batch Mode), `10-io.md:242` (§10.6) + `:252` (§10.6.1), `12-runtime.md:171` (§12.6) → `[Tested+Neg tests/spec_10_io.rs::batch_main_pure_int_return_is_rejected]`; `08-modules.md §8.9.3` → platform-IO enforcement test (0318 item 5).
- **Acceptance**: all three platform-IO sites read unconditional (✅ done, grep-verified); §10.6.3 present (✅); the 4 annotation flips land at close after the RED guard is green.

### /qa — test plan, both pillars (PLAN-COMPLETE; mass authoring is Phase-5 Stage-1)

- **Pillar A — 6 RED inventory** (`tests/spec_platforms_adt.rs`, all same blocker, confirmed matches 0323): `platform_adt_roundtrip_run/_link/_cache_restore` (exit 12) + `_hash_gate_run_refuses/_repl_warns_and_loads/_link_refuses`. **Reconciliation**: `area` already returns `IO Int` (0318 DLL-side landed) → `(defn main [] (area (Rectangle 3 4)))` is already spec-conformant; **Pillar A mains are EXCLUDED from the Pillar B sweep**.
- **Pillar A fixture plan**: program drops `shapes.cl` into the per-test tmpdir via `.file("shapes.cl", "(deftype Rectangle [:Int w :Int h])")` (self-contained, no `platforms/` coupling) + `(import [shapes [Rectangle]])`. Hash-gate tests (3,4,5) additionally **blocked on /platform schema regen** (real baked hash vs the `0000…` sentinel) — sequence regen first. Discovery-budget one /dev int triage (now confirmed real — see /platform).
- **0289 i4-5**: new tests in `tests/platform_errors.rs` — `platform_abi_version_mismatch_e2e` (`AbiVersionMismatch{expected,found}`, both values in stderr) + `platform_dispatch_error_carries_fn_name` (`DispatchError{fn_name}`). **Hard-dependent on /platform test-DLLs** — the natural cut if /platform can't land both (ride RED un-ignored, ledgered).
- **Pillar B sweep — ENUMERATED**: **221 `defn main` / ~220 batch sites across 21–23 files; ~200 bare-Int mains need reshaping** (S79's ~125 was a 60% undercount). Heaviest: `cache.rs` (51 sites→`(Pure 0)`), `spec_08_modules.rs` (35), `regression.rs` (18), `link.rs` (15), `spec_12_runtime.rs` (12). Transform is **mechanical**: `(defn main [] EXPR:Int)` → `(defn main [] (Pure EXPR))`, **exit codes preserved, assertions unchanged**. Default `(Pure …)` (seeded, no prelude coupling) over lowercase `(pure …)`.
- **3 test-design defects** (certify the violation, must fix): `spec_10_io.rs::run_mode_main_returns_int_exit_code` (`main []7`→reshape+recomment), `spec_12_runtime.rs` exit-witnesses (incl. `main []true` — needs a `IO Bool` exit-semantics confirm from /dev int, or convert to neg test), `link.rs::link_error_when_main_returns_wrong_type` (`Int||IO` disjunction → require `IO`, drop `Int`).
- **Mains that STAY non-IO** (rejection subjects): the RED guard (`main []0`), `link.rs` String main (`"hello"`), and the `Bool`-main witness (→ new neg test `batch_main_bool_return_is_rejected`).
- **Output-coverage reshape (FLOOR)**: new `run_through_all_modes_output` stdout harness (byte-equal program stdout across the 6 mode×cache permutations, REPL echo stripped); convert **~8 feature-class representatives + ~2-3 existing IO tests = ~10-12 all-modes-output tests** (up from 3 single-mode). `PLAN.md §Mode canonicalisation` reshaped: output-equivalence primary, exit-code-equivalence the pure-smoke minority. Annotate the harness to `spec/10-io.md §10.6.3`. **Full-corpus conversion = S81.**
- **RED guard flip**: `batch_main_pure_int_return_is_rejected` flips when /dev int deletes the `Type::Int` accept arm (`src/exe.rs:362`); /dev updates the message to name `(Fn [] (IO _))` + drop "or Int".
- **Sizing verdict**: **NOT comfortably one sprint at floor; recommends cut/sequence** (see Notes + the user sizing fork). Recommended order: land the int one-arm deletion FIRST (the suite then names every unconverted main), Pillar A core in parallel, sweep in 2-3 file-cluster waves (one serialized green-up each), output-floor last. If cut: drop 0289 i4-5 + trim output-reshape to the ~8-class floor; **do NOT cut the sweep** (all-or-nothing once enforcement lands).

### /platform — Pillar A `shapes` fixture (PLAN-COMPLETE; fixture authoring is Phase-5)

- **S79 fixture already correct safe-now**: `area : (Fn [shapes/Rectangle] (primitives/IO primitives/Int))` returning `CLIO<CLInt>` (✅ 0318 holds, no edit); `(deftype Rectangle [:Int w :Int h])`; ABI v3.
- **The one surfacing layer (CORRECTS Phase-2 arch)**: `register_platform_in_tc`→`parse_and_check_platform_type_sig` maps an unresolved FQ sig type-ref to `CranelispError::ModuleError`, **NOT** a `ResolutionGap` — so the FIXME-0268 FQ-autoload retry never fires for platform sig types. `shapes.cl`-on-search-path is **necessary but not sufficient**; needs a **§7.2 pre-resolve** in int (resolve+register the platform's associated `.cl` type-module(s) BEFORE the sig-check loop, via `drive_module_dep`). **/platform is filing a FIXME → /dev int** for this. Disjoint from Pillar B's `src/exe.rs` (collision-seam #2: same crate/skill, different files).
- **/qa contract (handed off)**: module `shapes` = `shapes.cl` at project_root; `Rectangle` single-ctor product tag 0; fields `w`(0),`h`(1) `:Int`; entry program de-defines `Rectangle`, adds `(import [shapes [Rectangle]])`; witness `(area (Rectangle 3 4))`⇒IO 12.
- **Schema regen (Phase-5 only)**: `/platform-schema shapes` → real `layout-hash` + `(schema (shapes/Rectangle (Rectangle 0 ((w primitives/Int)(h primitives/Int)))))` → rebuild dylib. Placeholder `w`/`h` names already correct (clean round-trip works pre-regen); only the **drift hash-gate** needs the real baked hash. Generator output is authoritative.
- **0289 i4-5 DLLs**: hand-rolled `platforms/shapes-badabi/` (stale `abi_version` literal — `declare_platform!` has no override arm; distinct dylib name dodges the manifest-symbol collision) for item 4; a dispatch-failure sibling DLL for item 5 (injection point pending a /dev int read). Both /platform-owned; tests/-side e2e is /qa's.

## Waves (Phase 4)

**Cut-line: EVERYTHING, no cuts** (user 2026-06-13) — int enforcement + full ~200-main sweep + 6 Pillar-A reds + 0289 i4-5 + output-floor; fully green with full platform drift coverage. Two parallel tracks (A platform / B conformance), **green-ups serialized** (one `cargo nextest` at a time — detached jobs, patient on the dyld cold-load). The two int changes (`exe.rs` enforcement + `platform.rs` §7.2 pre-resolve) **batch into one `/dev` int D/D/R** (same skill/crate, disjoint files — resolves collision-seam #2).

### Wave 0 — QA-first (Phase 5 Stage 1, one `/qa` fire, sprint-wide failing tests)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /qa | tests/ | Author the failing tests for the whole sprint: Pillar-A 6 round-trip reshaped to the new fixture (`.file("shapes.cl",…)` + `(import [shapes [Rectangle]])`); 0289 i4-5 e2e (failing, pending DLLs); `run_through_all_modes_output` harness + ~10-12 output-floor tests; new `batch_main_bool_return_is_rejected` neg test. (RED guard `batch_main_pure_int_return_is_rejected` already exists.) **NOT** the ~200-main sweep — that is coupled to enforcement (Wave 2). | pending |

### Wave 1 — Enabling changes (parallel; gates both tracks)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /design int → /dev int → /review int | src/ | **Batched int D/D/R, both pillars**: (B) `classify_main_return_type` (`src/exe.rs:362`) — delete the `Type::Int` accept arm, reject bare-Int with the `(Fn [] (IO _))` diagnostic (drop "or Int"); confirm `IO Bool` exit-semantics for the `spec_12_runtime` witness. (A) `register_platform_in_tc` (`src/platform.rs`) — §7.2 pre-resolve: resolve+register the platform's associated `.cl` type-module(s) via `drive_module_dep` BEFORE the sig-check loop (the `ModuleError`-not-`ResolutionGap` gap). + unit tests. | pending |
| /platform | platforms/ | Author `platforms/shapes-badabi/` (hand-rolled stale-`abi_version` DLL, distinct dylib name) + the dispatch-error fixture DLL. `cargo check -p` narrow, clean warnings. | pending |

*Gate: int compiles + enforcement live; `/review` int Blocker/Important resolved. After this lands, the suite NAMES every unconverted bare-Int main (per /qa) — making Wave 2's sweep mechanical.*

### Wave 2 — Sweep + fixture wiring + drift e2e (parallel tracks; serialized green-ups)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /qa (Pillar B) | tests/ | The ~200-main sweep in 2-3 file-cluster sub-waves (`cache+regression+modules` / `spec_*` / residual), `(Pure EXPR)` wrap (exit codes preserved); fix the 3 violation-certifying test-design defects; flip the RED guard. One serialized green-up per sub-wave. | pending |
| /examples | examples/ | Rewrap ~22-27 example mains → `IO`; rework the exit-code-checksum convention. (Parallel — disjoint files.) | pending |
| /port | exemplar/ | Rewrap exemplar inline-repro mains → `IO`. (Parallel — disjoint files.) | pending |
| /qa (Pillar A) | tests/ | Wire the tests/-side `shapes.cl` fixture for the 6 reds (depends Wave-1 §7.2); wire 0289 i4-5 e2e against the Wave-1 DLLs. | pending |
| /platform | platforms/ | Phase-5 schema regen (`/platform-schema shapes` → real layout-hash) + dylib rebuild — unblocks the 3 hash-gate reds. (After /backend confirms the generator emits real `w`/`h` e2e.) | pending |
| /qa (output-floor) | tests/, tests/plan/ | The ~10-12 all-modes-output tests green; `PLAN.md §Mode canonicalisation` reshaped (output-equiv primary). | pending |

### Wave 3 — Convergence + close-prep

| Skill | Crate | Task | Status |
|---|---|---|---|
| /qa | tests/ | Final serialized full `cargo nextest` green-up → target **1200+/0 fail** (all 7 reds cleared + new coverage). | pending |
| /review | (touched crates) | Final change-set review across int/platform; Blocker/Important resolved-or-deferred. | pending |
| /spec | spec/ | Apply the 4 close-time annotation flips (→ `[Tested+Neg …]`) once the RED guard is green. | pending |

**Wave-gate reminder**: before each advance, scan `design/arch/fixmes/` for `target: /skill-in-wave` + `status: open`. The §7.2 pre-resolve is carried in-plan (Wave 1 /dev int), not as a separate FIXME.

## Notes

- 2026-06-13 — Phase 1 scope drafted. Baseline from S79 close: 1196 passed / 7 failed (6 → 0323, 1 → 0317) / 8 skipped. User chose **"both pillars (platform + conformance)"** over the focused/rider/conformance-first shapes — full green by sprint end, 0323 + 0289 i4-5 + 0317. `/sprint` flagged the size risk (0317's sweep is plausibly a full sprint alone; dyld green-up tax compounds); user accepted. 0316 deferred to S81.
- 2026-06-13 — **Scope APPROVED** (user). Sequencing decision: **pillars run parallel, but green-ups serialize** — concurrent green-ups thrash the page cache under the dyld cold-load tax, so D/D/R work proceeds in parallel across both pillars while the integrating `cargo nextest` green-ups are run one-at-a-time (detached jobs). 0318's `08-modules.md:783` unconditional edit folds into Pillar B's `/spec` work (user confirmed). Advanced to Phase 2 — `/arch` review against this scope.
- 2026-06-13 — **Cut-line decided: EVERYTHING, no cuts** (user, informed by the /qa "not comfortably one sprint at floor" verdict + the ~200-main / Pillar-A-needs-real-int-change findings). Full scope retained; multi-wave, serialized green-ups. **Phase 4 waves locked** (Wave 0 QA-first → Wave 1 enabling int+DLLs → Wave 2 sweep+fixture+drift → Wave 3 convergence). Status → PHASE 5 READY, awaiting user go to begin execution.
- 2026-06-13 — **Phase 3 design collected** (`/spec` + `/qa` + `/platform`, parallel). Spec side design-complete (edits landed: 0318 unconditional ×3 sites + new §10.6.3 mode-output-equivalence; ruling = enforce main:IO). **Two findings materially enlarge the Phase-1 estimate**: (1) `/qa` enumerated the sweep at **~200 bare-Int mains / ~220 batch sites across 21 files** (not ~125/11 — a 60% undercount), and gave an explicit **"not comfortably one sprint at floor"** sizing verdict; (2) `/platform` source-corrected the Phase-2 "gap-retry auto-loads the platform type-module" claim — it does NOT (unresolved sig type-ref → `ModuleError`, not `ResolutionGap`), so Pillar A carries a **real `/dev` int §7.2 pre-resolve change** (FIXME incoming from /platform), not a possible no-op. Both pillars still terminal-shaped; the transform is mechanical (`(Pure EXPR)`, exit-codes preserved). **Sizing fork surfaced to user before Phase 4.**
- 2026-06-13 — **`/arch` Phase-2: SIGN-OFF.** No `cranelisp-types` / public-API change needed (no baseline regen); both pillars terminal-shaped (Principle 8 clean) + cleanly separable. **Two source-validated corrections** (full detail in the Arch-review section): (1) the 0317 `main:IO` enforcement seam is **`src/exe.rs::classify_main_return_type`** (int — a one-arm deletion of the `Type::Int` accept arm), **NOT typecheck** — re-owned to `/dev` int; (2) **0318's compiler-side `require_io_return` already landed S79** — 0318 residual is `/spec` text + the `shapes` `area`→`IO` fixture. Output-coverage reshape (0317 item 4) confirmed a `/qa` test-harness detail, no arch artefact moves. Crate-touch maps for both pillars recorded. Advanced to Phase 3 — design invocations: `/spec` (Pillar B semantics), `/qa` (test plan both pillars — the sweep needs a plan before mass authoring), `/platform` (Pillar A `shapes` fixture). `/arch` interface work complete (none needed); `/dev` int design refinement folds into Phase-5 Stage-2 (one-arm deletion + the load-ordering triage are implementation-discovered).

## Outcome (Phase 7)

### Delivered
- {what shipped}

### Deferred (with rationale)
- {item — why deferred, target sprint, escalation count}

### Findings (record in FIXMEs if not already)
- {unexpected observations, methodology lessons, skill feedback}
