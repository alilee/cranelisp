# Sprint 79: Stage 2 — Platform round-trip + FQTypeName: cement landed changes with tests

**Status**: PHASE 7 CLOSE (pending user approval)

**Goal**: Cement two already-landed-but-unexercised changes by their tests — drive the platform-interface ADT round-trip + dual hash-gate to green e2e behind a real ADT-typed test-DLL (fixing whatever gaps the first real exercise surfaces), and retire the FQTypeName arc by auditing its resolved-stage test coverage, closing gaps, and getting to green.

## Scope

Sprint 78 closed the de-special-casing arc fully green (1175/1175, 8 skipped). This is **Stage 2** of the post-arc consolidation arc (S77 = Stage 1 settle+green; S78 = int restructure). **The /arch Phase-2 review (below) overturned the original "land a feature + migrate" framing**: both the platform-interface cross-crate mechanism (S76 W4a/W4b) and the FQTypeName resolved-stage compliance are **already in source** — what's missing is the *tests that exercise and cement them*. S79 is therefore a **test-cementing / coverage-closing sprint**, kept deliberately **lean + discovery** (user 2026-06-12). Two independent, parallel pillars on disjoint surfaces.

### Pillar A — Platform ADT round-trip to green e2e (lean + discovery)

The full cross-crate mechanism landed S76 W4a/W4b (load-path, GOT-indirect dispatch, `LayoutHashGate`, `--link` hash bake, `/platform-schema` command, `PlatformError::LayoutHashMismatch`) — see Architecture review §(a)–(c). But it has **never actually executed end-to-end**: no ADT-typed platform DLL exists in the tree (`platforms/` holds only `stdio` + `test-capture`, neither ADT-typed), so the GOT-indirect dispatch arm (0287) and host-side ADT marshaling (0229) have never run against a real ADT-typed platform. **S79 is the first real exercise of that path** — expect the fixture to surface gaps that need fixing (this is the discovery half; the S25 "scaffolding without the final codegen step" lesson applies — the path isn't *proven* until it runs).

- **`/platform`** — author the ADT-typed `shapes` test-DLL fixture: sigs reference a `Rectangle` ADT defined in an ordinary `.cl` module, so the backend emits a non-empty schema + `__cranelisp_layout_hash_shapes`. (Owns `platforms/shapes/`.)
- **`/qa`** — the e2e walks (FIXME 0289 items 1–3): clean FQ-ADT round-trip (`Rectangle {w=3,h=4} → 12` crosses the DLL boundary in `--run` + `--link`); dual hash-gate drift (REPL warn / `--run` refuse / `--link` refuse, both hashes + rebuild guidance); cache-restore round-trip. Authored failing-first, then green.
- **`/dev` (discovery, as surfaced)** — whatever the first real round-trip breaks: the dormant backend GOT-indirect arm (0287), host-side ADT marshaling residual (0229), or any int load-path gap. Scoped reactively — no implementation is *predicted* owed for items 1–3, but the sprint owns fixing what the fixture exposes.

**Acceptance**: `tests/spec_platforms_adt.rs` (or sibling) green — clean FQ-ADT round-trip + dual hash-gate + cache-restore (0289 items 1–3). Re-engages **Phase 6** (`/platform` validates a real FFI capability — waived since ~S68). **Deferred → S80**: perturbed-ABI + dispatch-error e2e (0289 items 4–5; both already unit-proven in `src/platform.rs`).

### Pillar B — FQTypeName arc retirement via test coverage (parallel, small)

The /arch review (§(d)) found the four originally-named sites **do not migrate** — three are Decision-0047 exception-2 keeps (scope-relative chain resolvers), one (`Type::adt`) already produces the FQ form. The resolved-stage `FQTypeName` compliance is **already correct in source**. Per the user (2026-06-12): *"this feature arc can be retired when the unit and e2e tests cement in the change — start by auditing test coverage, closing the gaps and getting to green."*

So Pillar B is **not a migration** — it is the arc's **test-cementing retirement**:

- **`/design` (cranelisp-types)** — a fresh resolved-stage **boundary audit**: enumerate every public API carrying a type/trait identifier across a crate boundary; classify each as FQ-carrying (compliant), exception-1 (reverse-lookup/display), or exception-2 (context-supplied/receiver-pinned); annotate the exception keeps with `// FQTypeName exception N` comments. Confirm zero genuine bare-`TypeName`-at-a-resolved-boundary leaks remain (or surface any that do as the real residual).
- **`/qa`** — author the **coverage that cements compliance**: a boundary test asserting `Type::ADT` / `ResolvedCall` / `ModuleEntry` resolved-stage identifiers carry FQ form end-to-end; close whatever coverage gap the audit names. Get to green.
- **Retirement**: once the audit confirms compliance and the tests cement it, the FQTypeName arc (Decision 0047, the standing project priority) is **declared retired** at close — recorded in the Outcome + the `project_fqtypename_priority` memory updated.

**Acceptance**: audit complete (every resolved-stage boundary classified, exception keeps annotated); coverage test green; **zero `public-api.txt` change** expected (no signatures migrate); arc retirement recorded.

### Out of scope (deferred, with target)

- **Perturbed-ABI + dispatch-error e2e (FIXME 0289 items 4–5)** — both drift paths are already wired and unit-proven in `src/platform.rs` (`abi_version_mismatch_detected`); only the e2e companions defer. → S80.
- **Import-ambiguity model + `resolve_with_fallback` unification (FIXME 0316)** — `/spec` + `/arch` design decision (terminal-source dedup; glob-vs-specific precedence) plus the 5×-duplicated prelude-fallback seam collapse. Separable design work; not blocking (no red test). → S80 (or a focused /spec+/arch slot).
- **S80 increment — "Batch `IO`-main conformance + output-coverage reshape"** (the largest deferral; durable record = the RED `batch_main_pure_int_return_is_rejected` test + ledger row + FIXME 0317): (a) `/dev` (typecheck) **enforces `main : (Fn [] (IO _))`** — reject non-`IO` batch main; (b) `/qa` **suite-wide sweep** — ~125 batch bare-`Int` mains across ~11 test files → `IO` (`(pure 0)` smoke / `(print …)` observable), ~22 examples rewrap, exemplar repros, **exit-code-checksum convention rework** (`IO Int` inner-Int semantics); (c) `/qa` **test-design-defect fixes** — `run_mode_main_returns_int_exit_code` + `spec_12_runtime` exit-code tests + `link.rs::link_error_when_main_returns_wrong_type` (`Int||IO` disjunction) all currently certify the violation; (d) full **output-coverage reshape** (`run_through_all_modes_output` harness + majority-produce-output mode-equiv corpus); (e) `/spec` **annotation upgrade** — `02-grammar.md:23` / `10-io.md §10.6/§10.6.1` / `12-runtime.md §12.6` from stale `[R4 S10]` → `[Tested+Neg …]`; (f) the RED test flips green. All land together (the sweep is only sensible once enforcement is live).
- **Stdlib in-language test runner (FIXME 0273)**, **legacy harvest (0116–0149)**, **Stage 3 perf baseline**, **Stage 4 int doc-reorg (0298) + intrinsics trace cascade (0297)** — later Stage-2/3/4 increments.
- Opportunistic small W0 carries (0303/0306/0308/0309, stale `repl_lifecycle.rs` comments) — fold in only if a pillar touches the same surface; otherwise S80.

## FIXME debt

Carried into scope (Pillar A unless noted):

| FIXME | Target | Status | Notes |
|---|---|---|---|
| 0289 | /qa | open | Platform e2e round-trip + hash-gate (acceptance gate) — **the live Pillar-A gate** |
| 0233 | /int | **STALE → close** | superseded by W4b (0288); all owed items landed |
| 0287 | /dev (backend) | backend-landed; arm dormant | GOT-indirect arm activates on `got_slot: Some` when ADT-DLL appears; no new work for items 1–3 |
| 0232 | /backend | open | `.meta.json` platform schema field — re-pointed: `schema_literal` already retired; check if any residual owed |
| 0238 | /dev platform | **STALE → close** | `schema_types:` arm deleted wholesale with the `schema:` declaration arm (0286/W4b); moot |
| 0229 | /int | re-scope or close | host-side ADT marshaling — `alloc_with_tag` KEEP landed; residual (if any) is fixture-surfaced |
| 0104 | /dev | open | PlatformError adoption (types/platform/int) — variant landed; confirm consumer adoption |
| 0293 | /arch | **RESOLVED — deleted** | PlatformError `LayoutHashMismatch` variant + `schema_literal` removal both landed |
| 0106 | /design | open | archive platform-registry-removal |
| 0252 | /design | open | backend-jit platform effect shape stale |
| 0253 | /design | open | backend-jit zero-arg disposition stale |
| 0047 (Decision) | /design+/qa | binding → **retire** | FQTypeName already compliant in source; Pillar B audits coverage + cements with tests, then retires the arc (not a migration) |
| 0316 | /spec | open | DEFERRED → S80 (import-ambiguity + resolve_with_fallback) |

## Architecture review (Phase 2)

**SIGN-OFF with scope corrections (/arch, 2026-06-12).** Both pillars are architecturally
coherent and disjoint; sign-off granted. The platform-interface design is NOT in an
interim state — its full cross-crate mechanism already landed (S76 W4a/W4b); what remains
is fixture + e2e (execution, not design). Pillar B's premise needs two corrections before
Phase 3. Detail:

### (a) Platform-interface FIXME coverage — 0286/0288 are NOT missing; they LANDED

The SPRINT draft's premise that 0286 (platform macro) and 0288 (int load-path) are
"missing equivalents to file" is **stale**. Both FIXMEs existed and were **resolved +
deleted** in commit `2d754f3` (S76 W4b — "platform-interface coordinated cut"). That commit
landed:

- **0286 (platform macro):** `declare_platform!` reworked — `validate_schema` /
  `null_validate_schema` / `jit_name` / `derive_jit_name` / per-fn `export_name` all
  removed; ABI v3; GOT populated by manifest fn-refs. FIXME deleted.
- **0288 (int load-path):** `dlsym __cranelisp_got_platform_<name>`, `GotTable` wrap-not-copy,
  SymbolTable-from-manifest (`got_slot = manifest index`), FQ sigs,
  `inject_primitives_import_for_platform` + `jit_name`/`JITBuilder::symbol` registration
  DELETED, GOT-indirect dispatch, layout-hash gate (`LayoutHashGate` enum + `layout_hash_gate()`
  in `src/worker.rs:2700/2717`; `--link` bake in `src/exe.rs`), `/platform-schema` command
  (`src/session_v4.rs:200/2222/3554`). FIXME deleted.

**No FIXMEs need to be filed.** 0233 (int) and 0238 (platform-macro proc-macro upgrade)
are **stale and should be CLOSED** as part of this sprint, not "carried":
- **0233** — its three owed items (injection deletion, DLL-exported-GOT model, layout-hash
  check) ALL landed in 0288/W4b. It is fully superseded; **re-point: close/delete 0233.**
- **0238** — the `schema_types:` redundancy it targeted was deleted wholesale when the
  `schema:` declaration arm retired (0286). The proc-macro upgrade is moot — there is no
  `schema_types:` ident list any more. **Close/delete 0238.**
- **0229** (host-side ADT marshaling) — `alloc_with_tag` KEEP landed; the `validate_schema`
  half retired. Only residual relevant to this sprint is whatever marshaling the `shapes`
  round-trip exercises (qa/platform fixture work, NOT a separate int change). Re-scope to
  the fixture or close.

What ACTUALLY remains for Pillar A acceptance is **the fixture + e2e only**: the `shapes`
ADT-typed test-DLL does not exist (`platforms/` holds only `stdio` + `test-capture`, neither
ADT-typed), and `tests/spec_platforms_adt.rs` does not exist. This is precisely the
0289-option-2 scope. So Pillar A = **0289 (qa e2e) + the `/platform` fixture it needs**, NOT
the four-crate D/D/R the draft's wave plan implies. The backend (0287) GOT-indirect arm is
landed-and-dormant — it activates automatically when the ADT-typed DLL flips a platform entry
to `got_slot: Some(_)`; no new backend work is owed for items 1–3.

### (b) Layout-hash gate coherence — FULLY SPECIFIED, no underspecification

The dual gate is coherent across all three manifestation sites: BC §3 (backend generator +
GOT-indirect dispatch + startup hash bake), BC §6 (int load path: regenerate-and-compare,
REPL warns / `--run` refuses), BC §5 (platform three exports incl. `__cranelisp_layout_hash_<name>`).
The regenerate-from-live-tables checker is unambiguously placed in `cranelisp-backend`
(`schema::generate_schema` / `compute_layout_hash`, sharing the closure-walk + substitution
with the trace `DisplayDescriptor` baker per §6.0), with int + `--link` as the two thin
callers. q-tag-stability and q-schema-grammar (the only §2.2 residue) were both confirmed
source-positional / S-expr at 0287 landing. **No /dev blocker.**

### (c) PlatformError hash-refusal variant (0293) — RESOLVED, FIXME deleted

`PlatformError::LayoutHashMismatch { dll, platform, expected, found, location }` is landed
in `crates/cranelisp-types/src/error.rs:273` (wired into `location()` / `message_static()` /
`Display` with both-hashes + `run /platform-schema <name> and rebuild` guidance, and
`CranelispError::Platform` delegation). The sibling `schema_literal` removal — the only
residue that kept 0293 `partially-resolved` — has ALSO landed: `schema_literal` is gone from
`cranelisp-types` entirely (the only surviving mention is a cache version-history changelog
comment at `crates/cranelisp-backend/src/cache/mod.rs:122`, "v3 REMOVED"). 0293 is fully
resolved; **/arch deleted it this review.** No further variant work owed.

### (d) FQTypeName migration (Pillar B) — DRAFT PREMISE CORRECTED on two counts

Two corrections before /dev touches these:

1. **The three `*_chain` functions are NOT export-only.** The draft claims "zero in-workspace
   callers (export-only), so ripple is minimal." False — there are **5+ live callers** in
   `src/session_v4.rs` (`lookup_type_def_chain` at 4161/4283; `get_impls_for_type_chain` at
   4292/4345; `get_implementing_types_chain` at 4330), all in the REPL display/introspection
   path. Ripple is small but real; /dev must update these call sites in the same change-set.

2. **The `*_chain` functions are SCOPE-RELATIVE resolvers, NOT FQTypeName consumers — they
   do NOT migrate.** Their signature is `(modules, scope: &ModuleFullPath, name: &TypeName)`:
   `scope` is the *access root*, `name` is an **unqualified** name resolved *through* that
   scope by chain-following imports/reexports (Decision 45 Pattern B). The bare `TypeName`
   here is a **syntactic-stage, pre-resolution input** — the function's whole job is to
   perform the `(scope, name) → resolved entry` lift. Forcing `&FQTypeName` would mean the
   caller has already resolved the type, defeating the chain-follow. This is squarely
   **Decision 0047 exception 2 (receiver-pinned / context-supplied)**: the `(modules, scope)`
   pair supplies the module context that disambiguates the bare name. **Ruling: the three
   `*_chain` fns KEEP `&TypeName` / `&TraitName`**, with an exception-2 code comment per
   Decision 0047's Wave-5 acceptance rule. The S67 W0 enumeration already classified int at
   "0 changes (all keeps justified by exceptions)" — these are those keeps. **They are NOT
   Pillar-B migration sites.**

3. **`Type::adt` shape — KEEP `(ModuleFullPath, TypeName)` parameters; do NOT take
   `FQTypeName`.** `Type::adt(module: ModuleFullPath, name: TypeName, args)` is a smart
   constructor whose first act is `FQTypeName::new(module, name)` (`types.rs:49`) — it already
   produces the FQ form internally. The `Type::ADT` variant it builds **already carries
   `FQTypeName`** (resolved-stage identity is correct). The parameter pair is a constructor
   ergonomic, not a boundary identity leak. Its 8 callers (`cranelisp-primitives/src/{operator,lib}.rs`)
   pass `ModuleFullPath::from("primitives")` + a literal `TypeName` — these are
   **construction-site conveniences at known-module seed points**, not resolved-stage
   *consumption* boundaries that Decision 0047 governs. Changing the signature to
   `adt(fq: FQTypeName, args)` would force every caller to spell `FQTypeName::new(...)` at the
   call site — more ceremony, zero identity gain (the result type is identical). **Ruling:
   `Type::adt` KEEPS its `(ModuleFullPath, TypeName)` signature.** It is already
   Decision-0047-compliant: the *boundary type* (`Type::ADT`) carries `FQTypeName`; the
   *constructor params* are an interior convenience.

**Net Pillar B finding:** of the four named sites, **none requires migration.** Three are
exception-2 keeps (scope-relative chain resolvers); one (`Type::adt`) already produces the
FQ form and its params are a constructor convenience, not a boundary. **Pillar B as drafted
has no migration work** — its premise (4 un-migrated resolved-stage boundary APIs) does not
survive inspection. The genuine open question, if any remains, is whether the `Type::ADT`
variant or any *other* resolved-stage public API still takes bare `TypeName`; that needs a
fresh /design (cranelisp-types) audit (the Explore-agent scoping that produced these four was
mis-targeted — it caught syntactic-stage inputs and a compliant constructor, not boundary
violations). **Recommend: either (i) drop Pillar B from S79 and re-scope FQTypeName closure
via a /design audit FIXME, or (ii) narrow Pillar B to "annotate the three `*_chain` keeps
with exception-2 comments + add the boundary test confirming compliance" (a <½-day
documentation+test slice, no signature changes).**

**Expected `public-api.txt` baseline delta:** with rulings (d), **ZERO baseline change** for
`cranelisp-types` — no signature migrates. If Pillar B proceeds as option (ii), the only diff
is the exception comments (non-public-API) + a `/qa` boundary test (in `tests/`, not the
crate surface). The draft's anticipated `public-api.txt` churn does not materialize.

### (e) Interim-architecture risk + disjointness — CONFIRMED disjoint, no S78 regression

- **Disjointness holds.** Pillar A touches platform/backend(dormant)/int/qa surfaces +
  `platforms/` fixtures + `tests/`. Pillar B (if it proceeds) touches `cranelisp-types`
  resolved-stage APIs + their `src/session_v4.rs` callers + a `tests/` boundary test. The one
  surface overlap is `src/session_v4.rs` (Pillar A adds nothing there beyond what W4b already
  landed; Pillar B's option-(ii) only adds exception comments to existing call sites) — no
  hidden coupling, parallelizable.
- **No Principle 8 (no-interim) violation.** Pillar A is not building scaffolding — the
  full mechanism is landed; the sprint adds the missing *fixture* that exercises it. The
  dormant GOT-indirect arm (0287) is a single no-fork discriminator (`got_slot: Some` vs
  `None`), not a parallel interim path — it activates structurally when the ADT-typed DLL
  appears. That is target-state, not interim.
- **No Principle 19 / S78 prelude-as-outer-scope regression.** Platforms register as ordinary
  synthetic `.cl`-style modules (BC §5 / §6; their associated ADTs are *ordinary* importable
  `.cl` modules found by ordinary `resolve_module_file`, NOT `CRANELISP_PLATFORM_PATH`, NOT a
  privileged `platform.<name>.*` mount). Platform FQ-sig checks pass an empty
  `PreludeFallback::default()` (FQ leaves never need the bare-name fallback — `src/CLAUDE.md`
  "Prelude as an OUTER SCOPE"). Nothing in Pillar A keys orchestration or resolution on a
  module name. Invariant intact.

### (f) Required SCOPE revisions

1. **Pillar A**: re-frame from "four-crate D/D/R" to "**`/platform` fixture (`shapes` ADT-typed
   test-DLL) + `/qa` e2e (0289 items 1–3)**". The load-path, dispatch arm, generator, command,
   and PlatformError variant are all landed (S76 W4a/W4b). No int/backend/types implementation
   is owed for items 1–3 — only the fixture + e2e + any marshaling residual the round-trip
   surfaces (0229, re-scoped to the fixture or closed).
2. **Pillar B**: per ruling (d), **no migration work exists as drafted.** Choose option (i)
   drop + re-scope via /design audit FIXME, or option (ii) narrow to exception-comment
   annotation + boundary test. Remove the "`Type::adt` → take `FQTypeName`" and
   "`*_chain` → `&FQTypeName`" line items — both are rejected by the Decision-0047 analysis.
3. **FIXME debt table**: mark **0293 RESOLVED (deleted this review)**; mark **0233 + 0238
   stale → close** (superseded by W4b); re-point **0229** to the fixture or close.
4. **Wave plan**: Wave A collapses — there is no per-crate Pillar-A implementation triad.
   Wave 0 = `/platform` fixture + `/qa` failing e2e; Wave A = `/qa` green-up + Phase-6
   validation; Pillar B (if kept) runs as a tiny parallel `/design`+`/qa` slice.

### (g) Verdict: SIGN-OFF (Phase 2 passed) with the (f) scope revisions

Architecturally coherent, disjoint, no interim-architecture risk, no S78 regression. The
platform-interface mechanism is target-state and landed; this sprint exercises it. Pillar B's
drafted migration does not survive Decision-0047 analysis and must be re-scoped or dropped.
Proceed to Phase 3 with the (f) corrections folded into scope.

**/arch files changed this review:** `sprints/SPRINT.md` (this section); deleted
`design/arch/fixmes/0293-arch-platform-error-hash-refusal-variant.md` (fully resolved). No
`cranelisp-types` source change (no new cross-crate interface type is needed — the
PlatformError variant already landed). No facade/BC edit needed (BC §3/§5/§6 +
`platform-interface.md` are already target-stating and consistent with landed source).

## Skill plans (Phase 3)

_Collected 2026-06-12. Three parallel agents (/qa, /arch, /platform). Two discovery gaps surfaced before any test ran — see "Discovery (known gaps)" below._

### /platform — `shapes` ADT-typed test-DLL fixture
- **Task**: author `platforms/shapes/` (5th workspace member, `cdylib`+`rlib`): a `Rectangle` ADT in an ordinary `.cl` module + an `area : (Fn [shapes/Rectangle] primitives/Int)` platform fn that reads `w`/`h` host-side and returns `w*h`. `declare_platform!` under ABI v3 with embedded generated schema (`include_str!("shapes.platform-schema")`).
- **Design refs**: `design/arch/platform-interface.md` §4/§5.5/§7; FIXME 0289 item 1.
- **Acceptance**: `(area (Rectangle 3 4))` ⇒ 12 across the DLL boundary; non-empty schema + `__cranelisp_layout_hash_shapes` emitted; `got_slot: Some(0)` activates the dormant backend GOT-indirect arm.
- **Mechanism status (recon)**: `alloc_with_tag` live (`src/platform.rs:240`); GOT-indirect dispatch arm landed (`apply.rs:494`); `generate_schema`/`compute_layout_hash` deterministic; dual gate in `worker.rs:2700`; `/platform-schema` in `session_v4.rs:3554`. Fixture is buildable today **except** the schema field-name gap (below).

### /qa — OUTPUT-COVERAGE: RE-SCOPED (user 2026-06-12, post-audit)
> **RESOLUTION**: the full output-coverage reshape **defers to S80**, landing together with `main : IO _` enforcement (converting ~150 mains to IO *before* the compiler requires it is premature). **S79 keeps only**: (1) the RED forcing-function test `batch_main_pure_int_return_is_rejected` (ledgered, failing-not-ignored — the durable obligation guard); (2) a minimal `--link` + `stdio` `print` → stdout test as the simplest **R1 guard** (isolates "is `--link` platform wiring alive at all" from the richer `shapes` ADT marshaling), needing a small stdout-capture helper, not the full `run_through_all_modes_output` harness. Everything below is the S80 increment design, retained for the handoff.

### /qa — OUTPUT-COVERAGE GAP CLOSURE (DEFERRED → S80 increment; design retained)
- **Directive**: "qa should close the test coverage gap of having the majority of programs produce output." The all-modes mode-equivalence corpus (`tests/build_confidence.rs::run_through_all_modes`, 11 programs) is **almost entirely pure** (arithmetic, ADT match, `Pure 7`) — so cross-mode equivalence only ever tests **exit-code equivalence**, the thinnest channel. **Conceptual ruling (user)**: linking a *pure* program is a weak/near-meaningless test — a standalone executable exists for its observable effect; a pure `main` has none. Meaningful mode-equivalence is **output equivalence** (same stdout across REPL / `--run` / `--link`), which requires output-producing (platform-IO) programs — making R1 (`--link` platform IO) a **prerequisite**, not a side-feature.
- **Task**: (1) audit the corpus — quantify how many test programs assert observable stdout vs only exit codes; (2) plan the reshape so the **majority** produce + assert real output, verified equivalent across all three modes; (3) decide the disposition of the pure `--link` permutations (drop, or keep as minimal pipeline smoke); (4) author the failing-first output-equivalence tests (the `--link` halves fail until R1 lands — QA-first intended state). The simple built-in case (`--link` + `stdio` `print`) is the floor; the `shapes` ADT round-trip is the rich case.
- **Acceptance**: majority-produce-output gap closed; output-equivalence asserted across REPL/`--run`/`--link`; pure-`--link` disposition recorded.
- **Sequencing**: this is the leading edge of Phase 5 Stage 1 (QA-first). Bring the audit + reshape plan back for user review before mass test authoring.
- **Audit result (2026-06-12)**: 3 of 911 tests assert program-produced stdout, all `--run`-only; zero cross-mode output coverage; zero `--link`+platform coverage. "Majority produce output" is false. **Scope decision: FLOOR this sprint** (new stdout harness + `--link` `print` floor test + ~3 output mode-equiv programs + ~2 kept smoke); full-corpus conversion → S80.
- **Spec grounding (the pure-`--link` ruling)**: `spec/02-grammar.md:25` + `spec/10-io.md:244–247` (`main :: (Fn [] (IO _))`) + `spec/12-runtime.md:173` — **batch `main` MUST return `IO _`**; a batch/`--link` main is *always* an IO action by type. There is NO spec-conformant pure (non-IO) entry point. **Finding**: the mode-equiv corpus's `(defn main [] 0)` / `(add-i64 1 2)` / ADT-match programs return bare `Int`, NOT `IO _` — spec-non-conformant mains the compiler accepts only via an unenforced leniency. **Disposition (spec-grounded)**: no bare-pure mains; kept-smoke mains become `(defn main [] (pure 0))` (conformant trivial-IO, nil effect, exit 0); majority become `(print …)` observable — the output reshape IS the conformance fix.

### /qa — platform e2e (0289 items 1–3) + FQTypeName boundary coverage
- **Task**: `tests/spec_platforms_adt.rs` — failing-first then green. Item 1 round-trip (`_run` + `_link`, exit 12 + neg checks); Item 2 dual hash-gate (`_run_refuses` / `_repl_warns_and_loads` / `_link_refuses`, both hashes + rebuild guidance, drift induced test-side by editing the program `deftype`); Item 3 cache-restore (`CRANELISP_MODULE_TRACE=1` proves cache hit). Pillar B: `tests/spec_fqtypename_boundary.rs` — two-module same-short-name (`a/Box` vs `b/Box`) resolve-distinctly + FQ REPL introspection display (the e2e cement /arch named).
- **Design refs**: 0289; `tests/spec_platforms.rs`/`platform_errors.rs` patterns; `Cranelisp` builder + `.use_workspace_platforms()`.
- **Acceptance**: e2e green for `--run`/REPL halves (firm); `--link` halves gated on R1 (below). Add `[S79]` ledger rows; `// spec:` traces to `spec/` first then `platform-interface.md §`.

### /arch — FQTypeName resolved-stage boundary audit (Pillar B) — COMPLETE
- **Outcome**: full classification of every identifier-carrying public site in `cranelisp-types` (29 sites). **(D)-count = ZERO** — every resolved-stage boundary is FQ-carrying (class A); all bare-`TypeName` hits are exception-1 (display: `get_impls_for_type_chain`/`get_implementing_types_chain`/`ResolveError`), exception-2 (context-supplied chain-resolvers `lookup_*_chain` + receiver-pinned `TraitDeclInfo::name`), or syntactic-stage (`ParsedEntry`/`TopLevel`/`TypeRef`/`TraitRef`/`ImplSexp`). FQTypeName binding (Decision 0047, delivered S67 W5) is real across the surface. **Arc is retire-able.**
- **Cement (the coverage gap)**: (1) e2e two-module same-short-name disambiguation (/qa, above); (2) `cranelisp-types` unit test asserting `Type::adt(module,name,args)` → `Type::ADT(fq)` with `fq.module` populated + two same-`name`/different-`module` adts `!=` (/dev, in-crate).
- **Exception-annotation plan** (Phase-5 /dev): `// FQTypeName exception 1/2` comments at the 6 named sites (`module.rs:1935/1985/1886/1910`, `check.rs:215`, `resolve.rs:104/113`).
- **Retirement manifestation**: S79 Outcome + flip `project_fqtypename_priority` memory to delivered+cemented + Decision 0047 → legacy/embodied (BC §7 already states it correctly — no canonical-doc edit owed). Expected `public-api.txt` delta: **ZERO**.

## Discovery (known gaps — surfaced in Phase 3, before tests ran)

| # | Gap | Owner | Likelihood | Detail |
|---|---|---|---|---|
| R1 | **`--link` platform path is an unwired stub** — **COMMITTED /dev (int) work this sprint (user 2026-06-12)** | /dev (int) | CERTAIN | `find_platform_rlibs()` (`exe.rs:779`), `collect_platform_manifest_names()` (`exe.rs:838`), `platform_layout_checks` (`session_v4.rs:3954`) all empty/TODO. The `--link` bake seam + linker rlib arm exist + are unit-tested, but nothing feeds them from a loaded platform. /dev wires loaded-platform → rlib-path + manifest-names + `PlatformLayoutCheck` derivation, so the `--link` round-trip + link-refuse halves go green. Largest single workstream this sprint. |
| R2 | **Product field-name loss in `generate_schema`** | /dev (backend) | HIGH | Single-ctor product type's key holds a `TypeDef` (not `Def`), so `ctors_of` (`schema.rs:203`) takes the product `else if` and emits positional `_0`/`_1`, losing `w`/`h`. The DLL's `read_field("w")` panics. Fix: product arm recovers real field names from `TypeDefInfo`/ctor `param_names`; existing `_0`/`_1` test flips to `w`/`h`. Local to `schema.rs`. |
| R3 | 0287 GOT symbol-name agreement (`__cranelisp_got_platform_shapes` vs `got_data_symbol_name`) | /dev (backend) | LOW | Dormant arm never run against a real DLL GOT; first round-trip exercises it. |
| R4 | RC consuming-convention balance on the ADT arg across the boundary | /dev | LOW–MED | `area` reads-only/returns scalar; confirm no leak/double-free under `CRANELISP_RC_TRACE=1`; if leak, `area` `into_owned_consuming`s the arg. |

## Waves (Phase 4)

- **Wave 0 — fixture + failing tests.** DONE: `/qa` output-coverage audit + traceability audit + the RED forcing-function test `batch_main_pure_int_return_is_rejected` (rides red, ledgered; enforcement+sweep → S80 / FIXME 0317). REMAINING: `/platform` authors `platforms/shapes/` (crate + `lib.rs` + placeholder schema + `shapes.cl`); `/qa` authors failing-first `tests/spec_platforms_adt.rs` (round-trip + drift + cache, `--run`+`--link`) + the minimal `--link`+`stdio`-`print` R1 guard + `tests/spec_fqtypename_boundary.rs`. (FQTypeName audit + the full output-coverage reshape are NOT S79 — audit done Phase 3, reshape deferred to S80.)
- **Wave A — discovery fixes + green-up.** `/dev` (backend) fixes R2 product field-name loss (then regenerate + commit `shapes.platform-schema`); `/dev` (int) implements R1 `--link` platform wiring (COMMITTED — `find_platform_rlibs` / `collect_platform_manifest_names` / `PlatformLayoutCheck` derivation) **+ platform-fn-IO enforcement (FIXME 0318, low-ripple)**; `/platform` fixes `shapes` `area` → `IO` (FIXME 0318); `/dev` reactive on R3/R4 if surfaced; `/arch` (owns `cranelisp-types`) adds the FQTypeName `Type::adt` unit test + exception-1/2 comments (per /arch plan). `/qa` reconciles hash-gate tokens + drives both e2e files to green (both `--run` AND `--link`). Backend (R2) and int (R1) touch disjoint crates → parallel.
- **Wave R2 (folded in — Option 3 product-ctor-as-Def correction, user 2026-06-12).** A sequenced facade-first cascade (push types to target, accept broken build, fix consumers wave-by-wave per `feedback_facade_first_migration`):
  - **R2.1 — `/arch` (cranelisp-types)**: retire `ModuleEntry::TypeDef.constructor_scheme`; add the type facet `type_def: Option<Box<TypeDefInfo>>` to `DefKind::Constructor` (3a; present iff the ctor IS its type — the product case); cache-schema bump + serde + rustdoc + BC §7 + interfaces + baseline. Produces the precise consumer-change spec. Build breaks by design.
  - **R2.2 — consumer cascade (`/dev` narrow)**: typecheck (`adt.rs` stop-overwrite + attach facet; `checker.rs` uniform type-def accessor; delete `find_same_name_constructor_scheme` + 3 `constructor_scheme` reads; `infer.rs` delete the product fallback leg); backend (`compiler/mod.rs::extract_constructor` collapse to the `Def` arm; `schema.rs` product branch reads real `param_names` — the 0319 fix lands here + flip `product_type_schema_lists_typed_fields`; `heap.rs` product branch drops); int (`display.rs` collapse to `Def` arm — FIXME 0302 patch becomes unnecessary; `bootstrap.rs` seeded products `Pair` attach the facet; int got-slots + enumerates the product ctor into the codegen batch).
  - **R2.3 — `/qa` green-up**: the MISSING product-ctor-as-first-class-value e2e (`(deftype R [:Int w :Int h]) (let [f R] (f 1 2))`, `(map R …)` — RED today, the §4.2.1 spec-violation guard) + the 0319 schema field-name test; regenerate `shapes.platform-schema`; full `cargo nextest` green-up.
- **Wave B — Phase 6 + retirement.** `/platform` Phase-6 validation (first real FFI ADT capability exercised e2e); FQTypeName arc retirement recorded (Outcome + memory + Decision 0047 → legacy).

## Wave 0 outcome (2026-06-12)

**DONE.** `/platform` authored `platforms/shapes/` (5th workspace member; `cargo build -p cranelisp-shapes` clean; dylib + `__cranelisp_got_platform_shapes`/`__cranelisp_layout_hash_shapes`/manifest exported; placeholder `w`/`h`-named schema + sentinel hash pending R2 regen; conservative `into_owned_consuming` RC choice for R4). `/qa` authored `tests/spec_platforms_adt.rs` (8 tests) + `tests/spec_fqtypename_boundary.rs` (4 cement, expected green) + ledger rows; spec-link clean; failing-not-ignored. Fixture interface matched the contract — no drift.

**Platform-fn-IO tightening (user 2026-06-12, FIXME 0318):** the spec only *conditionally* requires platform fns to be IO (`08-modules.md:783`), but foreign purity is unverifiable → unsound. **Decision: all platform fns MUST be IO.** Every existing platform is already IO; the `shapes` `area : (Fn [Rectangle] Int)` is the ONLY violation (and we're fixing it) → **enforcement is LOW-RIPPLE and folds into S79 Wave A**: (a) `/platform` fixes `area` → `(Fn [shapes/Rectangle] (IO primitives/Int))` (Rust follows the stdio IO pattern); (b) `/dev` (int) enforces "platform fn return MUST be `IO _`" in `register_platform_in_tc` + a unit forcing test (no sweep — nothing else violates); (c) `/spec` tightens `08-modules.md:783` to unconditional. This **resolves reconciliation item #1** — `area` returning `IO Int` makes the round-trip `main` spec-conformant for free.

**Wave-A reconciliation items (surfaced by the agents):**
1. **Round-trip `main` is bare-`Int`** — RESOLVED by the platform-fn-IO tightening above: with `area : (Fn [Rectangle] (IO Int))`, `(defn main [] (area (Rectangle 3 4)))` returns `IO Int` → conformant. (Observable-output nicety — printing `12` — is already covered by the separate `platform_stdio_print_link` R1 guard; the shapes round-trip stays `area → IO Int → exit 12`.)
2. **Hash-gate stderr tokens** — /qa asserts the refusal names `shapes` + `hash`/`layout` + rebuild guidance; reconcile against the real `PlatformError::LayoutHashMismatch` Display wording (cheap, substring-based).
3. **R2/R3/R4 from /platform** — R2 (regenerate the real schema after the backend field-name fix), R3 (GOT symbol-name agreement on first round-trip), R4 (drop the `into_owned_consuming` line if `CRANELISP_RC_TRACE=1` shows a double-free).

## Wave A outcome (2026-06-12)

**3 of 4 landed; R2 escalated (genuine data-model gap).**
- **R1 ✅** (`/dev` int): `--link` platform path wired — `CompilerSession::linked_platform_link_data()` sources rlib paths + manifest names + `PlatformLayoutCheck`s from `SharedState.kept_dlls`; feeds the existing bake seam + force-load arm. `cargo check -p cranelisp` clean; 31 exe/platform tests green. **Known limit (documented)**: multi-platform `--link` collides on the `cranelisp_platform_manifest` symbol — single-platform (the S79 target) fully wired; multi-platform is a future item.
- **0318 ✅** (`/dev` int): `require_io_return` in `register_platform_in_tc` + 3 forcing unit tests (non-IO sig rejected, IO accepted). Low-ripple confirmed — `stdio` real-DLL test still green.
- **Fixture IO ✅** (`/platform`): `area` → `(Fn [shapes/Rectangle] (primitives/IO primitives/Int))`, Rust returns `CLIO<CLInt>` mirroring `stdio::print_string` (deferred effect + consuming-RC capture). Resolves reconciliation #1. Clean build, 3 exports present.
- **FQTypeName cement ✅** (`/arch`): 2 `Type::adt` FQ unit tests (pass) + 6 exception-1/2 comments. Clean.
- **R2 ❌ → FIXME 0319** (`/dev` backend, correctly escalated): single-ctor **product** field names are DROPPED from the symbol table — the ctor `Def` (holds `param_names`) and the `TypeDef` collide on key `"Rectangle"`; `TypeDef` overwrites, `TypeDefInfo` carries no field-name list, `constructor_scheme` has types-not-names. Schema generator can only emit positional `_0`/`_1` → platform `read_field("w")` fails. **Needs a `cranelisp-types`+`cranelisp-typecheck` change** (out of backend scope). No backend edits made; unit-test flip deferred (would be permanently red). **On the critical path for Pillar A** (the round-trip can't work without correct field names).

**R2 / 0319 — /arch design survey (2026-06-12, user-requested before picking a shape):** the user's instinct was right — product ctors should be proper `Def`s like sum ctors. **Field-name loss is one of 3 symptoms**; the decisive one is a **live spec violation (§4.2.1)**: a product ctor used as a first-class value (`(map Rectangle xs)`, `(let [f Rectangle] f)`) fails to compile (no GOT slot, absent from `defined_symbols()`) — and is UNTESTED (only sum-ctor-as-value is tested). Construction/scheme/display/match survive only via **six bespoke `constructor_scheme` fallback legs** (the S78 thread-at-one-seam anti-pattern). **/arch recommends Option 3 (dual-facet entry)**: the got-slotted ctor `Def` survives for the `"Rectangle"` key + carries a type facet (3a: `type_def: Option<Box<TypeDefInfo>>` on `DefKind::Constructor`); retire `TypeDef.constructor_scheme` + the six fallback legs. Fixes (a)/(f)/(b) by construction; mostly deletion; product ctors stop being special (Principle 16 / Decision 48). Blast radius MEDIUM — all 5 crates, a `cranelisp-types` enum change, cache-schema bump. **/arch rejects the cheap `field_names`-on-`TypeDefInfo` patch** (leaves the spec violation live + Principle-7 dual store). **Not platform work — an ADT data-model correction. Timing decision pending (fold into S79 vs own increment vs cheap-patch-now).**

## Wave R2 cascade status (2026-06-12)

- **R2.1 ✅** (`/arch`, cranelisp-types): dual-facet landed — `DefKind::Constructor.type_def` added, `TypeDef.constructor_scheme` retired; `cargo check -p cranelisp-types` green; baseline + BC §7 + interfaces updated; FIXME 0320 filed (cache bump → backend).
- **R2.2 typecheck ✅** (`/dev`): green independently; introduced `type_def_view_of` accessor; **discovery**: the load-bearing consumers were `lookup_type_def`/`resolve_type`/`concrete_type_for_impl_target` (product-as-type resolution), beyond the spec's enumerated sites. Zero new clippy.
- **R2.2 backend ✅** (`/dev`): green independently; **the 0319 fix landed** (schema product branch reads real `param_names` → `(w …)(h …)`, test flipped); cache `CACHE_SCHEMA_VERSION` 3→4 (FIXME 0320 resolved+deleted); **discovery**: extra heap sites `classify_adt`/`is_mixed_adt` would have mis-classified products. Zero new clippy.
- **R2.2 int ✅ (compiles)** (`/dev`): `src/` changes landed (bootstrap `Pair` dual-facet, display collapse, got-slot enumeration). Agent returned incomplete + left stray background nextest jobs. **`/sprint` verified directly**: `cargo check -p cranelisp` GREEN (2m14s) — the full cascade (types→typecheck→backend→int) compiles.
- **dyld false-alarm (investigate-first, S78 lesson)**: the int agent's 4 new product-ctor unit tests appeared to HANG (>10min). **Diagnosed NOT a bug**: `sample` of the hung PID showed 0.0% CPU, `state SN`, entire stack in `_dyld_start`, 112K footprint — **macOS dyld cold-start on the large debug binary** (the documented S78 hazard: `--list` 31s cold / 0.00s warm), severely compounded by concurrent `nextest` invocations thrashing the page cache. No loop, no deadlock. Nearly mis-framed as a codegen-loop defect; the sample overturned it. **Mitigation for green-up: ONE nextest invocation (not concurrent), patient on the single cold load, `-j2` optional.**
- **R2.3 — /qa green-up DONE (NOT green)**: full `--no-fail-fast` run = **1090 passed / 105 failed / 8 skipped** (baseline 1175/1175). `cargo check` green hid it (compiles ≠ passes). 104 real regressions + 1 intended-RED. /qa filed **FIXME 0321** (4 roots + fix order) + committed 2 minimal failing guards. Product-ctor-as-first-class-value e2e (the §4.2.1 guard) already existed + PASSES post-fix. Schema regen + round-trip BLOCKED on Root B-shapes.
- **R2.4 — fix wave (FIXME 0321):**
  - **Root A ✅ FIXED** (`/dev` typecheck, ~89 tests): the deleted `lookup_constructor_scheme` was ALSO the only path splitting a qualified ctor name on `/` in patterns → `macros/SCons` looked up as one literal key. Added `resolve_constructor_entry` (qualified→named module per §8.6.6; bare→current+prelude). Macro repro exits 41; 365 typecheck unit tests pass. No product re-break.
  - **Root B-prim ✅ FIXED** (`/dev` frontend): reclassified — a PRE-EXISTING `cranelisp-frontend` bug (`read_colon_prefix` tokenized `:primitives/Int` as 3 tokens). Added `read_qualified_tail`; 269/269 frontend tests pass.
  - **Root C ✅ FIXED** (`/dev` int): product-ctor display updated for the dual-facet (`lookup_type_def_from_tables` + `format_def_entry` read the `type_def` facet) — `(Point 3 4)` + single-qualified name.
  - **Root B-shapes layer-1 ✅ FIXED** (`/dev` int): `fqize_type_expr` now splits `shapes/Rectangle` via `split_slashed_type_ref` across all arms. Error moved `module ''` → `module 'shapes'` (split confirmed working).
- **R2.4-cont — shapes round-trip's two REMAINING layers** (surfaced exercising it for the first time; the discovery half): (1) **typecheck `resolve.rs::resolve_named`** doesn't accept a product-ctor `Def` as a type (still `TypeDef`/`IntrinsicType`-only — a MISSED dual-facet cascade site); (2) **fixture mismatch** — the sig says `shapes/Rectangle` but the test program defines `Rectangle` in its entry module → `shapes.cl` must be a loadable `shapes` module the program imports (per the platform-interface design), not defined locally. Both round-trip-specific.
- **R2.5 — re-assessment green-up DONE**: 1190/1202 (1225s). 12 failed = 1 intended-RED + 5 stragglers + 6 shapes round-trip. Root A cleared ~89.
- **R2.6 — straggler fixes ✅ (all 5)**: Issue 1 (`/dev` typecheck — `resolve_named`/`resolve_applied` accept product-ctor `Def` as type, the missed cascade site; unblocks shapes type-res too); Issue 3 ×2 (`/dev` typecheck — product-ctor under-application errors instead of currying); 0322 ×3 (`/dev` int — `:`-prefix guard at TWO masked FQ-autoload seams `worker.rs::recognize` + `expander.rs::recognize_macro_head`; clears `s79_fq_field_type` + the 2 FQTypeName cements). 368/368 typecheck unit tests; primary repros verified. **Projected ~1195/1202 — only the 6 shapes round-trip + 1 intended-RED remain (pending confirming green-up).**
- **R2.7 — shapes round-trip (DECISION PENDING)**: the 6 need Issue 2 (fixture — `Rectangle` must be a loadable `shapes` module the program imports, not defined in the entry module; Issue 1 now unblocks the type-resolution once it's reachable) + schema regen. First e2e run of the platform-ADT-module-loading path — consistent with the discovery pattern, may surface more layers. **Decision: push to green this sprint vs land the correction green-minus-6 + finish the round-trip as a focused S80 follow-up.**

## Notes

- 2026-06-12 — Phase 1 scope drafted. User chose both platform round-trip + FQTypeName as the Stage-2 centerpiece. Pillars are disjoint (platform/backend/int/qa vs cranelisp-types) → parallelizable.
- 2026-06-12 — User narrowed Pillar A to round-trip + hash-gate (0289 items 1–3); perturbed-ABI + dispatch-error e2e (items 4–5) deferred to S80. Advanced to Phase 2 (/arch review).
- 2026-06-12 — **/arch Phase-2 sign-off overturned the draft premise on three of five questions**: platform mechanism already landed (S76 W4b commit `2d754f3`; FIXMEs 0286/0288 resolved+deleted; 0293 deleted this review; 0233/0238 stale→close); FQTypeName's four named sites do NOT migrate (already compliant / exception-2). Both changes are *in source*; what's missing is *tests that exercise them*.
- 2026-06-12 — **User reframed S79 as a test-cementing sprint** + chose **lean + discovery**: Pillar A = fixture + e2e + fix surfaced gaps (the round-trip has never actually run); Pillar B = FQTypeName **test-coverage audit → close gaps → get to green → retire the arc** (not a migration). Advanced to Phase 3.
- Caveat (S25 lesson): the platform ADT path is built but unexercised — "scaffolding without the final codegen step" until the `shapes` fixture proves it. The discovery half is real work, not a formality.
- 2026-06-12 — Phase 3 design collected (/qa + /arch + /platform, parallel). **Two discovery gaps surfaced pre-test**: R1 `--link` platform path unwired stub (/dev int, CERTAIN, largest); R2 product field-name loss in schema generator (/dev backend, HIGH). /arch FQTypeName audit: (D)-count = ZERO, arc retire-able.
- 2026-06-12 — **Scope decision: commit R1 `--link` wiring to S79** (user). Both `--run` and `--link` round-trip + hash-gate halves are firm acceptance this sprint. S79 now carries two committed implementation workstreams (backend R2 + int R1) atop the fixture + e2e — discovery-shaped but no longer ultra-lean. Phase 4 waves locked; advanced to Phase 5.
- 2026-06-12 — Investigated "how are all-modes combination tests green if `--link` platform is stubbed?": **they are all platform-free** (`run_through_all_modes` corpus is pure; only platform/IO test runs `--run` only). `--link` + platform has never been exercised and can't work today (compile-time dlopen'd fn-ptr can't survive into a standalone binary; needs the static rlib force-load R1 wires). Confirms R1 is real + necessary.
- 2026-06-12 — **User scope expansion: /qa output-coverage gap is the leading workstream.** Mode-equivalence on pure programs only tests exit-code equivalence (thin); the majority of programs should produce + assert OUTPUT, verified equivalent across all three modes. Linking a pure program ruled a weak test. Elevates R1 to a prerequisite for meaningful all-modes testing. /qa to audit + plan reshape (review-gated) before mass authoring.
- 2026-06-12 — /qa audit returned (3/911 produce output, all `--run`). **Scope = FLOOR this sprint** (user); full-corpus → S80. **Pure-`--link` ruled on spec grounds**: spec MANDATES `main : (Fn [] (IO _))` (02-grammar/10-io/12-runtime) — no pure entry point exists; corpus bare-`Int` mains are an unenforced-leniency conformance gap; kept-smoke mains become `(pure 0)`, majority `(print …)`. **One /spec FIXME to file**: "observable output across run modes" invariant (currently only in PLAN.md + Principle 11, not spec).
- 2026-06-12 — **User directive: enforcement becomes a forcing function, not a deferred FIXME.** (1) /qa authors a **failing-first negative test** that a pure (bare-`Int`, non-`IO`) batch `main` is REJECTED — red today (compiler leniently accepts), so "the suite cannot be green without the enforcement change." Pulls `main : IO _` enforcement IN-SCOPE. (2) /qa runs a **traceability audit** against `02-grammar.md:25` / `10-io.md:244` / `12-runtime.md:173` — "something was missed" (false `[Tested]` or no trace, since pure mains pass). **Ripple flagged**: enforcement breaks every BATCH-mode bare-`Int` main (link.rs, mode-equiv `--run`/`--link`, examples/exemplar; REPL exempt) → a suite-wide sweep larger than the floor. /qa to QUANTIFY the sweep before sizing.
- 2026-06-12 — **Platform-fn-IO tightening (user)**: spec only conditionally requires platform fns to be IO; foreign purity unverifiable → unsound. Decision: ALL platform fns MUST be IO. Filed **FIXME 0318** (target /spec). Low-ripple (shapes `area` is the sole violation) → enforcement + fixture fix fold into S79 Wave A; resolves Wave-0 reconciliation item #1.
- 2026-06-12 — **Sizing resolved (user): defer enforcement + sweep + full output reshape to S80** (land together when the compiler enforces; pre-enforcement main rewrites are premature). S79 keeps the RED forcing-function test (ledgered guard) + a minimal `--link`+`stdio`-`print` R1 guard. Filed **FIXME 0317** (target /spec) capturing the S80 increment. S79 closes green-except-the-ledgered-red-guard.
- 2026-06-12 — **/qa report back.** (1) `batch_main_pure_int_return_is_rejected` authored in `tests/spec_10_io.rs` — confirmed RED, un-ignored, ledger row added. (2) **Traceability miss**: all three refs carry stale `[R4 S10]` (never traced) AND existing tests positively certify the violation — `run_mode_main_returns_int_exit_code` asserts `(defn main [] 7)`→exit 7; `spec_12_runtime` exit-code tests use bare-Int mains; `link.rs::link_error_when_main_returns_wrong_type` uses an accepting `Int||IO` disjunction. Test-design defect, not just a gap. (3) **Sweep = SUITE-WIDE**: ~125 batch bare-Int mains across ~11 test files + ~22 example files + ~4 exemplar repros + the examples exit-code-checksum convention needs rework. **Far exceeds the S79 floor + committed R1/R2/shapes.** /qa verdict: enforcement + sweep is a dedicated increment; the red test should ride as the forcing-function guard while the sweep schedules. **Sizing fork pending user.**

## Outcome (Phase 7)

**Baseline (confirmed green-up, 1346s)**: **1196 passed / 7 failed / 8 skipped** (1203 run). Started 1175/1175. The 7 failures are EXACTLY the deliberate deferrals — no stragglers: `batch_main_pure_int_return_is_rejected` (intended-RED, main:IO forcing guard → 0317) + the 6 `spec_platforms_adt` round-trip/hash-gate/cache tests (→ 0323). All 5 cascade-regression fixes (Root A + 4) cleared.

### Delivered
- **Platform `--link` wiring (R1)** — `linked_platform_link_data()` sources rlib paths + manifest names + `PlatformLayoutCheck`s from the loaded-platform registry; standalone executables support (single) platforms for the first time. The `platform_stdio_print_link` guard (built-in `stdio` `print` → stdout under `--link`) is GREEN.
- **All platform fns MUST return `IO _` (0318)** — `require_io_return` enforcement in `register_platform_in_tc` + forcing tests; spec-grounded (foreign purity unverifiable); low-ripple (only the `shapes` fixture violated, fixed to `IO`). `/spec` cascade to make `08-modules.md:783` unconditional carried in 0318.
- **Product constructors are proper `Def`s (the Option-3 data-model correction — unplanned, surfaced by R2)** — single-ctor product types are now got-slotted ctor `Def`s carrying a `type_def` facet (not absorbed into `TypeDef`); `constructor_scheme` + six bespoke fallback legs RETIRED. **Fixes a latent §4.2.1 spec violation** (product ctors as first-class values — `(map R xs)`, `(let [f R] f)` — were silently broken + untested). Cascaded across `cranelisp-types` → typecheck → backend → int; cache schema v3→v4. The §4.2.1 first-class-value e2e + product-ctor arity errors are now correct.
- **FQTypeName arc — audited + retired** — full resolved-stage boundary audit ((D)-count = 0); `Type::adt` FQ unit test + 6 exception-1/2 annotations cement compliance. The standing project priority is **RETIRED** (delivered S67, cemented S79).
- **`main : IO _` conformance forcing-test** — `batch_main_pure_int_return_is_rejected` (RED, ledgered) makes the suite unable to go green without the enforcement change; traceability miss documented (stale `[R4 S10]` + tests certifying the violation).
- **5 cascade-regression fixes** — qualified-ctor pattern resolution (Root A, ~89 tests); frontend colon-prefix qualified-type reader (B-prim); product-ctor display dual-facet; `fqize_type_expr` slash-split; `resolve_named` product-ctor-as-type; `:`-prefix guards at two masked FQ-autoload seams.

### Deferred (with rationale)
- **Platform-ADT round-trip — 6 `spec_platforms_adt` tests (→ FIXME 0323, S80)**. Machinery delivered; the round-trip rides RED on one remaining layer (the fixture must make `Rectangle` a loadable `shapes` module the program imports, per `platform-interface.md` §2). Deferred by user decision (2026-06-13) to avoid open-ended discovery at session end — the path has never run e2e and consistently surfaced one more layer each exercise. Failing-not-ignored; the 6 tests ARE the durable record. To be finished in a focused S80 platform/conformance increment alongside 0317 + 0289 items 4-5 + 0316.
- **`main : IO _` enforcement + suite-wide sweep (→ FIXME 0317, S80)** — ~125 batch bare-`Int` mains + ~22 examples + exit-code-checksum rework + full output-coverage reshape. Land together when the compiler enforces (pre-enforcement rewrites are premature). The RED forcing-test is the guard.
- **Import-ambiguity model + `resolve_with_fallback` unification (FIXME 0316)**; **perturbed-ABI + dispatch-error platform e2e (0289 items 4-5)**.
- **Phase 6 user-facing** waived (consistent with the post-S68 pattern; the language-visible surface this sprint — product-ctor-as-value, platform IO enforcement — is covered by the e2e suite).

### Findings (record in FIXMEs if not already)
- **Investigate-first overturned the framing repeatedly** — the apparent 10-min test "hang" was the documented S78 macOS dyld cold-start hazard (proven by `sample`: 0% CPU in `_dyld_start`), NOT a codegen loop; nearly mis-handed to `/dev` as a phantom bug. Root B-prim was a pre-existing frontend bug, not a cascade regression. The user's "is a product fn pure?" / "should product ctors be Defs?" probes each overturned a settled assumption and surfaced real latent defects.
- **`cargo check` green ≠ tests pass** — the consumer-cascade agents reported "green" on compile-check; only the e2e green-up surfaced the 104 regressions. The data-model boundary change needs a full test run, not a compile gate, as the done-signal.
- **The dual-facet change validated the survey-before-patch discipline** — `/arch`'s "should product ctors be Defs?" survey (user-requested) found 3 symptoms (field names + first-class-value spec violation + representable-state asymmetry) where the cheap `field_names`-on-`TypeDefInfo` patch would have fixed only one and committed a Principle-7 dual store.
- **Discovery dominated a "designed feature" sprint** — the platform round-trip's machinery was "designed + landed" but had never run; exercising it for the first time surfaced a chain of layers (FQ-split → resolve_named → arity → display → module-loading). The S25 "scaffolding isn't proven until it runs" lesson, in full.
- **dyld test-infra tax** — each green-up was ~20-25 min (rebuild + cold-load of the 44 MB debug binary); subagents time out mid-cold-load, so the orchestrator ran green-ups as detached background jobs. Mitigation for future heavy-cascade sprints: warm the binary / `-j2` / `--release` / a smaller test binary.
- **Methodology**: ~16 agent fires across the cascade + fix waves; the facade-first "types to target, broken build, consumers wave-by-wave" discipline held (typecheck + backend cascaded green independently); every consumer found product-as-type sites beyond `/arch`'s enumerated spec (confirming the under-modelling).

### FIXMEs this sprint
Filed: 0317 (main:IO enforcement, /spec), 0318 (platform-fn-IO, /spec), 0319 (product-ctor field names → resolved by the Option-3 cascade), 0320 (cache bump → resolved), 0321 (cascade regressions → resolved by R2.6), 0322 (FQ-autoload colon-split → resolved), 0323 (platform-ADT round-trip completion, /qa S80). Deleted/resolved: 0293, 0320, 0322 + 0321's roots. 0316 carried.
