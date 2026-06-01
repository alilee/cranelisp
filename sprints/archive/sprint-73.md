# Sprint 73: `cranelisp-primitives` self-containment + bounded-context fix

**Status**: CLOSED (Phase 7) — user-approved 2026-06-01; Phase 6 waived (no language-visible change)

**Goal**: Bring `cranelisp-primitives` to a **sound, settled, facade-aligned** shape
— importing only `cranelisp-types` (boundary) + `cranelisp-intrinsics` (runtime
substrate), **not** `cranelisp-backend`. Four moves: (1) **sever the
`cranelisp-backend` dependency** — publish the table as `SymbolTable<(), ()>`; `int`
concretizes to `<Code, ()>` at session mount (S74) via the existing `into_concrete`;
(2) adopt the `ModuleEntry::def` builder with `code: None` (FIXME 0244); (3)
**pin the primitives↔intrinsics heap-layout contract** as intrinsics' blessed public
ABI and remove primitives' layout duplication (FIXME 0245, option A); (4) add a
content+behavioural unit harness. Plus: **fix both bounded contexts/facades** for
the boundary (`bounded-contexts.md §4a/§4b`, `facades/primitives.md`,
`facades/intrinsics.md` incl. closing stale FIXMEs 0190/0213). **Backend is
UNTOUCHED** (cascade + retirement → future sprint); the intrinsics change is a
minimal additive const-exposure, **not** a full intrinsics audit.

**Acceptance**: `cargo nextest run -p cranelisp-primitives` green —
**independently of backend's red state**; `cargo nextest run -p cranelisp-intrinsics`
green (additive consts); no `cranelisp-backend` line in
`crates/cranelisp-primitives/Cargo.toml`; no duplicated layout constants in
primitives; consumed contract pinned in both facades.

## Why this is now backend-independent

Earlier scope assumed the spine *backend green → primitives green → int mount*,
because primitives imported `cranelisp-backend` for the `C = Code` type parameter.
With FIXME 0244 (`code: None` everywhere; primitive-ness from `kind`), primitives
**never constructs a `Code` value** — so it has no reason to name `Code` at all.
It builds a `()`-flavoured table; `int` concretizes at mount. The dependency that
made primitives' build/test hostage to backend's 42-error cascade is removed, and
primitives reaches green on its own this sprint. The int mount (FIXME 0242) and the
backend cascade/retirement remain future-sprint work, now properly decoupled.

## Scope

### A. Sever `cranelisp-primitives → cranelisp-backend`

- `PRIMITIVES_TABLE` type changes `LazyLock<Arc<SymbolTable<Code, ()>>>` →
  `LazyLock<Arc<SymbolTable<(), ()>>>`. `build_primitives_table()` returns
  `SymbolTable<(), ()>`.
- Remove `use cranelisp_backend::Code;` and the `cranelisp-backend` line from
  `Cargo.toml`. The lib.rs `//!` preamble's `Code::Primitive` / dep-ban narrative
  is rewritten to the severed shape.
- The shared `Arc<GotTable>` is `C`-independent and is preserved through
  `into_concrete` (`got: self.got`) — the "one process GOT" invariant
  (BC §4a invariant 6 / 2) holds: `int` does `(*PRIMITIVES_TABLE).as_ref().clone()
  .into_concrete::<Code, ()>()` at the S74 mount, sharing the one static GOT.

### B. Builder adoption + `code: None` (FIXME 0244)

- Rebuild `insert_primitive_entry` + `insert_vec_len_entry` with
  `ModuleEntry::def(scheme, kind).param_names(..).got_slot(slot).build()` — the
  builder default `code: None` is now *correct*; this also fixes the **stale
  missing-`seq` field** (currently masked by primitives not compiling).
- No `Code::Primitive` construction (the variant is gone per 0244); primitive-ness
  is read from `kind: DefKind::Primitive`. The variant's own deletion in
  `cranelisp-backend/src/code.rs` is **deferred to the backend sprint** — it does
  not block this sprint because primitives no longer references `Code` at all.

### C. Content + behavioural unit harness

- **Content:** one row per primitive asserting `Scheme` / `param_names` /
  `jit_name` against the spec contract (Appendix A.2/A.3/A.5) — closes the
  FIXME-0239 drift risk at the unit level.
- **Behavioural:** transmute-and-invoke every pure scalar op against known I/O
  pairs (extend the existing `not` pattern). Heap primitives (`str-concat`,
  `int-to-string`) need the allocator → stay e2e.
- Rewrite `every_entry_carries_code_primitive_marker` → assert `matches!(kind,
  DefKind::Primitive { .. })`.
- These now **actually run** under `cargo nextest -p cranelisp-primitives`, since
  the crate compiles standalone.

### D. Bounded-context + facade alignment (`/arch`)

- `bounded-contexts.md §4a` (Primitives) — corrected for the severance: primitives
  depends only on `cranelisp-types` (+ allocator-by-link-name); no `cranelisp-backend`
  edge; concretization-at-mount is `int`'s.
- `facades/primitives.md` — Public surface (`LazyLock<Arc<SymbolTable<(), ()>>>`),
  §Type shape (drop the "C = Code load-bearing" claim — uniformity is achieved at
  the session layer via `into_concrete`, not by building with `C = Code`),
  §Session-integration contract (`int` into_concrete clone), §Consumed surface
  (remove `cranelisp-backend`).
- `decisions/0048-*.md` — the §"Structural invariant — backend dep-ban" becomes a
  **bidirectional severance** (primitives ⟂ backend); the previously-permitted
  `primitives → backend` edge (for `Code::Primitive`) retires (already obsoleted by
  0244).

### E. Heap-layout contract — intrinsics' blessed public ABI (FIXME 0245)

The `cranelisp-intrinsics` dep is **NOT severable** — it is real, behavioural, and
type-level: primitives' heap primitives Rust-call intrinsics' allocator
(`alloc_string`, `alloc_with_rc`, `rc`, `drop`, `runtime_panic`, `vec_new`) and
read heap layout (`HeapString` offsets; duplicated Vec offsets). The facade's
"no intrinsics dep / call-by-link-name" claim is aspirational and unhonoured.
Decision (A) (user, 2026-05-31): **keep the dep; pin the layout as intrinsics'
public ABI; eliminate primitives' duplication.** Option (B) reader-function
encapsulation rejected (minimum mechanism; no second consumer).

- **`/dev (intrinsics)`** — expose canonical Vec-layout consts as `pub const` on
  `vec_runtime` (`LEN_OFFSET`/`CAP_OFFSET`/`DATA_PTR_OFFSET`), mirroring
  `HeapString::{DATA_OFFSET, LEN_OFFSET}`. Small additive change; `vec_runtime`'s
  own code switches to its consts. Regen `cranelisp-intrinsics/public-api.txt`.
- **`/dev (primitives)`** — delete `vec.rs`'s private `LEN_OFFSET` and `string.rs`'s
  `VEC_*` consts; consume intrinsics' consts exclusively (single source of truth,
  Principle 7).
- **`/design (intrinsics)`** — `facades/intrinsics.md`: name the layout-ABI consts
  as a stable public contract; name `cranelisp-primitives` as a Rust consumer;
  **close stale FIXMEs 0190** (renamed `heap_string`/`vec_runtime` modules) **and
  0213** (stale §"String primitives" section) — facade-doc catch-up against
  already-current source, leaving the intrinsics facade sound w.r.t. this boundary.
- **`/arch` / `/design (primitives)`** — `facades/primitives.md §Consumed surface`
  pins the exact consumed contract; `bounded-contexts.md §4a/§4b` corrected.

This is **not** the full intrinsics audit (extern-signature review, inventory 0178,
facade retirement) — that stays a future intrinsics sprint. S73 firms up the
primitives↔intrinsics **layout boundary** only.

### Triage (assess; in scope only if trivial)

- **FIXME 0182** (`ring0_jit_symbols()` retired) — verify/close.
- **FIXME 0212** (`#[used]` discipline on `pub(crate)` externs) — confirm.

### Out of scope (deferred)

- **All `cranelisp-backend` work** — the 42-error types cascade AND the facade
  retirement (5th data point). Deferred to a future backend sprint, by user
  direction. Includes deleting the `Code::Primitive` variant from `code.rs`
  (decoupled from primitives by the severance) and FIXME 0191 / backend dep-ban
  source cleanup.
- **int FIXME-0242 mount + int cascade** (0098/0187) → S74 host-wiring. Handoff is
  ready: `PRIMITIVES_TABLE` (now `<(),()>`) + the `into_concrete` concretization.
- **Primitives facade retirement** — `facades/primitives.md` stays binding
  (aligned-to this sprint); its fold-into-rustdoc is a later data point.
- **Workspace-wide green** — backend/int/exe-bundle/binary stay red.

## FIXME debt (Phase 1 triage)

| FIXME | Target | Status | Disposition this sprint |
|---|---|---|---|
| 0244 | /arch + /dev primitives | open | **In scope.** Config ratified (Phase 2); primitives source (builder + `code:None`) is deliverable B. `code.rs` variant deletion → backend sprint. |
| 0245 | /arch + /dev intrinsics+primitives | open | **In scope — deliverable E.** Heap-layout = intrinsics' blessed public ABI (option A); expose vec consts; primitives dedups; both facades pin the contract. |
| 0190 | /design intrinsics | **closed (deleted)** | Resolved by /arch Phase 2 top-up — facade now names `heap_string`/`vec_runtime`. |
| 0213 | /design intrinsics | **closed (deleted)** | Resolved by /arch Phase 2 top-up — §"String primitives" reworked to post-S67 state. |
| 0239 | /arch | open | **Partially addressed — deliverable C.** Content harness closes the unit-level test-oracle drift; broader source-abstraction stays deferred. |
| 0182 | /dev primitives | **closed (Wave 2)** | Confirmed: no `ring0_jit_symbols` fn/re-export remains (comment-only). |
| 0212 | — | open → **re-routed to 0247** | `#[used]` premise was wrong (statics-only); DCE mechanism re-disposition owed. |
| 0247 | /arch | **open (filed Wave 2)** | `#[used]` not applicable to `extern fn`; facade's DCE-prevention wording needs correction (export_name + exe-bundle force-link, or `#[used] static` anchor). Non-blocking (exe-bundle deferred). |
| 0189 | /design primitives | open | Triage — facade export-name coverage. |
| 0178 | /arch intrinsics | open | **Out of scope — future intrinsics audit** (inventory). |
| 0221, 0191 | /dev backend | open | **Out of scope — backend sprint.** |
| 0242, 0098, 0187 | /int | open | **Out of scope — S74.** |

## Architecture review (Phase 2 — partial, carries forward)

**FIXME 0244 ratified + cascaded** by `/arch` (2026-05-31, one change-set, config
only): `decisions/0048-*.md` (A2 reversed; A1b accepted), `facades/primitives.md`
(§Type shape / §Static-init / §Consumed / BC-inv #6), `design/arch/CLAUDE.md`
(drain line), `interfaces.md` (`ModuleEntry::Def.code` → 2-variant `Code`),
`facades/int.md` (session-init para). The `ModuleEntry::def` builder is confirmed
present (`cranelisp-types/src/module.rs:1092`; `code: None` default; `seq: 0`).

**Re-scope note**: the backend-specific Phase-2 arbitration (retirement partition,
cascade-width, dep-ban-as-permitted-edge) is **moot** under the re-scope and
retires with the backend deliverables.

**Phase 2 top-up — APPROVE (2026-05-31).** `/arch` enacted both architectural moves
across 6 owned docs: (i) the sever's facade impact — `facades/primitives.md`
(Public surface + §Type shape → `<(),()>`, dropped "C = Code load-bearing", §Session-
integration → int `into_concrete::<Code,()>()`, §Consumed surface drops backend +
pins the intrinsics contract), `decisions/0048` (dep-ban → **bidirectional
severance**), `facades/int.md` (int names `Code` at the concretize-at-mount site),
`design/arch/CLAUDE.md`; (ii) **FIXME 0245 ratified** — `facades/intrinsics.md`
(layout-ABI consts pinned as public contract incl. NEW `vec_runtime::{LEN/CAP/
DATA_PTR_OFFSET}`; primitives named as Rust consumer), `bounded-contexts.md §4a/§4b`.
**Stale FIXMEs 0190 + 0213 resolved and deleted.** No scope revisions.

**Phase-3 caveat (from /arch soundness note).** Vec layout pins cleanly: the consts
already exist `pub(crate)` in `vec_runtime` (header 16 | LEN 16 | CAP 24 | DATA_PTR
32); Phase 5 is a pure visibility promotion to `pub` (additive, ~3 baseline lines).
`/design (primitives)`: when `string.rs` switches its `split`/`join` reads to
`vec_runtime` consts, import only the offsets it uses (LEN + DATA_PTR) — there is no
local CAP use; don't pull CAP blindly. `HeapString::{LEN,DATA}_OFFSET` already `pub`
(pinning is doc-only).

## Outcome (Phase 7)

S73 brought **`cranelisp-primitives`** to a sound, self-contained, facade-aligned
shape — importing only `cranelisp-types` (boundary) + `cranelisp-intrinsics`
(runtime substrate), **not** `cranelisp-backend`. Backend untouched (deferred by
user direction).

**Acceptance met** (independent of backend's red state):
- `cargo nextest -p cranelisp-primitives`: **70 pass / 0 fail**.
- `cargo nextest -p cranelisp-intrinsics`: **76 pass / 0 fail**.
- No `cranelisp-backend` in primitives' `Cargo.toml`; no duplicated layout consts;
  consumed contract pinned in both facades.
- Workspace-wide green explicitly NOT in scope (backend/int/exe-bundle/binary stay red).

### Delivered
- **Backend severed** — `PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>>` (was
  `<Code,()>`); `int` will concretize to `<Code,()>` at the S74 mount via the proven
  `into_concrete` bridge (shares the one process `Arc<GotTable>`). public-api narrowed.
- **Builder + `code: None`** (FIXME 0244, ratified) — both hand-rolled `ModuleEntry::Def`
  literals → `ModuleEntry::def(scheme, DefKind::Primitive).…build()`; `Code::Primitive`
  marker dropped, primitive-ness from `kind: DefKind::Primitive`; fixed the stale `seq`
  field + the crate's own retired-`DefKind::Primitive`-payload compile blocker.
- **Heap-layout = intrinsics' blessed public ABI** (FIXME 0245, option A) — `vec_runtime::
  {LEN,CAP,DATA_PTR}_OFFSET` promoted `pub` + compile-time single-source asserts;
  primitives' 3 duplicated layout consts deleted, now single-sourced from intrinsics
  (Principle 7).
- **Unit harness** — content parity (≥30 rows vs Appendix A.2/A.3/A.5) + behavioural
  (20 pure scalar ops via transmute-invoke); runs standalone (the payoff of the sever).
- **Defects/debt cleared** — FIXME 0215 fixed (was a misdiagnosed test-side pointer-
  precedence bug, not an impl bug — impl was already spec-correct); FIXME 0182 closed;
  `cranelift_op` dead field removed (Principle 7).
- **Config cascade** (/arch) — FIXMEs 0244 + 0245 ratified across 6 docs (facades/
  primitives + intrinsics + int, decisions/0048, bounded-contexts §4a/§4b, interfaces,
  CLAUDE.md); dep-ban → bidirectional severance; FIXMEs 0190, 0213, 0246 resolved + deleted.

### Deferred (with rationale)
- **All `cranelisp-backend` work** (42-error types cascade + facade retirement / 5th
  data point) → future backend sprint. User-directed descope to keep S73 on primitives.
  Includes the `Code::Primitive` *variant deletion* in `code.rs` (decoupled from
  primitives by the sever — FIXME 0244 backend half) and FIXME 0191 / dep-ban source cleanup.
- **int FIXME-0242 mount + int cascade** (0098/0187) → S74 host-wiring. Handoff ready:
  `PRIMITIVES_TABLE` (`<(),()>`) + `into_concrete::<Code,()>()`.
- **Full intrinsics audit** (extern-signature review, inventory FIXME 0178, facade
  retirement) → future intrinsics sprint. The 3 pre-existing `vec_runtime` clippy
  warnings (cast-helper idiom) fold into it.
- **FIXME 0247** (`#[used]` not applicable to `extern fn`; the facade's DCE-prevention
  wording needs re-disposition) → /arch. Non-blocking — `--link` DCE is exe-bundle-side
  (deferred); JIT/rlib keeps fns live via `export_name` + the `extern_shims()` harvest.
  FIXME 0212 re-routed here.
- **E2e regression replay BLOCKED-by-red-binary** → S74. All `tests/*.rs` link the root
  binary → backend cascade, so the Appendix-A guard + `s68_primitives_uniform` can't RUN
  this sprint. Runnable evidence = the crate-narrow unit suites (70/76). 2 backend-
  dependent `s68` assertions `#[ignore]`'d (FIXME 0221/0191), bodies intact.

### Findings / lessons
- **Validate-against-spec-first earned its keep**: FIXME 0215's premise (impl wrong) was
  false — the impl was spec-correct; the bug was in the *test's* pointer arithmetic. The
  rule caught a misdiagnosis that would otherwise have "fixed" correct code.
- **Dropping a redundant marker simplified the dependency graph for free**: choosing
  `code: None` (derive primitive-ness from `kind`) over keeping/setting a `Code::Primitive`
  marker dissolved the builder-setter question AND removed primitives' only use of `Code`,
  which is what made the backend sever a near-trivial type-narrowing rather than a rewrite.
- **Scope discovery, not scope assumption**: the iterative Phase-1 dialogue surfaced that
  primitives was red for *two* independent reasons (backend dep + retired DefKind payload),
  and that the intrinsics dep is load-bearing (behavioural + type-level), not severable —
  reshaping a "backend sprint" into a tightly-bounded primitives sprint.

### FIXME ledger at close
- Resolved + deleted: 0215, 0182 (closed), 0190, 0213, 0246.
- Ready-to-close (both-sides work fully landed this sprint): **0245** — /arch to delete at
  close confirmation.
- Open / carried: **0244** (primitives half landed; backend `Code::Primitive` variant
  deletion deferred), **0247** (/arch — `#[used]` re-disposition), 0221/0191/0242/0098/0187
  (out-of-scope deferrals), 0178 (intrinsics audit).

### Principles check
The sprint was well-served by the existing principles — **Principle 7 (single source of
truth)** drove the layout dedup and the `cranelift_op` removal; **minimum mechanism** drove
option-A-over-reader-functions and the no-builder-setter (`code: None`) resolution; the
**baseline-diff discipline** worked cleanly (every public-surface change paired with its
facade + baseline regen). No principle gap surfaced.

## Skill plans (Phase 3)

### `/design (primitives)` — `design/primitives/primitives.md` (authored)

Ordered `/dev (primitives)` work-steps:
1. **Sever backend** — narrow `<Code,()>`→`<(),()>` at 5 `lib.rs` sites; delete
   `use cranelisp_backend::Code;` + the `cranelisp-backend` line/comment in
   `Cargo.toml`; rewrite the three `//!` sections (drop `Code::Primitive` lifecycle;
   dep-ban → bidirectional severance; note int `into_concrete` mount is S74).
2. **Builder + `code: None`** — replace both hand-rolled `ModuleEntry::Def {…}`
   literals with `ModuleEntry::def(scheme, DefKind::Primitive).param_names(..)
   .got_slot(slot).build()`. **Also drop the retired `DefKind::Primitive{primitive_kind,
   jit_name}` payload + `PrimitiveKind`/`JitSymbol` imports** — this is the crate's
   *own* compile error (independent of the backend dep). Builder defaults fix `seq: 0`,
   `code: None`.
3. **Layout dedup** — delete `vec.rs`'s private `LEN_OFFSET` + `string.rs`'s
   `VEC_LEN_OFFSET`/`VEC_DATA_PTR_OFFSET`; import `vec_runtime::{LEN_OFFSET,
   DATA_PTR_OFFSET}` (**no CAP** — string.rs doesn't use it); `HeapString` consts
   unchanged. Depends on Wave-1 `pub` promotion.
4. **Unit harness** — content (parity over `ring{0,1,3}_primitives()` + `vec-len`
   vs Appendix A.2/A.3/A.5) + behavioural (20 pure scalar rows via an `Invoke` enum);
   rewrite `every_entry_carries_code_primitive_marker` → `matches!(*kind,
   DefKind::Primitive)`. Heap ops excluded (allocator-coupled → e2e).
5. **Triage** — 0182 already gone (comment-only); **0212 premise corrected:
   `#[used]` is NOT present, must be ADDED** (only `#[unsafe(export_name)]` exists).
6. **Acceptance** — `cargo nextest -p cranelisp-primitives` green sans backend;
   clean `Cargo.toml`; zero local layout consts; regen `public-api.txt` (type narrowed).

### `/design (intrinsics)`

Confirmed: `vec_runtime::{LEN_OFFSET=16, CAP_OFFSET=24, DATA_PTR_OFFSET=32}` match the
facade names/values exactly; promotion `pub(crate)`→`pub` is **purely additive**
(helpers already read them); facade already carries the contract → no design-doc note.

### `/qa` — Phase 3 test plan

All regression risk **LOW** (the `<(),()>` table isn't mounted until S74; builder
migration + layout dedup are value-preserving). **No new e2e tests.** Replay-green
guard set: `tests/spec_appendix_a_builtins.rs` (named string/vec/scalar/`int-to-string`
rows) + `tests/{regression,spec_11_stdlib,stdlib_trait_impls}.rs`. `/qa` Phase-5 work:
rewrite 3 stale `tests/s68_primitives_uniform.rs` source-grep assertions to the S73
target (`<(),()>`, `code: None`, `matches!(kind, DefKind::Primitive)`); `#[ignore]`
the 2 backend-dependent rows (pending FIXME 0221/0191). Recommends a compile-time
`const _: () = assert!(vec_runtime::LEN_OFFSET == 16)` single-source guard in `/dev`'s
harness. No FIXME filed.

### FIXMEs (Phase 3)

- **0246** filed by `/design (primitives)` (facade documented the retired
  `DefKind::Primitive{primitive_kind, jit_name}` payload) → **resolved + deleted by
  `/arch`** (corrected to the committed unit variant across 6 docs; `PrimitiveKind`
  retired; jit-name = symbol-table key, inline-eligibility per-call-site in
  `ResolvedCall::BuiltinFn`).

## Waves (Phase 4)

Four sequential waves (the const-promotion gates the primitives dedup; one source
owner at a time per the no-concurrent-tests rule).

- **Wave 1 — `/dev (intrinsics)`**: promote `vec_runtime` layout consts
  `pub(crate)`→`pub`; add compile-time single-source asserts; regen
  `crates/cranelisp-intrinsics/public-api.txt`. Acceptance: `cargo nextest
  -p cranelisp-intrinsics` green; baseline delta = 3 added `pub const` lines.
- **Wave 2 — `/dev (primitives)`**: the 6-step refactor above (consumes Wave-1's
  `pub` consts). Acceptance: `cargo nextest -p cranelisp-primitives` green sans
  backend; clean `Cargo.toml`; zero local layout consts; `public-api.txt` regen.
- **Wave 3 — `/qa`**: rewrite the stale `s68_primitives_uniform.rs` assertions to
  the S73 target; replay the Appendix-A guard set green.
- **Wave 4 — `/review (intrinsics)` + `/review (primitives)`**: change-set review
  against the pinned facades + design doc. Gates close.

## Notes

- 2026-06-01: **Wave 1 complete** (/dev intrinsics). `vec_runtime::{LEN,CAP,DATA_PTR}_OFFSET`
  promoted `pub(crate)`→`pub` with blessed-ABI rustdoc + compile-time single-source
  asserts; `public-api.txt` regen = exactly +3 `pub const` lines. `cargo nextest
  -p cranelisp-intrinsics`: 75 pass / 1 pre-existing SIGABRT (`heap_string::tests::
  test_alloc_string_null_ptr` = **FIXME 0215**, null-deref in `heap_alloc_string`,
  filed S68, unrelated to Wave 1 — Wave 1 did not touch `heap_string.rs`). No
  warnings introduced. Not committed (sprint-in-progress).
- 2026-06-01: **Wave 1b complete** (/dev intrinsics — FIXME 0215, user-added). Validate-
  against-spec-first **reversed the FIXME's premise**: §12.1.2 + `heap_alloc_string`
  were already correct (impl guards `null || len==0`); the SIGABRT was a **test-side
  pointer-precedence bug** (`*(s as *const u8).add(16) as *const i64` read a byte then
  deref'd it as a ptr). Fixed the test (`.add(LEN_OFFSET).cast::<i64>()`, matching
  siblings); implementation untouched. `cargo nextest -p cranelisp-intrinsics`:
  **76 pass / 0 fail / 0 abort**. FIXME 0215 git-rm'd. **Carry**: clippy flags 3
  warnings in `vec_runtime.rs` (Wave-1 const-promotion casts) — /review (intrinsics)
  Wave 4 to confirm origin + clean per clean-your-own-crate.
- 2026-06-01: **Wave 2 complete** (/dev primitives). Backend severed (`Cargo.toml` deps
  = types/intrinsics/serde; `PRIMITIVES_TABLE: <(),()>`; public-api narrowed); builder
  + `code:None` (DefKind::Primitive unit variant; dropped retired payload — the crate's
  own compile blocker); layout deduped onto intrinsics' `pub` consts (no local consts;
  no CAP import); unit harness added (content parity ≥30 rows + behavioural 20 pure
  scalar ops; marker test → `matches!(kind, DefKind::Primitive)`). `cargo nextest
  -p cranelisp-primitives`: **71 pass / 0 skip**, builds independent of backend;
  check+clippy clean. **FIXME 0182 closed.** Carries: (1) **FIXME 0247 filed (/arch)** —
  `#[used]` not applicable to fns; 0212's DCE mechanism needs re-disposition (non-blocking;
  exe-bundle deferred); (2) `cranelift_op` dead-field `#[allow(dead_code)]` → /review
  Wave 4 remove-vs-keep; (3) `Scheme.vars`→`type_vars` rename handled in-place. Not committed.
- 2026-06-01: **Wave 3 complete** (/qa). `tests/s68_primitives_uniform.rs`: 2 assertions
  rewritten to S73 target (`PRIMITIVES_TABLE: <(),()>`; entries built via
  `ModuleEntry::def(.., DefKind::Primitive)` + negative "no `Code::Primitive`"), re-cited
  to FIXME 0244/Decision 0048; 2 backend-dependent assertions `#[ignore]`'d (reason
  "backend sprint — Code::Primitive deletion deferred; FIXME 0221/0191", bodies intact).
  **E2e guard replay BLOCKED-by-red-binary** (anticipated): all `tests/*.rs` link the root
  `cranelisp` binary → `cranelisp-backend` 42-error cascade, so Appendix-A suite +
  `s68_primitives_uniform` itself cannot RUN this sprint. Consistent with "workspace-green
  NOT in scope." **Runnable regression evidence = crate-narrow unit suites**: primitives
  71/71, intrinsics 76/76, both green independent of backend. Rewritten assertions
  validated by inspection; replay when backend clears (S74). No new e2e authored.
- 2026-06-01: **Wave 4 complete** (/review ×2). **/review (intrinsics): PASS-WITH-FINDINGS**
  (0 Blocker/Important; 1 Suggestion) — the 3 `vec_runtime` clippy warnings are
  **pre-existing** (cast helpers Wave 1 never touched; integer-const visibility change
  can't introduce a ptr-cast lint) → fold into deferred intrinsics audit; const
  names/values/asserts/baseline/0215-fix all verified. **/review (primitives):
  PASS-WITH-FINDINGS** (0 Blocker; **1 Important**; 2 Suggestion) — Important: remove
  `cranelift_op` dead field (zero readers outside operator.rs; only 3 self-referential
  tests; not serialized; Principle 7) rather than `#[allow(dead_code)]`; FIXME 0247
  handling confirmed correct (no broken `#[used]` in source); harness adequate.
  **Suggestion-3 (facade Static-init payload staleness) = MISREAD** — facade verified
  clean (0246 resolution stuck: `DefKind::Primitive` unit variant; `PrimitiveKind`/
  `JitSymbol` excluded). Change-set mergeable; 1 Important pending resolve/defer.
- 2026-06-01: **Wave 2b complete** (/dev primitives — Important finding resolved).
  `cranelift_op` dead field removed from `PrimitiveDef` (+33 construction sites +
  `#[allow(dead_code)]`); 1 self-referential test deleted, 2 tests kept live `.ty`
  asserts. `cargo nextest -p cranelisp-primitives`: **70 pass / 0 fail**; clippy/check
  clean; `public-api.txt` unchanged (field crate-private). Phase 5 complete.
- 2026-05-31: Sprint opened on user request "get primitives in shape — build a
  symbol table and pass it to int for CompilerSession construction." Initial scope
  (backend cascade → primitives → int mount) approved, then **re-scoped same day**:
  user directed "no backend changes this sprint (future sprint); just need
  primitives to not import that crate; do fix the bounded contexts for primitives."
- 2026-05-31: Severance mechanism grounded — `code: None` (FIXME 0244) removes
  primitives' only use of `Code`; `into_concrete` (`cranelisp-types`, the proven
  cache-restore bridge, preserves the shared `Arc<GotTable>`) concretizes at the
  int mount. Primitives reaches green independently of backend's 42-error cascade.
- Primitives-construction design (Phase 1, user-settled): builder adoption +
  option (c) — `code: None`, primitive-ness from `kind: DefKind::Primitive`.
  FIXME 0244 filed + ratified.
