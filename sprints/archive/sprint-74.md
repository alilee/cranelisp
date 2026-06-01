# Sprint 74: `cranelisp-intrinsics` alignment + intrinsics & primitives facade retirement (5th + 6th data points)

**Status**: COMPLETE — Phase 6 waived (no language-visible change); Phase 7 close user-approved 2026-06-01

**Goal**: Run `cranelisp-intrinsics` through the four-step alignment approach —
absorb input-crate changes (types S69, platform S71), conform the facade,
streamline the interior, and retire `facades/intrinsics.md` (5th data point). In
the same pass, complete the bilateral 0245 boundary by retiring the already-aligned
`facades/primitives.md` (6th data point, doc-only — primitives' source was aligned
in S73), leaving the whole primitives↔intrinsics layout-ABI boundary rustdoc-canonical.

## Why intrinsics (crate selection)

The sprint's selection rule: *a crate with no dependencies, or all of whose
dependencies have been conformed to their documented facades.* Applied to the
current DAG, `cranelisp-intrinsics` is the **only** remaining eligible crate:

| Crate | Cranelisp deps | All deps conformed? |
|---|---|---|
| **intrinsics** | types (retired S69), platform (retired S71) | **YES — eligible now** |
| primitives | types, **intrinsics** | no — blocked on intrinsics |
| backend | types, **intrinsics** | no — blocked on intrinsics |
| src/ (int) | everything | no — blocked downstream |

Conforming intrinsics is also the dependency-correct unblock: backend's alignment
(and then int's host-wiring) both wait on intrinsics being conformed first.
S73 named this work directly — *"Full intrinsics audit (extern-signature review,
inventory FIXME 0178, facade retirement) → future intrinsics sprint."*

`cranelisp-intrinsics` builds + tests green **standalone** today (`cargo build
-p cranelisp-intrinsics` clean; 76 unit-test fns) because it is upstream of the
backend cascade. So crate-narrow green is achievable this sprint independent of
the workspace's red state — the same shape as S72 (typecheck) and S73 (primitives).

## Scope — the four-step alignment

### 1. Absorb input-crate changes (`/dev intrinsics`)
Reconcile intrinsics' **consumed surface** against the now-retired facades of its
two dependencies, whose canonical surface is now source rustdoc:
- **`cranelisp-types`** (locked S69; baseline shrank ~80%) — confirm intrinsics'
  imports (`Symbol`, `ErrorLocation`, `Span`, `CranelispError`, marshaling tags
  `TAG_SNIL`/`TAG_SCONS`/`TAG_SEXP_*`, `SchedulingClass`, `heap::HeapHeader`) still
  resolve against types' narrowed pub surface; no stale references to S69-narrowed
  (`pub → pub(crate)`) items.
- **`cranelisp-platform`** (redesigned S71 — ABI_VERSION 2, schema.rs, adt.rs,
  `CLAdt`) — confirm the IO-trampoline path still consumes `IO_TAG_*` + `HostContext`
  correctly against platform's current rustdoc-canonical surface.

### 2. Conform the facade (`/arch` + `/design intrinsics`)
Resolve any drift between `facades/intrinsics.md` and source before folding it:
- **FIXME 0178** (/arch) — verify the §"Forbidden patterns" no-conditional-registration
  clause is complete; finalize the int-owned-intrinsics inventory note
  (`discover-tests`/`run-test`/`cranelisp_trace_format` physically live in `src/`,
  not this crate — inventory-and-rule doc action, no source move). Close + delete.
- **FIXME 0245** (/arch) — S73 left this "ready-to-close (both sides landed)"; verify
  the blessed-ABI consts + the primitives consumer pin are coherent, then delete.
- **FIXME 0247** (/arch) — `#[used]` is not applicable to `extern fn`. **Arch ruled
  Option 2 (Phase 2):** rely on `#[unsafe(export_name)]` + the existing exe-bundle
  force-link (`LazyLock::force(&PRIMITIVES_TABLE)` at `cranelisp-exe-bundle/src/lib.rs:75`)
  + the primitives `extern_shims()` address harvest — no redundant `#[used] static`
  anchor (minimum mechanism). Corrected wording folds into primitives' `//!` rustdoc;
  same Option-2 anchor noted in intrinsics rustdoc for symmetry. Delete on fold.

### 3. Streamline the interior (`/dev intrinsics`)
- `pub → pub(crate)` narrowings per Principles 13/18 for any pub item with no
  cross-crate consumer (types S69 did 14; intrinsics' surface is 215 baseline lines —
  expect a smaller set since most externs are genuinely backend-emitted-call targets).
- Clear the **3 pre-existing `vec_runtime` clippy warnings** (cast-helper idiom,
  S73 carry) and any other in-crate lints per clean-your-own-crate.
- Regenerate `crates/cranelisp-intrinsics/public-api.txt` under the standard
  `--omit blanket-impls,auto-derived-impls` convention (S72 baseline convention).

### 4. Absorb facades into rustdocs — retire `facades/intrinsics.md` + `facades/primitives.md` (`/design intrinsics` + `/design primitives` + `/arch`)
5th + 6th data points of the now-stable facade-retirement pattern (types §7 →
frontend §1 → platform §5 → typecheck §2):

**Intrinsics (5th DP):**
- Fold the contract into `crates/cranelisp-intrinsics/src/lib.rs` `//!` preamble +
  per-item `///` rustdoc (the canonical surface).
- Cross-surface narrative + the 10 bounded-context invariants → `bounded-contexts.md
  §4b`.
- `git rm design/arch/facades/intrinsics.md`.

**Primitives (6th DP — doc-only; source aligned S73):**
- Fold `facades/primitives.md` into `crates/cranelisp-primitives/src/lib.rs` `//!`
  preamble + per-item `///` rustdoc; cross-surface narrative + invariants →
  `bounded-contexts.md §4a`.
- The §"Consumed surface" 0245 contract folds as a `///`-documented Rust-consumer
  note on primitives' `vec.rs`/`string.rs` read sites, pointing at intrinsics'
  blessed-ABI const rustdoc (NOT at a facade) — this completes the bilateral
  boundary in one coherent sweep.
- `git rm design/arch/facades/primitives.md`.

**Both:** update `design/arch/CLAUDE.md` exception list (6 retired facades) + sweep
cross-references across canonical docs; verify 0 dangling refs to either retired file.

### Acceptance
- `cargo nextest run -p cranelisp-intrinsics` green — **independent of backend's red
  state**; clippy clean on the crate.
- `public-api.txt` regenerated under the standard convention; every baseline line
  named in source rustdoc (post-retirement, the rustdoc IS the contract); 0 orphans.
- Consumed surface reconciled with types + platform current rustdoc.
- `facades/intrinsics.md` **and** `facades/primitives.md` retired; the bilateral
  0245 boundary is rustdoc-canonical on both sides; cross-refs swept; exception list
  updated (6 retired facades); 0 dangling refs to either file.
- `cargo nextest run -p cranelisp-primitives` stays green (no source change — doc-only).

### Out of scope (deferred, with rationale)
- **All `cranelisp-backend` work** — the 42-error types cascade + backend facade
  retirement. Backend is the *next* eligible crate once intrinsics conforms; deferred
  to a future backend sprint. Includes FIXME 0221/0191.
- **int host-wiring** (FIXMEs 0242/0098/0187/0214) — depends on backend conforming
  first; S74-host-wiring as originally named slips behind this prerequisite.
- **Workspace-wide green** — stays blocked on backend + int (red).
- **Full extern-signature audit beyond 0178** — only the inventory + forbidden-pattern
  rule is in scope; a deeper signature-by-signature ABI review is a backend co-design.

## FIXME debt (Phase 1 triage)

| FIXME | Target | Status | Disposition this sprint |
|---|---|---|---|
| 0178 | /arch | open | **In scope** — inventory + forbidden-pattern clause; verify/complete/close. |
| 0245 | /arch | open (ready-to-close per S73) | **In scope** — both sides of the boundary now fold to rustdoc (intrinsics provider + primitives consumer); verify coherent; delete. |
| 0247 | /arch | open | **In scope** — `#[used]`/extern DCE re-disposition; folded into retirement. |
| 0214 | /int | open | **Defer (arch-confirmed)** — int's enumeration of the 8 intrinsics force-link re-exports is target /int; step-3 narrowing touches `pub fn`s *within* modules, not the `pub mod` paths, so 0214 is unaffected. Watch-item: step 3 must keep the 8 force-link module paths `pub mod`. Leave open. |
| 0247 | /arch | open | **In scope** — Option 2 ruling (above); delete on fold. |
| — (int-side mount drift) | /int | to file/fold | **Revision C** — primary primitives mount at `session_v4.rs:1064–1069` still comments the static as `<Code,()>` + bare `.clone()`; post-S73 it is `<(),()>` + `.into_concrete::<Code,()>()`. Fold the reconciliation into existing FIXME 0242 (already owns that call site, `:1072`) rather than a new FIXME. `/arch`/`/sprint` do not edit `src/`. |
| 0248 | /dev | **resolved + deleted** | `io_observer.rs:1` module rustdoc repointed off retired `facades/intrinsics.md` → crate-root `//!` + BC §4b; bonus stale `cranelisp-runtime::io` (retired S66) → `crate::io`. Grep confirms 0 facade refs remain in crate src. intrinsics 76/76 green; baseline unchanged. |
| 0221, 0191 | /dev backend | open | Out of scope — backend sprint. |
| 0242, 0098, 0187 | /int | open | Out of scope — blocked behind backend (0242 gains the Revision-C int-side reconciliation note). |

## Architecture review (Phase 2)

**Reviewer:** `/arch`. **Date:** 2026-06-01. **Verdict: APPROVE-WITH-REVISIONS** (4 revisions, all small; none re-opens the increment's shape).

### 1. Technical coherence of the four-step alignment + doc-only primitives retirement

Coherent and correctly bounded. The four-step alignment is the established pattern (types S69 / frontend S70 / platform S71 / typecheck S72 / primitives-source S73), applied to the one crate the selection rule admits. Crate selection is forced and correct: intrinsics depends only on `cranelisp-types` (retired S69) and `cranelisp-platform` (retired S71), both conformed; it builds + tests green standalone, upstream of the backend 42-error cascade. Workspace-green-out-of-scope is the right call and consistent with S72/S73.

One coherence correction the sprint text should absorb (does not change scope): **the intrinsics-side of FIXME 0245 already landed in S73, not "this sprint."** The three `vec_runtime` layout consts (`LEN_OFFSET=16`, `CAP_OFFSET=24`, `DATA_PTR_OFFSET=32`) are already on `crates/cranelisp-intrinsics/public-api.txt` (lines 124–126), committed at `ef69ede` (S73 close). The facade's §"Vec runtime" still describes them as "new pub items added by `/dev (intrinsics)` this sprint" and as a "Phase-5 co-deliverable" — that is stale-to-source. On retirement this stale prose must NOT be carried into rustdoc as a forward action; it folds as a *settled* statement ("`vec_runtime` exposes `LEN_OFFSET`/`CAP_OFFSET`/`DATA_PTR_OFFSET` as the blessed Vec layout-ABI; primitives is the named consumer"). This is **Revision A**. The practical effect: Step 1 (absorb input) + Step 2 (conform facade) for the 0245 surface is largely a *verification-and-fold*, not a source change — exactly what FIXME 0245's own §"Scope boundary" anticipated.

### 2. Public-API impact

- **Intrinsics baseline (`crates/cranelisp-intrinsics/public-api.txt`, 215 lines):** Step 3 `pub→pub(crate)` narrowings WILL change it; the retirement doc-fold will NOT. Whoever narrows regenerates in the same change-set per `design/arch/CLAUDE.md` §"Baseline-diff discipline" — that is **`/dev (intrinsics)`**, using `cargo public-api --omit blanket-impls,auto-derived-impls -p cranelisp-intrinsics > crates/cranelisp-intrinsics/public-api.txt`. Post-retirement the rustdoc IS the contract the baseline is checked against (rustdoc-coverage replaces the facade-compliance test, per the typecheck §2 "Per-surface documentation" template). `/arch`/`/design` do NOT regen — they author the rustdoc the baseline is named against.
- **Scope guard on step 3 (sizing):** the narrowable set is genuinely small. The baseline's 179 `pub` lines are dominated by the `IoEvent`/`IoEventTag` variant+field enumeration (one observation enum, ~45 lines) and the alloc/drop/rc/io Rust-callable families that have real cross-crate consumers (`int` reads `alloc_count`/`take_runtime_error`/`run_io_trampoline`; primitives reads `alloc_with_rc`/`consume_shallow`/`consume_sexp`/`consume_slist`/the layout consts; platform's `CLString::as_str` reaches `read_string_as_str`). The honest narrow candidates are the **root re-export duplicates** (13 root-level `pub fn` re-exports that shadow the per-module `pub fn`s, e.g. root `cranelisp_intrinsics::alloc_with_rc` vs `cranelisp_intrinsics::alloc::alloc_with_rc`) where a consumer reaches the per-module path — those root `pub use`s in `lib.rs:57–69` are candidates IF no consumer imports the root form. This is **Revision B**: step 3 must verify each consumer's import path (grep `int`/`primitives`/`platform` source) before narrowing any root re-export; "no in-crate use" is NOT sufficient justification when the item is a backend-emitted-call ABI symbol (see §6).
- **Primitives baseline (`crates/cranelisp-primitives/public-api.txt`, 9 lines):** MUST be zero-delta — the retirement is doc-only, source aligned S73. Confirmed: 9 lines (one `PRIMITIVES_TABLE` + seven `pub mod` + crate root). No regeneration; `cargo nextest run -p cranelisp-primitives` stays green. If the primitives baseline changes, that is a defect signalling an accidental source edit — flag and stop.

### 3. Interim-architecture risk (Principle 8) — ruling on the primitives §"Session-integration contract" fold

**RULING: the `into_concrete` mount is a LIVE, EXERCISED contract — fold it into rustdoc as asserted-live, NOT as forward-work.** The user's concern (folding an as-yet-unexercised contract ahead of FIXME 0242 host-wiring) does not hold against the source: the `<(),()>`→`<Code,()>` concretization of the primitives static is already wired and on the hot path in `src/session_v4.rs` — the cache-restore path calls `into_concrete::<Code, ()>()` explicitly (`session_v4.rs:1363`, `worker.rs:1917`), and the primary session mount inserts the `<Code,()>` primitives table into `session.symbol_tables` at `session_v4.rs:1064–1069`. `into_concrete` is defined and tested in `cranelisp-types` (`module.rs:470`). What FIXME 0242 (`register_builtins` → synthetic-module mount) defers is a *different* seam — the typecheck-side builtin-assembly retirement — not the primitives `into_concrete` bridge, which the cache-restore path has exercised since S73. So Principle 8 is satisfied: we are documenting a contract the code embodies, not asserting a future one.

**BUT one source-vs-doc coherence wrinkle (Revision C):** the *primary* mount at `session_v4.rs:1064–1069` currently does `(*PRIMITIVES_TABLE).as_ref().clone()` and the in-line comments describe the static as `SymbolTable<Code, ()>` — whereas post-S73 the static is `<(),()>` and the facade prescribes an explicit `.into_concrete::<Code, ()>()` at the mount. The cache-restore path concretizes explicitly; the primary mount's comment is stale to the S73 `<(),()>` shape. This is a real (small) drift between the facade's §"Session-integration contract" and `int` source. **Disposition:** the contract folds into primitives rustdoc AND BC §4a as the canonical statement (correct, matches `into_concrete` semantics); the stale `int`-side comment/call at the primary mount is **`int`'s** to reconcile — file FIXME `target: /int` (or fold into the existing FIXME 0242 host-wiring brief, which already owns `register_builtins` at this exact call site, `session_v4.rs:1072`). Do NOT edit `src/` (not `/arch`'s file). The rustdoc assertion is sound regardless of whether int's mount spells `.clone()` or `.clone().into_concrete()` — both produce the shared-`Arc<GotTable>` `<Code,()>` table; the explicit-`into_concrete` form is the one the facade blesses and is already proven on the cache-restore path.

### 4. FIXME dispositions

- **0178 (/arch — in scope, close+delete):** Correct. Substance lands at **two** manifestation sites on retirement: (a) the "no conditional registration" forbidden-pattern + the `JITBuilder::symbol`-intrinsics-only narrowing → intrinsics crate-root `//!` rustdoc (it is a maintainer-facing invariant of the surface) AND BC §4b invariant set; (b) the int-owned-intrinsics inventory note (`discover-tests`/`run-test`/`cranelisp_trace_format` physically in `src/`, registered unconditionally) is already documented in `src/CLAUDE.md` §"Int-owned JIT intrinsics" — the FIXME's doc action is satisfied there; the intrinsics rustdoc cross-references it. No source move (the three int-owned externs stay in `src/`). Verify the `src/CLAUDE.md` note still names all three before deleting the FIXME.
- **0245 (/arch — in scope, verify+delete):** Correct, and lighter than the sprint text implies (see Revision A — intrinsics side already landed S73). Substance lands as: blessed-ABI const rustdoc on `vec_runtime`/`HeapString` (intrinsics provider side) + a `///` consumer note on primitives' `vec.rs`/`string.rs` read sites pointing at the intrinsics const rustdoc (NOT at a facade) + BC §4a/§4b "what crosses the boundary" already carries the contract (verified present, BC §4a line 155, §4b line 195–196). Both sides fold to rustdoc → bilateral boundary is rustdoc-canonical. Verify coherence of the const values (16/24/32) against source, then delete.
- **0247 (/arch — in scope, re-dispose):** Correct to re-dispose now and fold into the retirement. `#[used]` on `extern fn` does not compile (rustc rejects; statics-only). **RULING: select Option 2 (rely on `#[unsafe(export_name)]` + the exe-bundle force-link via `LazyLock::force(&PRIMITIVES_TABLE)`).** Grounds: the `extern_shims()` harvest in primitives' `lib.rs` already takes every fn address at static-init (FIXME 0247 §"Why the symbols survive today anyway"), and `cranelisp-exe-bundle/src/lib.rs:75` already calls `LazyLock::force(&PRIMITIVES_TABLE)` at startup — that force IS the link anchor. Option 1 (a `#[used] static FORCE_LINK: [*const u8; N]`) is a redundant second anchor for the same fns; minimum-mechanism (Principle 2) prefers the existing harvest. **Manifestation site:** this is a *primitives*-facade DCE-wording fix, but primitives' facade is being retired in the SAME pass — so the corrected wording folds directly into primitives' `//!` rustdoc §(DCE/force-link) and the exe-bundle `///` on `cranelisp_init_primitives`. The intrinsics externs have the identical property (they are `pub extern` with `#[export_name]`/`#[no_mangle]`, kept alive by int's `JITBuilder::symbol` registration harvest) — note the same Option-2 anchor in intrinsics rustdoc for symmetry. Strike the `#[used]`-on-fn language wherever it appears (primitives facade line 24 / §"Removed from pub surface"; verify no copy leaked into intrinsics facade). Delete 0247.
- **0214 (target /int — DEFER, confirmed):** Defer to the int sprint. It is target `/int` (not `/arch`), concerns `facades/int.md` / `cranelisp-exe-bundle/public-api.txt` enumeration of the 8 intrinsics force-link re-exports, and the intrinsics surface change this sprint does not force it: the 8 re-exported submodule names (`alloc`/`drop`/`io`/`ivar`/`panic`/`rc`/`intrinsics_string`/`intrinsics_vec`) are int-side `pub use` aliases of intrinsics modules; step-3 narrowing touches `pub fn`/`pub(crate)` *within* those modules, not the module paths themselves, so the int re-export list is unaffected. **One watch-item for step 3:** if any root re-export an int force-link line depends on is narrowed (Revision B), that WOULD touch 0214's territory — so step 3 must confirm the 8 force-link module paths stay `pub mod` (they will; modules are not narrow candidates, only their fn members are). Note this non-impact in the FIXME-debt table; leave 0214 open for /int.

### 5. Bounded-context invariants — clean home on retirement

- **Intrinsics (10 invariants, facade §"Bounded-context invariants" 1–10):** BC §4b currently carries the *narrative* (in-scope/out-of-scope/what-crosses/evolution-driver/cross-crate-edges) but NOT the numbered invariant list. On retirement the 10 invariants must land in BC §4b as a "Bounded-context invariants" subsection, mirroring the platform §5 template (which has its 8 invariants inline) and typecheck §2 (invariants 1–10 inline). Verified none are facade-only-and-lost: invariants 1 (backend-emitted-call only), 2 (representation containment — now naming primitives as the one sanctioned cross-crate offset reader per 0245), 3 (atomic RC), 4 (strings opaque), 5 (embedded drop_glue_ptr), 6 (consuming convention), 7 (IO trampoline shallow dec), 8 (no state across sessions), 9 (backend-driven evolution + Decision 0048 dispatch asymmetry), 10 (no FQTypeName at surface) — all have a natural home in BC §4b. **Revision D:** the fold MUST carry all 10 (the platform/typecheck precedent moved the full numbered list; do not summarise-and-drop). The asymmetry-justification prose (facade §"Asymmetry justification" / Decision 0048) is load-bearing and folds into invariant 9's BC statement, not dropped.
- **Primitives (8 invariants, facade §"Bounded-context invariants" 1–8):** Same — BC §4a carries narrative but not the numbered list. Fold all 8 into a BC §4a "Bounded-context invariants" subsection. Verified clean homes: 1 (user-callable), 2 (symbol-table addressable), 3 (uniform dispatch + structural backend dep-ban), 4 (no trait knowledge), 5 (inline-substitution optional), 6 (process-static lifecycle + `code: None`), 7 (spec-driven evolution), 8 (consuming convention). The §"Session-integration contract" and §"Static-init contract" prose folds into primitives' crate-root `//!` rustdoc (it documents the one `pub static`), with the cross-surface mount narrative summarised in BC §4a per §3's ruling.

### 6. Scope adjustments + the CRITICAL backend-relocation sub-point

**CRITICAL — backend's string-name relocation dependency (explicit safe-to-narrow guidance):**

The danger is real and the guidance is binary. Backend names intrinsics externs **by string at codegen** (relocation-time, `Linkage::Import` against the linker symbol), NOT by Rust path. The linker symbol is created by the `#[export_name = "runtime/alloc"]` / `#[no_mangle]` attribute — and **that attribute emits the symbol into the object/staticlib independent of the fn's Rust visibility (`pub` vs `pub(crate)`).** A `pub(crate) extern "C" fn` with `#[export_name]` still produces the linker symbol. So Rust-visibility narrowing does NOT, by itself, remove the emitted-call ABI symbol.

**However** — `cargo-public-api` only *tracks* `pub` items. The 15 `pub extern` fns currently appear on the baseline by their Rust-path names (`heap_alloc`, `cranelisp_run_io`, `ivar_create`, …); their linker symbols (`runtime/alloc`, etc.) are the actual ABI. Narrowing them to `pub(crate)` removes them from the baseline (and from Rust-path reachability) WITHOUT removing the linker symbol — which is *safe for the emitted-call ABI* but loses the baseline's record of them. That trade is acceptable ONLY if the rustdoc explicitly documents each narrowed extern's linker symbol as the ABI contract (the baseline no longer guards it; the rustdoc must).

**Explicit guidance for step 3:**

- **SAFE to narrow to `pub(crate)`:** any `extern "C" fn` carrying `#[export_name]`/`#[no_mangle]` that has NO Rust-path consumer (no `int`/`primitives`/`platform` Rust call) — the linker symbol survives the narrowing; the emitted-call ABI is intact. Precondition: the fn's `#[export_name]` linker name is documented in the rustdoc as the blessed ABI contract (since it leaves the cargo-public-api baseline). Likely-safe: the externs only ever reached by emitted CLIF (`heap_alloc`, `heap_dealloc`, `vec_*` family, `ivar_*` family, `runtime/panic`) IF they have no Rust caller — VERIFY per fn.
- **MUST stay `pub` (do NOT narrow):** (a) any extern with a real Rust-path consumer — primitives Rust-calls `alloc_with_rc`/`consume_shallow`/`consume_sexp`/`consume_slist`/`runtime_panic` and reads `HeapString`/`vec_runtime` consts; platform reaches `read_string_as_str`; int reads stats + `run_io_trampoline` + `take_runtime_error` — these MUST stay `pub` (they are the §"Consumed surface" of FIXME 0245 + the int consumed surface, bound by baseline-diff with named consumers); (b) the layout-ABI consts (`HeapString::{LEN_OFFSET,DATA_OFFSET}`, `vec_runtime::{LEN_OFFSET,CAP_OFFSET,DATA_PTR_OFFSET}`) — blessed public ABI per 0245, named primitives consumer; (c) the IO observation types (`IoEvent`/`IoEventTag`/`IoObserver`/`register_io_observer`/`emit`/`trace_anchor`) — int registers the observer.
- **Net:** step 3's narrow set is SMALL and is dominated by the **root re-export duplicates** (Revision B), not the externs. Do not narrow any `#[export_name]` extern purely on "no Rust consumer" without (i) confirming no Rust consumer across all three downstreams and (ii) moving its linker-symbol-ABI documentation into rustdoc. When in doubt, keep `pub` — the cost of an over-exposed extern is one baseline line; the cost of an under-documented narrowed ABI symbol is a future reader who cannot find the contract. This is the inverse of the usual "narrow by default" because the emitted-call ABI is real and string-keyed.

**No split / resequence / descope needed.** The four steps are correctly ordered (absorb → conform → streamline → retire) and the primitives 6th-DP retirement rides the same pass coherently because primitives becomes eligible the moment intrinsics conforms. No missing deliverable. The 3 `vec_runtime` clippy warnings (cast-helper idiom, S73 carry) are correctly in step 3 under clean-your-own-crate.

### Enumerated revisions (APPROVE-WITH-REVISIONS)

- **Revision A** — Correct the stale "new pub items this sprint / Phase-5 co-deliverable" framing for the `vec_runtime` consts: they landed S73 (baseline lines 124–126, commit `ef69ede`). Fold into rustdoc as a *settled* blessed-ABI statement, not a forward action. Step 1+2 of the 0245 surface is verify-and-fold, not source-add.
- **Revision B** — Step 3 narrowing: verify each consumer's actual import path (`int`/`primitives`/`platform` source grep) before narrowing any root `pub use` re-export or any `#[export_name]` extern. The honest narrow candidates are root re-export duplicates whose consumers use the per-module path; "no in-crate use" is insufficient justification for an emitted-call ABI symbol.
- **Revision C** — The primitives §"Session-integration contract" folds into rustdoc/BC §4a as asserted-live (the `into_concrete` bridge is exercised on the cache-restore hot path today). The stale `int`-side primary-mount comment/call (`session_v4.rs:1064–1069` describing the static as `<Code,()>` and using bare `.clone()`) is int's to reconcile — file FIXME `target: /int` or fold into FIXME 0242's brief (same call site). `/arch` does not edit `src/`.
- **Revision D** — On retirement, fold the FULL numbered invariant lists (intrinsics 1–10 → BC §4b; primitives 1–8 → BC §4a) as a "Bounded-context invariants" subsection per the platform §5 / typecheck §2 template. Do not summarise-and-drop. Carry the Decision-0048 dispatch-asymmetry prose into intrinsics invariant 9. Update `design/arch/CLAUDE.md` exception-list line (line 15) to read six retired facades (add intrinsics §4b + primitives §4a) and sweep the 0-dangling-ref requirement across the canonical docs (the working/legacy docs that mention the files — `sprint-65-*`, `cranelisp-types-settled-verdict-s70.md`, `substance-scoping.md`, Decisions 0040/0048 — are historical/draining and may retain references; only the canonical set must be clean, plus add an archive-style "retired" note where a canonical doc points at the now-deleted file).

### Cascade note (manifestation sites, no separate Decision file)

All substance manifests at permanent-set sites: intrinsics rustdoc (`//!` + per-item `///`) + BC §4b for the cross-surface narrative/invariants; primitives rustdoc + BC §4a; `design/arch/CLAUDE.md` exception-list update. FIXMEs 0178/0245/0247 delete on fold (substance migrated to the named sites). No new Decision file (manifestation-site rule). Principle 8 honoured (§3 ruling). Principles 13/18 (narrow-by-default / structural enforcement) govern step 3, qualified by the emitted-call-ABI exception in §6. The principles review proper is Phase 7; nothing here surfaces a new principle — the emitted-call-ABI narrowing nuance is already implicit in Principle 14 (FFI layout discipline) + Principle 2 (minimum mechanism) and needs no new axiom.

## Skill plans (Phase 3)

Full source-grounded plans in the Phase-3 readout (transcript); per-crate design docs
refreshed (`design/intrinsics/` + `design/primitives/primitives.md §8`). Condensed below.

### /design (intrinsics) → /dev (intrinsics)

- **Step 1 — absorb input (no source change expected).** Verified imports are minimal +
  already correct: from types only `HeapHeader`, `NULLARY_TAG_THRESHOLD`, six `TAG_*`
  marshaling consts; from platform only `IO_TAG_{PURE,EFFECT,BIND,PAR}`. **Facade phantom
  imports** (`Symbol`/`ErrorLocation`/`Span`/`CranelispError`/`SchedulingClass`/`HostContext`
  — claimed in §"Consumed surface" but never imported in source) are dropped on fold, not
  carried into rustdoc. Effect dispatch is GOT-slot-mediated (Decision 26), not a Rust-path
  `HostContext` call.
- **Step 2 — facade-drift items** (substance lands in rustdoc + BC §4b; facade then deleted):
  D2-1 Revision-A stale "new pub items this sprint" → settled blessed-ABI statement;
  D2-2 FIXME 0178 (forbidden-pattern clause complete; int-owned trio documented in
  `src/CLAUDE.md §"Int-owned JIT intrinsics"` — verified all three named; no source move);
  D2-3 FIXME 0245 const coherence (16/24/32 + `HeapString` consts — verified); D2-4 FIXME
  0247 Option-2 wording; D2-5 phantom-import correction.
- **Step 3 — interior streamline (VERIFIED, Revision B).** Narrow set = **17 unused root
  `pub use` re-export duplicates** in `lib.rs:57–69` (backend + int + primitives all reach
  intrinsics by per-module path; these root forms have no consumer). **Keep in root re-export**
  (real root-form consumer found): `alloc_count`/`dealloc_count`/`bytes_current`/`alloc_with_rc`/
  `heap_alloc_payload`/`run_io_trampoline`/`trace_anchor`/`register_io_observer`. **Zero
  per-module narrowings** — every per-module `pub fn`/`pub extern`/`pub const` either has a
  Rust consumer or is fn-ptr-harvested by `backend/jit.rs:102–121` (Rust-path, not just
  linker symbol) → MUST stay `pub` (§6 guardrail). Plus the **3 `vec_runtime` clippy warnings**
  (`read_len`/`read_cap`/`read_data_ptr` + write trio, cast-helper idiom). Baseline regen
  (~17 fewer root-duplicate lines; per-module surface unchanged).
- **Step 4 — retire facade.** Full section→rustdoc mapping authored (every `public-api.txt`
  line gets a `//!` or per-item `///` home; 0 orphans). BC §4b gains the 10-invariant numbered
  list (Decision-0048 asymmetry → invariant 9) — **/arch's edit**. `git rm facades/intrinsics.md`.
- **Acceptance**: `cargo nextest -p cranelisp-intrinsics` green standalone (76); clippy clean;
  baseline regenerated; 0 rustdoc orphans.
- **FIXMEs**: target /arch (facade-drift + BC §4b fold + CLAUDE.md exception — handled in-sprint
  as the Wave-3 /arch brief, not a cross-sprint file); target /int (Revision-C mount drift →
  fold into existing 0242).

### /design (primitives) → /dev (primitives)

- **Doc-only fold** (source S73-aligned: `<(),()>`, no backend dep, 9-line baseline). Full
  facade-section→rustdoc mapping authored. Two substantive edits: (a) **0247/DCE wording**
  (Ruling 2) — strike all `#[used]`-on-fn language; settle to `#[export_name]` + exe-bundle
  `LazyLock::force` + `extern_shims()` harvest; (b) **Session-integration asserted-live**
  (Ruling 1) — strike "the mount itself is S74"; the `into_concrete` bridge is exercised today.
- **0245 consumer note** — repoint `vec.rs:16`/`string.rs:25` `///` at intrinsics' const
  rustdoc (NOT a facade); `string.rs` consumes `{LEN_OFFSET, DATA_PTR_OFFSET}` only (CAP is a
  dead import — flag). BC §4a gains the 8-invariant numbered list — **/arch's edit**.
- **Acceptance**: `cargo nextest -p cranelisp-primitives` green (70); **baseline byte-identical
  (9 lines) — any delta = accidental source edit, STOP**; 0 rustdoc orphans.
- **Flag**: `facades/backend.md:407` still says stale `code: Some(Code::Primitive)` (post-S73
  it is `code: None`) → backend-sprint cleanup, noted in sweep, NOT this sprint.
- **FIXMEs**: none new. FIXME 0246 (stale facade `DefKind::Primitive` payload) resolved by
  retirement → /arch `git rm`s alongside the facade.

### /qa

- **Risk LOW; thin surface; no new tests** (doc/hygiene; no new language behaviour). Two-tier
  strategy → e2e or in-crate unit, no middle tier; no defect to guard.
- **One real structural-test collision**: `tests/facade_compliance.rs` reads both `.md` with
  panic-on-missing → breaks on retirement. **Already latently broken since S70** (4 retired
  facades in `facade_pairs()`, masked by the red-binary e2e block). S74 → 6/7 retired. **/qa
  re-anchors** to the rustdoc-coverage model for all six retired crates (FIXME 0218 option (b)),
  re-anchors the `s68_facade_compliance_test_exists` sentinel, and **resolves+deletes FIXME 0218**
  (target /qa, `deferred_to: 72`, now overdue). The test is pure-`std::fs` — authorable
  independent of the red binary.
- **Runnable evidence (acceptance)**: crate-narrow `cargo nextest -p cranelisp-intrinsics` (76)
  + `-p cranelisp-primitives` (70). **e2e replay BLOCKED-by-red-binary** — stated, not a gap
  (identical to S72/S73; resumes when backend conforms).
- **FIXME**: advance + resolve 0218 (own FIXME; sequenced into Phase 5).

## Waves (Phase 4)

Sequential — the no-concurrent-tests rule serializes the two source-owning `/dev` fires;
`/arch` retirement gates on both rustdoc folds (so `git rm` lands when rustdoc is canonical);
`/qa` re-anchor gates on retirement; `/review` last. The "QA-first failing tests" Stage 1 is
**N/A this sprint** (no new behaviour → no new failing tests; /qa's Phase-5 work is the
`facade_compliance.rs` re-anchor).

### Wave 1 — `/dev (intrinsics)` source + interior + rustdoc fold

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-intrinsics | Steps 1–4: verify consumed-surface (no source change); clear 3 `vec_runtime` clippy warnings; narrow the 17 unused root re-exports (NO per-module narrowing); regen baseline. Then author the rustdoc fold (`//!` + per-item `///`) per /design's Step-4 mapping (corrected statements: settled 0245, Option-2 0247, dropped phantom imports). | **done** |

Acceptance: `cargo nextest -p cranelisp-intrinsics` green (76); clippy clean; baseline −~17 root-duplicate lines, per-module surface unchanged; 0 rustdoc orphans.

### Wave 2 — `/dev (primitives)` rustdoc fold (doc-only)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-primitives | 5 rustdoc-only steps: strike `#[used]` hedge + settle Option-2 DCE wording; reframe Session-integration asserted-live; spec-governed-inventory note; repoint 0245 consumer note (`vec.rs`/`string.rs`) at intrinsics' const rustdoc; verify rustdoc coverage. NO behaviour change. | **done** |

Acceptance: `cargo nextest -p cranelisp-primitives` green (70); **baseline byte-identical (9 lines)**; 0 rustdoc orphans.

### Wave 3 — `/arch` facade retirement + BC folds + FIXME drain

| Skill | Crate | Task | Status |
|---|---|---|---|
| /arch | — | `git rm facades/intrinsics.md` + `facades/primitives.md` + FIXME 0246; fold BC §4b (intrinsics 10 invariants; Decision-0048 asymmetry → inv 9) + BC §4a (primitives 8 invariants) + asserted-live mount narrative; `design/arch/CLAUDE.md` exception list → 6 retired facades; cross-ref sweep (0 dangling in canonical set; archive-style "retired" pointers where canonical docs cite the deleted files); verify+delete FIXMEs 0178/0245/0247. | **done** |

Acceptance: both facades retired; BC §4a/§4b carry full numbered invariant lists; 0 dangling canonical refs; FIXMEs 0178/0245/0246/0247 deleted.

### Wave 4 — `/qa` structural-test re-anchor

| Skill | Crate | Task | Status |
|---|---|---|---|
| /qa | tests/ | Re-anchor `tests/facade_compliance.rs` to the rustdoc-coverage model for all six retired crates; re-anchor the `s68_facade_compliance_test_exists` sentinel; resolve+delete FIXME 0218. | **done** |

Acceptance: `facade_compliance.rs` compiles + retained slices pass standalone (pure-`std::fs`); FIXME 0218 deleted.

### Wave 5 — `/review (intrinsics)` + `/review (primitives)`

| Skill | Crate | Task | Status |
|---|---|---|---|
| /review | cranelisp-intrinsics | Change-set review against /design plan + Phase-2 rulings (esp. §6 ABI guardrail: confirm zero per-module extern narrowed; baseline diff = root-duplicates only). | **done — PASS-WITH-FINDINGS** |
| /review | cranelisp-primitives | Change-set review: confirm doc-only (baseline byte-identical); 0245 consumer note + 0247 wording correct. | **done — PASS** |

Gates close on PASS (or Blocker/Important resolved-or-deferred).

## Notes

- 2026-06-01: Phase 1 scope drafted. Crate selection forced by the rule (intrinsics
  is the only remaining crate with all deps conformed). Four-step alignment maps to
  the established pattern (types S69 / frontend S70 / platform S71 / typecheck S72 /
  primitives S73-aligned).
- 2026-06-01: User approved scope. Decision on the user's open question — **also retire
  `facades/primitives.md`** (6th DP, doc-only) to close the bilateral 0245 boundary in
  one pass, since primitives' source was already aligned in S73 and it becomes eligible
  by sprint-end (intrinsics conforms this sprint). Advanced to Phase 2 (/arch review).
- 2026-06-01: Phase 2 APPROVE-WITH-REVISIONS (4 revisions + 2 rulings, user-approved).
  Phase 3 plans collated (3 skills). Phase 4 waves organized (5 sequential).
- 2026-06-01: **Wave 1 done** (/dev intrinsics). 3 clippy warnings cleared (real ones were
  `fn_to_numeric_cast` in test code, not the cast-helper idiom — plan idiom also applied
  defensively); 17 unused root re-exports narrowed (zero per-module narrowing — §6 honoured);
  rustdoc fold authored (`//!` + per-item `///`, corrected statements). **public-api.txt
  215 → 139 (−76, 0 additions)** — larger than the "~17" estimate because the `IoEvent`/
  `IoEventTag` root re-exports expanded to ~60 baseline lines; per-module `io_observer::IoEvent`
  enumeration intact; all 8 KEEP root lines retained. **intrinsics 76/76 green; clippy clean;
  rustdoc 0 warnings.** Two benign /design-plan discrepancies reconciled: clippy-warning shape;
  consumed surface includes a real `cranelisp_platform::call_effect_thunk` Rust-path call
  (`io.rs:192`) the brief's "only" list omitted (`SchedulingClass` is doc-comment-only, not an
  import) — stated correctly in rustdoc. Not committed (working tree).
- 2026-06-01: **Wave 2 done** (/dev primitives, doc-only). 0247 wording settled to Option-2
  (struck `#[used]`-on-fn + "pending" hedge; remaining `#[used]` mentions are the settled
  "no `#[used] static`" prose); Session-integration reframed asserted-live (Ruling 1); 0245
  consumer note repointed (`vec.rs`/`string.rs`) at intrinsics' const rustdoc; spec-governed-
  inventory note added. Agent proactively repointed 4 submodule rustdoc refs + 2 lib.rs body
  comments off `facades/primitives.md` → **zero `facades/primitives.md` refs remain in the
  crate** (pre-empts dangling refs when /arch git-rm's it in Wave 3). **primitives 70/70 green;
  `public-api.txt` BYTE-IDENTICAL; `cargo doc` clean (0 orphans); clippy clean.** 7 files,
  doc-comment-only. Not committed.
- 2026-06-01: **Wave 3 done** (/arch retirement). Verified both crates' rustdoc carries the
  full facade substance BEFORE deletion. BC §4b gains intrinsics invariants 1–10 (Decision-0048
  asymmetry → inv 9; inv 2 names primitives as the sanctioned offset reader); BC §4a gains
  primitives invariants 1–8 + asserted-live `into_concrete` mount narrative (Ruling 1).
  `git rm`'d: `facades/intrinsics.md`, `facades/primitives.md`, FIXMEs 0178/0245/0247.
  `design/arch/CLAUDE.md` exception list → **6 retired facades**. Cross-ref sweep repointed
  `facades/backend.md` (4), CLAUDE.md, `sequences/exec-flow-runtime.mmd` (2) → **0 dangling
  canonical refs**. **Two carries**: (1) **FIXME 0246 does not exist** in the store (the /design
  primitives plan assumed it; nothing to remove — harmless); (2) **FIXME 0248 filed (/dev)** —
  `io_observer.rs:1` module rustdoc still cites the retired facade (Wave-1 miss; substance is in
  rustdoc+BC); resolve Wave 5. **SVG carry**: `sequences/exec-flow-runtime.svg` embeds one stale
  string; `.mmd` source corrected but `mmdc` headless render is sandbox-network-blocked — regen
  when a renderer is reachable (derivative artefact; non-blocking, consistent with prior-sprint
  Chrome-render limitations). Not committed.
- 2026-06-01: **FIXME 0248 resolved immediately** (user direction — fix now, don't carry).
  `/dev (intrinsics)` repointed `io_observer.rs:1` off the retired facade → crate-root `//!` +
  BC §4b; also caught + fixed a bonus stale `cranelisp-runtime::io` forward-ref (that crate
  retired S66) → `crate::io`. Crate-wide grep: 0 `facades/{intrinsics,primitives}.md` refs remain.
  intrinsics 76/76 green; clippy/doc clean; `public-api.txt` unchanged. FIXME 0248 deleted.
- 2026-06-01: **Wave 4 done** (/qa re-anchor). `tests/facade_compliance.rs` split into two checks:
  facade-text compliance retained for the binding facade(s) (`backend` + `backend-cache`; `int.md`
  has no baseline, covered by separate `int_facade_*` tests); new `rustdoc_coverage_for_retired_crates`
  asserts (from source, pure-`std::fs`) for all **six** retired crates that `public-api.txt` is
  non-empty + crate-root `//!` present + per-item `///` present (FIXME 0218 option (b),
  manifestation-site model). **No prior precedent existed** — the types/frontend/platform/typecheck
  slices were still `.md`-reading + equally (latently) broken; uniform fix applied to all six (so
  S74 also retro-fixes the S69–S72 latent breakage). Honest scope: presence-at-migration-sites, not
  per-line coverage (a text check can't map each baseline leaf to its `///`; documented in header).
  `s68_facade_compliance_test_exists` sentinel re-anchored to assert each crate is on the path
  matching its facade status. **BLOCKED-by-red-binary** for live run (tests/ links the red root
  binary — 41 backend errors, expected, same as S72/S73); validated by shell dry-run (all 6 retired
  crates pass: e.g. types 140 `//!`/2021 `///`, primitives 96/222) + `spec_link_check.py` clean.
  FIXME 0218 `git rm`'d. Also touched `tests/plan/PLAN.md` (plan rows, /qa-owned). Not committed.
- 2026-06-01: **Wave 4 revised** (user correction). The `rustdoc_coverage_for_retired_crates`
  test was over-built — asserting `//!`/`///` presence restates the code. **Principle (user):**
  once a facade is retired, the crate's surface is DEFINED by source — `public-api.txt` baseline
  + the compiler ARE the definition + guard; rustdoc is rationale, not a contract to re-verify.
  A retired crate therefore has **nothing to check** in a compliance test → it drops OUT, not
  replaced by a self-documentation check. `/qa` deleted the rustdoc-coverage test + its helpers;
  `facade_compliance.rs` now checks ONLY crates with a binding facade (`backend` + `backend-cache`;
  `int.md` via separate `int_facade_*`/`facade_pif_rows` tests). `s68` sentinel narrowed to
  positive+negative guard (backend present; primitives/intrinsics MUST be absent — locks in
  retirement). Header rewritten with the principle + retirement-sprint ledger. **Finding for
  Phase 7**: facade retirement = drop the crate from compliance testing; don't substitute a
  rustdoc-restating check.
- 2026-06-01: **Wave 5 done** (/review ×2). **/review (primitives): PASS** (0 findings — diff
  doc-only, `public-api.txt` byte-identical, Rulings 1+2 + 0245 faithful). **/review (intrinsics):
  PASS-WITH-FINDINGS** — **§6 ABI guardrail CONFIRMED CLEAN** (zero per-module narrowing; baseline
  215→139 root-duplicates only, every removed line's per-module twin retained; backend fn-ptr
  harvest `jit.rs:102–121` intact; all 8 KEEP re-exports retained with verified consumers; all 17
  removed verified zero root-form consumers). 1 **Important** (stale `emit` `///` at
  `io_observer.rs:159–161` — 0248-class miss) **resolved immediately** per user "fix now" direction
  (/dev repointed to `crate::io` in-crate trampoline; 76/76 green; baseline unchanged). 1
  **Suggestion** deferred (vec_runtime layout consts are literals not `offset_of!`-derived like
  `heap_string`; pre-existing S73, guarded by `const _: assert!`; opportunistic future alignment).
- 2026-06-01: **Phase 5 COMPLETE.** Acceptance met: intrinsics **76/76** green standalone +
  `public-api.txt` 215→139 (root-duplicates only); primitives **70/70** green + baseline
  byte-identical; both clippy + `cargo doc` clean; both facades retired (6 total); 0 dangling
  canonical refs; FIXMEs 0178/0245/0247/0218/0248 resolved+deleted. Workspace-wide green NOT in
  scope (backend + int stay red). All /review Blocker+Important resolved.

## Outcome (Phase 7 — DRAFT, pending user close approval)

S74 brought **`cranelisp-intrinsics`** to a sound, facade-aligned, self-documenting shape via the
four-step alignment, and **retired both `facades/intrinsics.md` (5th DP) and `facades/primitives.md`
(6th DP)** — closing the bilateral FIXME-0245 heap-layout-ABI boundary rustdoc-canonical on both
sides. Crate-narrow green independent of the backend red cascade (same shape as S72/S73).

### Delivered
- **Intrinsics interior + rustdoc** — 3 clippy warnings cleared; 17 unused root `pub use` re-export
  duplicates narrowed (zero per-module narrowing — §6 ABI guardrail held; backend's per-module
  fn-ptr harvest + `#[export_name]` emitted-call ABI intact); `public-api.txt` 215→139; full
  facade→rustdoc fold (`//!` + per-item `///`) with **corrected** content (dropped 5 phantom
  imports the facade falsely claimed; added the real `cranelisp_platform::call_effect_thunk`
  import; settled-0245 blessed-ABI wording; Option-2 0247 DCE wording). 76/76 green.
- **Primitives facade retirement (doc-only)** — source was S73-aligned; rustdoc fold settled the
  0247 DCE wording (Option 2 — no `#[used]`-on-fn) and reframed the `into_concrete` mount as
  asserted-live (exercised on the cache-restore hot path today); 0245 consumer notes repointed at
  intrinsics' const rustdoc. `public-api.txt` byte-identical; 70/70 green.
- **Facade retirements (5th + 6th DP)** — `facades/intrinsics.md` + `facades/primitives.md` `git
  rm`'d; BC §4b gains intrinsics invariants 1–10 (Decision-0048 asymmetry → inv 9); BC §4a gains
  primitives invariants 1–8 + asserted-live mount; `design/arch/CLAUDE.md` exception list → 6
  retired facades; cross-ref sweep 0 dangling canonical.
- **Test re-anchor** — `tests/facade_compliance.rs` corrected: retired crates DROP OUT of compliance
  testing (source = definition, baseline + compiler = guard, rustdoc = rationale — NOT a
  self-documentation check); only binding-facade crates remain. Also retro-fixes the
  latently-broken-since-S70 types/frontend/platform/typecheck slices. `s68` sentinel narrowed to a
  positive+negative retirement guard.
- **FIXMEs resolved+deleted** — 0178, 0245, 0247 (substance migrated to rustdoc + BC), 0218
  (compliance re-anchor, overdue from S69), 0248 (filed+resolved in-sprint).

### Deferred (with rationale)
- **All `cranelisp-backend` work** (42-error types cascade + backend facade retirement) → backend
  is the NEXT eligible crate now that intrinsics conforms; future backend sprint. Includes
  `facades/backend.md:407` stale `code: Some(Code::Primitive)` (post-S73 it is `code: None`).
- **int host-wiring** (FIXMEs 0242/0098/0187/0214) — blocked behind backend; 0242 carries the
  Revision-C int-side mount-comment reconciliation (`session_v4.rs:1064–69` still `<Code,()>`/`.clone()`).
- **Suggestion** — vec_runtime literals → `offset_of!` alignment (opportunistic; future intrinsics audit).
- **Workspace-wide green** — backend + int stay red.

### Findings / lessons
- **Facade retirement removes the crate from compliance testing** (user correction, Wave 4): once
  source is canonical, the baseline + compiler ARE the definition and rustdoc is rationale — a
  retired crate has nothing to "comply" with; don't substitute a rustdoc-restating check. Corrects
  the over-built first re-anchor AND the latent S69–S72 handling.
- **The facade was wrong in ways only a source walk caught** — 5 phantom imports + 1 missing real
  import (`call_effect_thunk`); the rustdoc fold is strictly more accurate than the doc it replaced.
- **§6 emitted-call-ABI guardrail inverts narrow-by-default** — `#[export_name]` survives `pub(crate)`
  but `cargo-public-api` only tracks `pub`; backend's per-module fn-ptr harvest is a real Rust-path
  dep. Net: honest narrow set was tiny (17 root duplicates), not the externs.
- **Fix-don't-carry** (user direction) — 0248 + the Wave-5 Important `emit` finding both resolved
  in-sprint rather than carried, keeping the retirement debt-free.
- **"Sandbox-blocked" was a misdiagnosis** (user "try the svg regen") — the `exec-flow-runtime.svg`
  regen Wave-3 carry blamed a sandbox network block; the real fault was a **semicolon** in the line-8
  `Note` text (mermaid treats `;` as a statement separator → parse error). The render environment
  (mmdc 11.15.0) works fine. Fixed (`;`→`,`) + SVG regenerated (carries "retired S74"). Lesson:
  verify the actual failure before recording an environmental blocker.

### SVG regen (resolved, not deferred)
`design/arch/sequences/exec-flow-runtime.{mmd,svg}` corrected + regenerated — the Wave-3 "sandbox-blocked"
carry was a misdiagnosis (semicolon-in-Note parse error). SVG now consistent with the retired-facade homes.

### Acceptance
- `cargo nextest run -p cranelisp-intrinsics`: **76 / 76**. `cargo nextest run -p cranelisp-primitives`:
  **70 / 70**. Both clippy + `cargo doc` clean. intrinsics baseline 215→139 (root-duplicates only);
  primitives baseline byte-identical. Both facades retired; 0 dangling canonical refs. Workspace-wide
  green explicitly NOT in scope.
