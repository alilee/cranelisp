# Sprint 75 — `/qa` test plan (Phase 3 Design)

Owner: `/qa`. Subordinate to `PLAN.md`. Folds back into `PLAN.md` /
`facade_compliance.rs` header on close.

**Sprint shape**: `cranelisp-backend` four-step alignment (absorb →
conform-boundary → conform-surface → streamline → retire) + the 7th + 8th
facade retirements (`backend.md` + `backend-cache.md`). Conform/cascade/
retirement sprint. **Backend goes to FINAL state; int stays red, re-wired
S77.** Acceptance is **crate-narrow green** (`cargo nextest run -p
cranelisp-backend`), NOT workspace-wide green.

This document is authored independent of running tests (per the sprint
rules: `/qa` does not run `cargo nextest` this phase). All dispositions are
validated against source/spec/SPRINT.md by reading.

---

## 1. Risk assessment — is any NEW language-visible behaviour introduced?

**Verdict: NO new e2e test needed. This is purely conform/cascade +
retirement; the e2e guard set is regression-replay only.**

The behaviour-adjacent items in the sprint are exactly two, and both are
re-shapings of EXISTING language behaviour, not new surface:

1. **`Expr::ConstrADT` lowering (`compile_constr_adt`)** — Step 1/W1 absorb +
   W4 streamline. This is the constructor-as-Def collapse (D47 + Decision
   44/45 ctor shape) landing in backend: it *replaces* the four-function
   ctor family (`compile_data_constructor_call`,
   `compile_data_constructor_as_value`, `nullary_constructor_tag`,
   `data_constructor_info`) with a single handler that lowers to the SAME
   emission target (alloc + tag + field stores). The observable language
   behaviour — `(Some 7)`, `(deftype ...)` construction + `match` — is
   **unchanged**. It is already exhaustively covered e2e:
   - `tests/spec_03_types.rs` — ADT construction / deftype surface
   - `tests/spec_06_pattern_matching.rs` — match on constructors
   - `tests/build_confidence.rs::mode_equiv_adt_option_match` /
     `::mode_equiv_pattern_match_nested` — construction+match across all
     modes (currently in the 0122 cluster, see §4)

   Validated against `facades/backend.md` §"Constructor codegen" (lines
   536–544, per the Phase-2 Q2 finding): the emission target is documented;
   the collapse changes the Rust call structure, not the runtime shape.
   `/dev (backend)` owns the in-crate behaviour test for `compile_constr_adt`
   (unit, inside the crate). **No new e2e row.**

2. **D41 boundary rotation** (`compile_to_module` →
   `Result<CompilationArtifacts, CompilationError>`; `produce_disasm`
   on-demand; `Code` variant-payload slim; `Code::Primitive` deletion;
   `Linker::get_symbol → Result`; `compile_to_object` DELETE). All of these
   are **internal Rust API / boundary signature** changes. None changes what
   the binary emits or how the language behaves. The single observable
   contract is *mode equivalence* (REPL / `--run` / `--link` converge on the
   same Int), which is already the job of `build_confidence.rs`'s
   `mode_equiv_*` set + `run_through_all_modes`.

**No new e2e test is owed by this sprint.** A conform/cascade/retirement
sprint changes the crate's internal shape + boundary + visibility; the
language surface is invariant. The acceptance evidence is (a) the
crate-narrow `cargo nextest run -p cranelisp-backend` (owned by `/dev
(backend)` — unit tests, incl. the `compile_constr_adt` behaviour test), and
(b) the e2e regression-replay set (§3) once int conforms (S77).

**Validate-against-source-first applied**: the Step-1 table's "new
`ResolvedCall` variant" wording is imprecise (Phase-2 Rev 1) — `ResolvedCall`
has exactly four variants, all already matched in `compiler/apply.rs`; the
E0004 is a payload-reshape non-exhaustiveness, not a new emission path. No
e2e implication either way (binding-level absorb work).

---

## 2. W5 `facade_compliance.rs` re-anchor — the main `/qa` deliverable

**Context.** After S74 retired six facades, `backend.md` + `backend-cache.md`
are the **only binding facades left** in `tests/facade_compliance.rs`. On
their retirement this sprint (W5 Step 4), they DROP OUT — mirroring exactly
how `primitives.md` + `intrinsics.md` dropped out in S74 W3/W4. Per the S74
correction: retired crates are **NOT** replaced by a rustdoc-restating
self-documentation check; they leave the compliance set entirely (source =
definition; baseline + compiler = guard; rustdoc = rationale).

This lands in **W5**, gated on the W5 retirement fold (`/design backend` +
`/arch` fold both facades → rustdoc + BC §3 and `git rm` both `.md` files).
`facade_compliance.rs` is pure `std::fs` — it reads files off disk and greps
strings — so it is **authorable and validatable independent of the red root
binary** (the binary won't link until int conforms in S77, but this test's
*logic* needs no binary). The runtime gate is still BLOCKED-by-red-binary
(it links the root crate to compile as an integration target), but the edit
is correct-by-inspection.

### 2a. `facade_compliance.rs` — assertions/helpers that change (W5)

The file becomes a no-op once backend is the last binding facade and it too
retires. Concretely:

| Element | Current (post-S74) | W5 change |
|---|---|---|
| `facade_pairs()` (lines 111–124) | returns one entry: `("cranelisp-backend", "cranelisp-backend", vec!["backend.md", "backend-cache.md"])` | **Remove the backend entry.** `facade_pairs()` returns an EMPTY `vec![]` — there are no binding facades left. |
| Header comment block (lines 1–92) | "the only crate exercised … is `cranelisp-backend`"; lists six retired crates | Add `backend` + `backend-cache` to the retired list (now EIGHT retired); state plainly that NO crate has a binding facade `.md`, so this file's grep check covers nothing. `int.md` note stays (binary crate, no `public-api.txt`, covered by `facade_pif_rows.rs`). |
| `facade_compliance_orphans_match_expected_sprint_67_baseline()` (lines 288–368) | iterates `facade_pairs()`, greps each baseline against the facade corpus, asserts `total_orphans == 0` | With an empty `facade_pairs()` the loop body never runs → `total_orphans == 0` trivially. **Two acceptable shapes** (the `/dev (backend)` reviewer + `/arch` pick at W5; `/qa` recommends option B):<br>**(A)** leave the test as-is — it passes vacuously (the loop is empty), and the file documents WHY in the header.<br>**(B) RECOMMENDED**: delete the now-vacuous grep test body and the helpers it solely supported (`extract_names`, `name_blacklist`, the panic-message builder), keeping the file as a documented tombstone: a header explaining all eight facades retired + the `s68` sentinel relocation note. A vacuously-passing test is a maintenance trap (a future reader re-adds a crate and it silently does nothing); an explicit tombstone + the sentinel guard (§2b) is the durable record. |
| `extract_names`, `name_blacklist`, `workspace_root`, `HashSet`/`PathBuf` imports | live (used by the grep test) | Under option B, `extract_names` + `name_blacklist` are dead → remove (or `#[allow(dead_code)]` + keep for provenance — `/qa` prefers removal; git history is the record per the S74 "rustdoc-restating is not a check" lesson). `workspace_root` may survive only if the sentinel-style assertions move here. |

**`/qa` recommendation: option B.** It mirrors the S74 *spirit* (retired
crates leave the check; nothing is restated) and avoids a vacuously-green
test. The final `facade_compliance.rs` is a tombstone documenting that ALL
EIGHT facades retired and pointing at the `s68` sentinel + `public-api.txt`
baselines + `bounded-contexts.md §3` as the durable guards.

### 2b. `s68_facade_compliance_test_exists` sentinel flip (W5)

`tests/s68_primitives_uniform.rs::s68_facade_compliance_test_exists_for_s68_touched_crates`
(lines 176–214) is the meta-sentinel. Post-S74 it asserts:
- backend **MUST appear** in `facade_pairs()` (the one still-binding facade), AND
- primitives + intrinsics **MUST NOT appear** (retired → absent).

**W5 flip — mirror exactly how primitives/intrinsics flipped in S74.**
backend + backend-cache must become **MUST-BE-ABSENT**, joining
primitives/intrinsics. Concretely the sentinel changes from a present+absent
guard to an all-absent guard:

| Assertion | Current | W5 |
|---|---|---|
| `pairs_block.contains("cranelisp-backend")` (positive, lines 192–197) | **MUST be present** | **REMOVE** the positive assertion. backend's facade is retired; it must no longer be required present. |
| `for name in ["cranelisp-primitives", "cranelisp-intrinsics"]` absent-loop (lines 204–213) | asserts these two absent | **EXTEND** the array to `["cranelisp-primitives", "cranelisp-intrinsics", "cranelisp-backend"]` — assert all three (the two S74 retirees + the S75 retiree) are absent from `facade_pairs()`. (`backend-cache` is not a separate crate dir — it was a sub-facade of the `cranelisp-backend` entry — so absence of `cranelisp-backend` covers both.) |

If option B (§2a) deletes `facade_pairs()` entirely, the sentinel's
`split_once("fn facade_pairs()")` lookup must adapt: either the sentinel
asserts the function is **gone** (string `fn facade_pairs()` absent from the
file) OR — if `facade_pairs()` is kept as an empty-returning tombstone — the
absent-loop still works (an empty `vec![]` contains none of the three names).
**`/qa` recommendation: keep an empty `facade_pairs() -> vec![]` so the
sentinel's grep anchor survives, and the sentinel asserts all three crates
absent.** This is the minimal, lowest-risk flip; it preserves the S74
sentinel mechanism verbatim (present-must-be-absent), just with backend added
to the absent set and the backend positive assertion removed.

The sentinel comment block (lines 141–174) is rewritten to state: of the
S68-touched crates, **none** retains a binding facade as of S75 W5 (backend
retired this sprint); all of primitives/intrinsics/backend are source-defined
and intentionally absent from `facade_compliance.rs`.

**This sentinel is itself BLOCKED-by-red-binary at runtime** (it links the
root crate as an integration target), same as `facade_compliance.rs` —
validated by inspection at W5, runs green once int conforms (S77). It is
pure `std::fs` (`read_source` reads the file off disk), so the *logic* is
binary-independent.

### 2c. `facade_pif_rows.rs` (int facade) — UNCHANGED

`int.md` remains binding (int conforms in S77, the last crate). The
`int_facade_*` / `facade_pif_rows.rs` tests stay as-is this sprint. Only
backend + backend-cache retire in S75.

### 2d. Spec annotation

The `PLAN.md` row #6 meta-sentinel annotation upgrades on close to record the
S75 W5 flip (all eight facades retired; sentinel asserts backend absent).

---

## 3. Regression-replay guard set + the red-binary reality

**STATEMENT (plain): e2e replay is BLOCKED-by-red-binary this sprint.** This
is the SAME posture as S72/S73/S74 — it is **NOT a coverage gap**. All
`tests/*.rs` integration/e2e targets link the root `cranelisp` binary. That
binary does not build until W1 makes backend compile, and the workspace
**stays red on int** for the whole sprint (int is fixed in S77). Therefore
`cargo nextest run` workspace-wide cannot execute the e2e suite this sprint.

**The runnable evidence this sprint is the crate-narrow
`cargo nextest run -p cranelisp-backend`** (backend builds + its own unit
tests pass standalone), owned by `/dev (backend)`. That is the S75 acceptance
bar per SPRINT.md §Acceptance.

**Named e2e regression-replay guard set** (for the record — these SHOULD
replay green once int conforms in S77; they are the behavioural safety net
that the boundary rotation + ctor collapse did not change observable
semantics):

| Guard | What it protects |
|---|---|
| `tests/build_confidence.rs::mode_equiv_*` (the full B.2 class set) | REPL/`--run`/`--link` mode equivalence — directly exercises the rotated `compile_to_module`/`Code`/codegen path across all modes. The 4 currently-failing `mode_equiv_*` (`adt_option_match`, `pattern_match_nested`, `macro_user_defined`, `io_pure_primitive`) are the 0122 cluster — see §4. |
| `tests/build_confidence.rs::smoke_*` (binary builds/starts/runs; `smoke_link_then_run_executable_matches_run_exit`) | Release gate — binary builds, starts, executes `--run` + `--link`. Directly downstream of the codegen-entry rotation (`compile_to_module<ObjectModule>` + caller `finish().emit()`, `load_object`, `produce_disasm`). |
| `tests/cache.rs` (cache-hit/miss equivalence, multi-module + transitive deps + prelude caching, mtime-preservation, round-trip parity) | The `backend-cache` retirement target — exercises `try_load_cached_module` / `load_cached_object` / `CacheManifest` / `Linker` mmap behaviour through the binary. Guards that the cache contract (kept `pub`) and `load_object` (kept `pub`) behave unchanged across the conform. |
| `tests/spec_03_types.rs`, `tests/spec_06_pattern_matching.rs` | ADT construction + `match` — the `Expr::ConstrADT` / `compile_constr_adt` collapse target. Guards observable ctor + match semantics unchanged. |
| `tests/spec_12_runtime.rs` (RC observable, redefinition, JIT reclaim via `/mem`) | The `Code`/`Jit`/`Linker` lifecycle-owner contract + GOT-single-source-of-truth invariant (the `ptr`-field removal). Guards lifecycle behaviour unchanged. |
| `tests/spec_10_io.rs` | `Pure`/`bind!`/IO path — `mode_equiv_io_pure_primitive`'s spec-section home; part of the 0122 cluster shape. |

These rows already exist in `PLAN.md` and are already `[Tested ...]` from
prior sprints; **no new rows are added by S75** (per §1, no new behaviour).
They are named here so the S77 int-conform sprint knows exactly which guards
must replay green when the binary builds workspace-wide.

---

## 4. FIXME 0122 re-test plan (the 4 `mode_equiv_*` `--link` failures)

**The four tests** (un-ignored, failing, `build_confidence.rs:156–225`):
`mode_equiv_adt_option_match`, `mode_equiv_pattern_match_nested`,
`mode_equiv_macro_user_defined`, `mode_equiv_io_pure_primitive`. Root cause
(per FIXME 0122): `--link`-mode GOT data atom `__cranelisp_got_user` /
`__cranelisp_got_prelude` declares alignment 1; the macOS linker wants
pointer alignment (8). REPL + `--run` (both JIT, no `.o`) pass; only `--link`
(AOT object writer) fails, on shapes that put ADT-ctor / defmacro-clause /
IO-trampoline entries in the GOT.

**Out of alignment scope** (SPRINT.md FIXME table + Rev 11): these are a
live `--link` GOT-alignment defect, not conform/cascade work. They stay
**failing-not-ignored** throughout (per `memory/feedback_failing_not_ignored.md`
and the parity rule). They ledger as `out-of-scope (owner=/backend)`.

**Re-test schedule** (per Phase-2 Rev 9 / Rev 11 — re-run after BOTH gates,
because each may shift GOT-slot population timing):

1. **After W1 (backend builds).** Until W1, backend doesn't compile, so the
   root binary doesn't link, so these tests can't even run. Once W1 lands the
   absorb (crate compiles) AND int conforms enough for the binary to link —
   **note: the binary stays red until S77**, so the *actual* re-run is
   crate-narrow-blocked too. Where these CAN be exercised this sprint is via
   a `/dev (backend)` in-crate object-writer unit test or a manual
   `--link` smoke once the binary links. For S75 the realistic checkpoint is:
   confirm the four shapes still produce the alignment-1 GOT atom in the
   object writer (inspectable via the W1-built crate, before int re-wires).
2. **After W2 (the `Code` ptr-rotation + `compile_to_module` rotation).** W2
   removes the per-variant `ptr` field (GOT becomes single source of truth)
   and rotates the codegen entry. This **may shift GOT-slot population
   timing** (Rev 11) — so the alignment defect may move, resolve incidentally,
   or persist. Re-assess the four shapes after W2 specifically: does the
   object writer still emit alignment-1 on the `__cranelisp_got_{M}` data
   symbol? The W2 `got_data_symbol_name` consolidation (the duplicate
   collapse) touches exactly the symbol the defect names — so W2 is the most
   likely incidental-fix point and MUST be checked.

**At W6 (if still failing):** the handoff to a future `/backend` defect
sprint carries a **minimal repro**, NOT just the four test names (per
`memory/feedback_cross_skill_minimal_repro.md`). The reduction target: the
SMALLEST program that emits an alignment-1 GOT data atom under `--link`. The
passing/failing pairs in FIXME 0122 already bracket it — `(defn main [] 0)`
and `add-i64` PASS; ADT-ctor / `match` / `defmacro` / `Pure` FAIL. The
minimal repro is one of the four reduced further: prefer
`(import [primitives [Pure]]) (defn main [] (Pure 7))` (the smallest,
no-prelude, single-primitive shape) reduced to confirm the GOT-atom-alignment
is the load-bearing failure. With the small repro, the object writer's GOT
data-symbol emission is inspectable by eye (small `.o`; `CRANELISP_CODEGEN_TRACE=1`
or `objdump`/`otool -l` on the produced `.o` to read the atom alignment). The
W6 handoff brief names this reduced repro + "the `__cranelisp_got_{M}` data
symbol is emitted with `align 1`; the AOT object writer is missing the
pointer-alignment directive on the GOT data symbol for ADT/defmacro/IO shapes"
— the isolation that the source/symptom already points at.

**No ledger/row change needed** beyond confirming the four stay
failing-not-ignored and the ledger `out-of-scope (owner=/backend)`
disposition holds with target sprint updated to "post-S75 re-assess" once W2
is read.

---

## 5. No new unit tests from `/qa` — boundary confirmation

Backend's unit tests are **`/dev (backend)`'s, inside the crate** —
`crates/cranelisp-backend/src/.../#[cfg(test)]` and any
`crates/cranelisp-backend/.../tests`. This includes:
- the `compile_constr_adt` behaviour test (the ctor-collapse target),
- the JIT/object-writer tests,
- the `Code`/`Jit`/`Linker` lifecycle + GOT-single-source unit tests,
- the cache round-trip / manifest / `Linker` mmap unit tests,
- the `Linker::get_symbol → Result` + `load_object` unit tests,
- the `register_got_observer` / `GotEvent` taxonomy tests.

`/qa` writes **none** of these (per `memory/feedback_unit_tests_with_dev.md`
+ `tests/CLAUDE.md §"Two tiers, no middle"`). `/qa`'s only S75 source edit is
the W5 `facade_compliance.rs` re-anchor + the `s68` sentinel flip — both
pure-`std::fs` structural tests in `tests/`, both `/qa`-owned. The boundary
holds: `/qa` does not touch `crates/cranelisp-backend/`.

---

## 6. FIXMEs `/qa` would file

**None this sprint.** All cross-skill requests are already captured in
SPRINT.md's Phase-2 review + the FIXME debt table (0221, 0244, 0191, 0182,
0223, 0099, 0096, 0232, 0122). `/qa`'s W5 work is self-contained in
`tests/`-owned files. The only conditional filing is at **W6**: if 0122 still
fails after W2's GOT-slot-timing shift, `/qa` updates FIXME 0122 in place with
the minimal repro (§4) for the future `/backend` defect sprint — that is an
update to an existing open FIXME, not a new one, and the failing tests remain
the durable trigger.

---

## Phase 3 exit checklist (`/qa`)

- [x] Risk verdict: **no new e2e test** — purely conform/cascade + retirement
      (§1).
- [x] W5 `facade_compliance.rs` re-anchor planned: backend + backend-cache
      DROP OUT (empty `facade_pairs()` / tombstone); `s68` sentinel flips
      backend to MUST-BE-ABSENT, mirroring S74's primitives/intrinsics flip
      (§2).
- [x] BLOCKED-by-red-binary stated plainly + named replay guard set recorded
      for S77 (§3).
- [x] 0122 re-test plan: re-run after W1 AND W2; minimal repro for W6 handoff
      if still failing; stays failing-not-ignored (§4).
- [x] Unit-test boundary confirmed: backend unit tests are `/dev (backend)`'s
      (§5).
- [x] Enough to draft the (single) failing structural-test edit Phase 5 will
      land: the W5 re-anchor + sentinel flip are fully specified.

---

## W5c — DONE (`/qa`, 2026-06-02)

Both edits landed; no new e2e authored (conform/cascade/retirement only).

- **`tests/facade_compliance.rs`** — `facade_pairs()` reduced to empty `vec![]`
  tombstone (backend + backend-cache dropped; all eight facades now retired).
  Header + doc-comments + orphan-test panic message + final-assert comment
  rewritten to the eight-retired / no-binding-facade state. `fn facade_pairs()`
  grep anchor preserved; orphan test retained (passes vacuously over the empty
  list). `/qa` reconciliation of plan §2a option B (tombstone spirit) with §2b
  recommendation (keep empty `facade_pairs()` so the `s68` anchor survives) —
  the lowest-risk, anchor-preserving shape.
- **`tests/s68_primitives_uniform.rs::s68_facade_compliance_test_exists_for_s68_touched_crates`**
  — flipped to ALL-ABSENT guard: backend POSITIVE assertion removed; absent-set
  is now `["cranelisp-primitives", "cranelisp-intrinsics", "cranelisp-backend"]`.
  Comment block rewritten to the S75 W5c collapse (none of the S68-touched
  crates retains a binding facade). Mirrors the S74 primitives/intrinsics flip.
- **Validation (`std::fs` dry-run + inspection):** confirmed all eight retired
  facade `.md` files are absent from `design/arch/facades/` (only `int.md` +
  audit `.md`s remain); `int.md` was never in `facade_pairs()` (binary crate,
  no `public-api.txt`; covered by `facade_pif_rows.rs`). Braces balanced in both
  files; helpers still referenced. **LIVE `cargo nextest` BLOCKED-by-red-binary**
  (these targets link the root `cranelisp` binary, red on int until S77) — NOT
  a coverage gap; the logic is pure `std::fs` and binary-independent.

## Phase 6 `/qa` carry (NOT this sprint)

- **`(map Some xs)` real-pipeline e2e** — constructor-as-value runtime; needs
  int's S77 GOT-entry production per FIXME 0249. This is a **Phase-6 `/qa`
  item**, NOT W5c. Author it once int conforms (S77) and the constructor-as-
  value GOT entries are produced. Noted here so it is not lost; intentionally
  NOT authored this wave (no new behaviour lands in W5c).
