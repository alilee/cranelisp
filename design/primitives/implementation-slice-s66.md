# Sprint 66 implementation slice — `cranelisp-primitives` (new crate)

**Status.** draft
**Author.** `/design (cranelisp-primitives)`, 2026-05-06
**Reads.** `design/arch/facades/primitives.md` (W1 output, S65); `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md` (D43); `design/arch/legacy/substance-scoping.md §1.7` (substance source); `design/arch/fixmes/0150-runtime-split-primitives-intrinsics.md` (implementation tracker); `design/runtime/runtime.md` (current runtime master design — context for what migrates); `crates/cranelisp-runtime/src/primitives/{int,float,bool,mod}.rs` (current source of language-level callable primitives); `sprints/SPRINT.md` Phase 4 W4a; `design/arch/sprint-65-reshape-phase-2-review.md §3` (slice template).

**This is a "new crate" slice.** `crates/cranelisp-primitives/` does not yet exist. The slice scopes its **creation** plus the migration of user-callable primitives out of `crates/cranelisp-runtime/src/primitives/` into the new crate, per Decision 43's split. Sibling slice: `design/intrinsics/implementation-slice-s66.md` (the other half of the D43 split).

This slice maps onto FIXME 0150's Phases 1, 2 (primitives portion), 4 (primitives portion), and 5 (primitives portion). The intrinsics slice maps onto Phases 1, 2 (intrinsics portion), and 5 (intrinsics portion). Phase 3 (backend trait-knowledge deletions + crate-dep flip) is in the backend slice. Phase 4 (stdlib trait-impl audit) is split across this slice (deletion of `cranelisp_op_*` duplicates) and stdlib's slice (the impl-body audit).

---

## 1. Scope from facade

The crate does not yet exist, so every line of `facades/primitives.md` is a delta. The table below enumerates the migration as discrete actions. Action classes: **C** = create (new file/crate scaffolding); **M** = move (relocate source from `cranelisp-runtime`); **D** = delete (retire duplicate / pre-D43 artefact); **R** = re-export / wiring (workspace + dep declarations); **A** = audit + reconcile (verify naming + symbol-table parity).

| # | Delta | Source location(s) | Action class | FIXME closed | Acceptance |
|---:|---|---|---|---|---|
| 1 | Create `crates/cranelisp-primitives/` crate scaffolding (`Cargo.toml`, `src/lib.rs`, `CLAUDE.md`) | new — `crates/cranelisp-primitives/{Cargo.toml,src/lib.rs,CLAUDE.md}` | C | 0150 (Phase 1) | `cargo build -p cranelisp-primitives` succeeds with empty surface. |
| 2 | Add `crates/cranelisp-primitives` to workspace; declare path-dep in root `Cargo.toml` | `Cargo.toml` (workspace `members` + `[workspace.dependencies]`) | R | 0150 (Phase 1) | Workspace resolves; `cargo metadata` shows the new member. |
| 3 | Add `cranelisp-types` dep on the new crate (only Rust-level dep) | `crates/cranelisp-primitives/Cargo.toml` | R | 0150 (Phase 1) | Per facade §"Consumed surface" — only `cranelisp-types` consumed; nothing else. |
| 4 | Move `cranelisp-runtime/src/primitives/int.rs` → `crates/cranelisp-primitives/src/int.rs` | `crates/cranelisp-runtime/src/primitives/int.rs` (165 LOC incl. 10 `cranelisp_op_*` duplicates) | M | 0150 (Phase 2) | All 12 `pub extern "C" fn` (incl. `int_to_string`, `parse_int`, plus the 10 duplicates pending Phase 4 deletion) compile in the new location; old file deleted from runtime. |
| 5 | Move `cranelisp-runtime/src/primitives/float.rs` → `crates/cranelisp-primitives/src/float.rs` | `crates/cranelisp-runtime/src/primitives/float.rs` (~30 LOC) | M | 0150 (Phase 2) | `float_to_string` and any float arithmetic primitives compile in new location; old file deleted. |
| 6 | Move `cranelisp-runtime/src/primitives/bool.rs` → `crates/cranelisp-primitives/src/bool.rs` | `crates/cranelisp-runtime/src/primitives/bool.rs` (~15 LOC) | M | 0150 (Phase 2) | `bool_to_string` (and `not` if present) compile in new location; old file deleted. |
| 7 | Author `crates/cranelisp-primitives/src/lib.rs` re-exports — declare each per-type module + re-export the `extern "C"` fn set so the symbol-name surface is one `pub use` block | new | C | 0150 (Phase 2) | The list is searchable by string-grep of `pub use` lines; one cross-reference per facade-listed primitive name. |
| 8 | Add the **Rust-level** `extern "C" fn add_i64`/`sub_i64`/`mul_i64`/`div_i64`/`mod_i64`/`eq_i64`/`lt_i64`/`gt_i64`/`le_i64`/`ge_i64` (and float equivalents) — the *named* primitives that today exist only as backend's CLIF-substitution targets but have no Rust extern fallback for indirect calls | new — `crates/cranelisp-primitives/src/int.rs` + `float.rs` | C | 0150 (Phase 4 sets up: `add-i64` IS the addressable form; without a Rust extern, indirect calls have no backing) | Each named primitive in `facades/primitives.md` §"Integer primitives" + §"Float primitives" has a Rust extern fn body; `add-i64` linker-symbol resolves at JIT registration. |
| 9 | Delete the 10 `cranelisp_op_*` extern fns from `crates/cranelisp-primitives/src/int.rs` (post-relocation) | `crates/cranelisp-primitives/src/int.rs` (lines 60–119 after move) | D | 0150 (Phase 4) | `git grep cranelisp_op_` returns nothing in the new crate; `add-i64` is the sole addressable form per facade BC-invariant #3. |
| 10 | Author the `pub fn primitives_module() -> ModuleEntry`-like seeding helper, OR confirm seeding stays driven by `cranelisp-types::operator::ring{0,1,3}_primitives()` and primitives crate exposes only the Rust extern fns (no helper). | `crates/cranelisp-primitives/src/lib.rs`; cross-check `crates/cranelisp-types/src/operator.rs` `ring0_primitives()`/`ring1_primitives()`/`ring3_primitives()` | A | none (open-question; resolution in §6) | Per facade §"Public surface" the symbol-table seeding is `int`'s job consuming `cranelisp-types`'s `primitives()` registry; this slice confirms primitives crate exposes ONLY the extern fns + the `cranelisp-types` registry knows their names. No seeding helper authored unless §6 Q1 resolves toward "yes." |
| 11 | Update `crates/cranelisp-backend/src/jit.rs` `IntrinsicSymbol` array — entries for `int-to-string`, `parse_int`, `float-to-string`, `bool-to-string`, AND the per-primitive `add-i64`/`sub-i64`/… `add-f64`/… extern names — point to `cranelisp_primitives::*` (was `cranelisp_runtime::*`); REMOVE the 10 `cranelisp_op_*` rows. | `crates/cranelisp-backend/src/jit.rs:130–159` | M+D | 0150 (Phase 3 partial — primitives portion of the registration table) | After this row + the backend slice's row #N (delete trait-knowledge maps), `register_intrinsics` registers exactly the addressable primitive surface; `cranelisp_op_*` names are gone from the symbol table. |
| 12 | Add `cranelisp-primitives` dep to backend `Cargo.toml` (alongside `cranelisp-intrinsics` and dropping `cranelisp-runtime`) | `crates/cranelisp-backend/Cargo.toml:8` | R | 0150 (Phase 3) | `cargo build -p cranelisp-backend` succeeds; `cranelisp-runtime` no longer in backend's dep tree. |
| 13 | Add `cranelisp-primitives` dep to int's `Cargo.toml` (for primitives-module seeding at session init) | `src/Cargo.toml` (the binary crate that hosts `int`) | R | 0150 (Phase 3) | int names `cranelisp_primitives` for the seeding helper / extern-fn import path; `cargo build` of the binary succeeds. |
| 14 | Author `crates/cranelisp-primitives/CLAUDE.md` — local conventions, the JIT-symbol-naming convention reminder (kebab-case at symbol-table layer; underscore in Rust source), Decision-24 consuming-convention reminder at the extern boundary, FIXME-filing conventions | new | C | parallels FIXME 0102 (runtime CLAUDE.md) — primitives is a sibling that needs the same | File exists; covers the BC invariants from facade §"Bounded-context invariants"; `/dev` next-narrowing has a starting point. |
| 15 | Verify `src/CLAUDE.md` "JIT Symbol Names" section reflects the post-D43 convention — "registered into the symbol table at `primitives/<name>`" wording present (NOT "Runtime infrastructure"). May already be covered by W3's int-facade revision but cross-checked here. | `src/CLAUDE.md` | A | 0150 (Phase 5) | Wording matches facade §"Public surface" line 13. If still old, file `target: /int` FIXME from this slice. |
| 16 | `cargo public-api` baseline file authored for `cranelisp-primitives`; no baseline for the (retiring) runtime is created/maintained — runtime baseline deletes per Phase 5 of FIXME 0150 | `crates/cranelisp-primitives/cargo-public-api-baseline.txt` (or per-crate convention used by other crates) | C | 0150 (Phase 5) | `cargo public-api` against the new crate produces the baseline; CI consumes it. |

**Total rows: 16.** Action-class breakdown: **C × 5** (rows 1, 7, 8, 14, 16); **M × 4** (rows 4, 5, 6, 11 — row 11 is M+D partly); **D × 1** (row 9; row 11 mixed); **R × 4** (rows 2, 3, 12, 13); **A × 2** (rows 10, 15).

---

## 2. Ordering within the slice

Three logical phases gate each other; rows within a phase parallelise where they touch independent files.

**Phase α — crate scaffolding (rows 1, 2, 3, 14).** Land the empty crate + `Cargo.toml` workspace registration + `CLAUDE.md`. Must precede every other row because rows 4–13 depend on the crate existing.

**Phase β — source migration + named-primitive authoring (rows 4, 5, 6, 7, 8).** Move runtime's `primitives/{int,float,bool}.rs` over; author the new named-primitive `add_i64`/`sub_i64`/… extern fns; expose via `lib.rs`. Internally:

- 4, 5, 6 are file moves and parallelise (independent files).
- 8 (new named primitives) layered onto the moved files — must follow 4/5/6.
- 7 (`lib.rs` re-export wall) is the integration step — last in this phase.

The 10 `cranelisp_op_*` duplicates from `int.rs` are kept across the move (they compile in the new crate even though backend's `IntrinsicSymbol` array will stop registering them in row 11). They delete in Phase γ — post-row-11 the backend no longer references them, so deletion is safe.

**Phase γ — consumer wiring + deletion (rows 9, 10, 11, 12, 13).** Update `jit.rs` `IntrinsicSymbol` registration (row 11) to name `cranelisp_primitives::*` and stop registering `cranelisp_op_*`. Add the dep edges (rows 12, 13). Delete the 10 `cranelisp_op_*` extern fns (row 9). Confirm seeding-helper question (row 10).

Within Phase γ:
- 11 must precede 9 (delete duplicates only after backend stops registering them).
- 12 + 13 are parallel-safe with 11.
- 10 is independent (audit/decision).

**Phase δ — finalisation (rows 15, 16).** Cross-check `src/CLAUDE.md` wording (row 15); author public-API baseline (row 16). Independent and post-everything.

The phase ordering across this slice and the intrinsics slice is bilateral — see §4. Phase α MUST land in lockstep across both (FIXME 0150 Phase 1 single commit). Phase β is parallelisable across the two slices (independent files). Phase γ in this slice depends on Phase γ in the intrinsics slice for the same `jit.rs` file (both slices touch the `IntrinsicSymbol` array; coordinate one commit, not two — see §4).

---

## 3. Estimated effort

**~2 narrow `/dev` triad cycles** (one cycle = "scope-implement-test" for one bounded change set).

- Cycle 1: Phases α + β (crate creation + source migration + named-primitive authoring + lib.rs wall). ~16 file additions; ~5 Cargo.toml edits; light per-fn body work for the named primitives (each is `a + b`, etc., so trivial); ~3-line CLAUDE.md draft. The named-primitive authoring (row 8) is the largest single deliverable in this cycle and is mechanical (10 int + ~10 float + 1 bool).
- Cycle 2: Phases γ + δ (consumer wiring + deletion + finalisation). The backend `jit.rs` edit (row 11) is shared with the intrinsics slice and must be coordinated. The `cranelisp_op_*` deletion (row 9) is a `git rm`-grade change once row 11 lands. The dep flips (rows 12, 13) are one-liners. Public-API baseline (row 16) is mechanical.

Sizing rationale: no novel design, no algorithm work, no test-shape changes. The volume is real (16 rows, multi-crate touch, workspace edits) but each row is shallow. The **coordination** with the intrinsics slice and backend slice on row 11 is what consumes any non-mechanical effort.

If row 8's named-primitive list expands at S67+ (per facade §"Float primitives" line 45 — "comparison ops as the language requires; pre-implementation list will be confirmed at S67+ vertical"), this slice gains 1–2 cycles worth of follow-on. That work belongs to the S67 vertical, not S66 — the initial cut is whatever the spec already names.

---

## 4. Dependencies on other crates' slices

Bilateral — every entry below has a counterpart in the named slice, surfaced for cross-check.

| This slice's item | Depends on | In the other crate's slice |
|---|---|---|
| Row 1 (crate scaffolding) | `design/intrinsics/implementation-slice-s66.md` Phase α — Cargo workspace member addition coordinated as one commit | intrinsics slice §"Phase α" |
| Row 11 (`jit.rs` IntrinsicSymbol array — primitives portion) | `design/backend/implementation-slice-s66.md` row "delete trait-knowledge maps in `operators.rs:323–394` and `literals.rs:327–332`; rename `operators.rs` → `primitives_inline.rs`" | backend slice §"trait-knowledge map deletions" |
| Row 11 (intrinsics rows in same array) | `design/intrinsics/implementation-slice-s66.md` row "register intrinsics (`heap_alloc`, `rc_dec`, `runtime_panic`, `cranelisp_run_io`, …) under `cranelisp_intrinsics::*` path" | intrinsics slice §"jit.rs IntrinsicSymbol array — intrinsics portion" |
| Row 12 (backend Cargo.toml: drop `cranelisp-runtime`, add `cranelisp-primitives`) | `design/backend/implementation-slice-s66.md` row "Cargo.toml dep flip" + `design/intrinsics/implementation-slice-s66.md` row "backend Cargo.toml gets `cranelisp-intrinsics` dep" | backend slice §"Cargo.toml dep flip"; intrinsics slice §"backend dep edge" |
| Row 13 (binary `src/Cargo.toml`: add `cranelisp-primitives` dep) | `design/int/implementation-slice-s66.md` row "Cargo.toml dep flip" + `design/intrinsics/implementation-slice-s66.md` row "int Cargo.toml gets `cranelisp-intrinsics` dep" | int slice §"Cargo.toml dep flip"; intrinsics slice §"int dep edge" |
| Row 9 (delete `cranelisp_op_*` duplicates) | `design/stdlib/implementation-slice-s66.md` (the trait-impl audit must precede or coincide — if any stdlib impl was relying on `cranelisp_op_*` name resolution rather than backend collusion, deletion breaks it) | stdlib slice §"trait-impl audit (impl Num Int, impl Display Int, impl Eq Int, impl Ord Int, impl Num Float)" |
| Row 9 (delete `cranelisp_op_*` duplicates) | `design/backend/implementation-slice-s66.md` row "delete `literals.rs:327–332` `+ → cranelisp_op_add` map" — the duplicate path through that map must close before the duplicates delete | backend slice §"literals.rs operator-as-value map deletion" |
| Crate retirement (row not present here; tracked by `design/runtime/implementation-slice-s66-retiring.md`) | `design/runtime/implementation-slice-s66-retiring.md` final phase: workspace `Cargo.toml` removes the runtime member | runtime-retiring slice §"workspace member removal" |

**Cross-crate dependency count: 5 distinct sibling slices** (intrinsics, backend, int, stdlib, runtime-retiring) — the largest sibling-set of any S66 slice, reflecting D43's largest-single-migration scope.

`/sprint`'s wave plan must:
- treat Phase α as a single-commit lockstep across all five sibling slices;
- order Phase γ such that backend slice's trait-map deletions land at-or-before this slice's row 11, and stdlib slice's audit lands at-or-before row 9;
- treat the runtime-retiring slice's workspace-member-removal as the absolute last commit (after this slice and the intrinsics slice both finish their Phase β migrations).

---

## 5. Test surface impact

**No new public-API tests originated by this slice.** Primitives is a leaf crate publishing extern fns — every primitive's correctness is exercised by integration tests (`tests/`) that call the language operator from user code.

**Existing tests that change shape:**

1. **None at the test source level** — the migration is an import-path change only. Tests that today call `cranelisp_runtime::int_to_string` directly (if any) would need to swap to `cranelisp_primitives::int_to_string`. Confirmed: `git grep cranelisp_runtime::int_to_string` reports only `crates/cranelisp-backend/src/jit.rs:130` (the `IntrinsicSymbol` row, which migrates per row 11 of this slice). No test source calls primitives by Rust path; tests exercise them via the language.

2. **Operator-as-value tests** (`(let [f +] (f 1 2))` shape — exists in `tests/` integration suite per FIXME 0150 §"Test impact"): these route through `cranelisp_op_add` today (via the `literals.rs:327–332` map). Post-row-9 deletion they go through the `+`-symbol-table-entry's GOT slot which holds the `(impl Num Int)` body which calls `(add-i64 a b)`. **Net behaviour unchanged; intermediate path changed.** No test edit required if the test asserts on language-level behaviour. If any test asserts on `cranelisp_op_*` symbol resolution by name, that's a test bug to surface — file FIXME `target: /qa` at row 9 enactment.

3. **`crates/cranelisp-primitives/src/*.rs` unit tests** (per `feedback_unit_tests_with_dev.md` — owning skill writes unit tests inside its crate). Each migrated file (`int.rs`, `float.rs`, `bool.rs`) ports its existing `mod tests` from runtime; new named-primitive fns from row 8 each get a one-shot test (`assert_eq!(add_i64(2, 3), 5);`). Volume: ~25 unit tests authored as part of cycle 1; mechanical.

4. **`cargo nextest run` of the whole workspace** must pass at every commit boundary in Phase α/β/γ — the migration MUST NOT break the suite at any intermediate state. The phasing in §2 is designed for this: Phase α adds a stub crate (no behaviour), Phase β duplicates source (runtime AND primitives both compile), Phase γ flips registration THEN deletes runtime's copy.

**`/qa` test-plan coordination.** This slice files a coordination request against `/qa`'s S66 test plan slice: confirm there is **at least one** integration test that exercises operator-as-value (`(let [f +] (f 1 2))`) — load-bearing for row 9 deletion's safety. If the test is missing, file `target: /qa` FIXME at slice review time. (`/qa`'s S66 slice is authored alongside this one in W4a per SPRINT.md.)

---

## 6. Open questions

Surfaced for `/arch`. Not invented; the facade does not pin these.

**Q1 — Where does the `primitives` synthetic-module seeding helper live?**

Facade §"Public surface" line 14 says symbol-table seeding is `int`'s job, consuming `cranelisp-types`'s `primitives()` registry. But the registry today (`cranelisp-types/src/operator.rs:39+178+315`) contains `ring0_primitives()`, `ring1_primitives()`, `ring3_primitives()` — function-name strings + signatures. To translate registry entries into actual GOT-installed `extern "C" fn` pointers, *something* needs to resolve `Symbol("add-i64")` to `cranelisp_primitives::add_i64 as *const u8`. Two options:

- (a) **`cranelisp-primitives` exposes a public `pub fn primitives_table() -> &'static [(Symbol, *const u8)]`** that int consumes alongside `cranelisp-types::ring0_primitives()`. The two tables join on `Symbol` to produce the seeded module.
- (b) **`cranelisp-types::ring0_primitives()` carries the fn pointer directly in `PrimitiveDef`.** Requires `cranelisp-types` to depend on `cranelisp-primitives` — which inverts the dependency direction (primitives depends on types, per facade §"Consumed surface"); `cranelisp-types` depending back creates a cycle.
- (c) **`int` uses Cranelift's linker name-resolution** (the same path backend's `register_intrinsics` already uses): seeding installs symbol-table entries by name only, and the actual pointer resolves at JIT registration time via `IntrinsicSymbol`. This is the simplest path and matches what `register_intrinsics` already does, but raises Q2 below about whether seeding even needs the pointer.

**Recommended.** (c) is correct in shape and matches the existing pattern. The seeding helper (if any) lives in `int`, not in `cranelisp-primitives` — primitives crate stays leaf-pure. Row 10 of the delta table commits to this resolution unless `/arch` says otherwise. **File `target: /arch` FIXME if (a) is preferred — would require row 10 to author a new helper in `cranelisp-primitives/src/lib.rs`.**

**Q2 — Does the seeded `primitives/` symbol-table entry need the fn pointer at seed time, or is "this name is a primitive" enough until first call?**

Symbol-table entries today carry a `kind` plus, post-Decision-41, a `Code` enum describing how the symbol was compiled. For primitives (which are not compiled — they're linked in), `Code` is presumably `Code::Primitive` or similar. Whether the fn pointer is materialised at seed time or lazily at first call is a `cranelisp-types`-and-int facade decision that bears on row 10's resolution. The facade does not pin this. **File `target: /arch` FIXME at slice review.**

**Q3 — `not` placement: is `not` a primitive or a stdlib fn?**

Facade §"Boolean primitives" line 51 lists `not(b: i64) -> i64`. Source today: `crates/cranelisp-runtime/src/primitives/bool.rs` has `bool_to_string` but `git grep` confirms no `pub extern "C" fn not` in that file. The facade may be aspirational, OR `not` may live elsewhere (stdlib's `(impl Not Bool)`). Slice authoring time confirmed: **the facade says it should be a primitive but it is not present in source.** This is row 8 territory (author it as part of cycle 1) — but verify with `/arch` whether `not` is genuinely categorised as a primitive (per spec) or whether the facade is over-specified. **File `target: /arch` FIXME at slice review.**

**Q4 — `parse-int` symbol-table name vs Rust source name.**

Facade lists `parse_int` (Rust) → `parse-int` (symbol). Source today is `parse_int` (Rust), but `git grep parse-int` shows the symbol-name kebab form is used by `cranelisp-types::ring*_primitives()` registries. Confirm during cycle 1: does the linker-side `register_intrinsics` row in `jit.rs` use `parse_int` (matching Rust) or `parse-int` (matching the symbol table)? Mismatch would cause linker failure at JIT time. **Implementation diagnostic, not a facade gap; resolve in cycle 2.**

**Q5 — `non_exhaustive` policy for the `pub use` re-export wall.**

Facade §"`#[non_exhaustive]` policy" says vacuous (no public structs/enums). Confirmed. But what about adding a *new* primitive between S66 and S67? The crate currently has no version-bump policy; the facade is silent. Is adding a primitive a minor or major version bump under `cargo public-api`? Likely minor (additive surface), but `/arch` should confirm before row 16's baseline is established. **File `target: /arch` FIXME at slice review.**

---

## Cross-references

- `design/arch/facades/primitives.md` — the facade this slice executes against
- `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md` — D43
- `design/arch/legacy/substance-scoping.md §1.7` — substance source for D43
- `design/arch/fixmes/0150-runtime-split-primitives-intrinsics.md` — implementation tracker (this slice executes its primitives portion)
- `design/intrinsics/implementation-slice-s66.md` — sibling slice (the other half of D43); bilateral dependencies in §4
- `design/backend/implementation-slice-s66.md` — backend trait-knowledge deletions + `operators.rs` rename
- `design/int/implementation-slice-s66.md` — int slice (Cargo.toml dep flip + symbol-table seeding host)
- `design/stdlib/implementation-slice-s66.md` — stdlib trait-impl audit (precedes row 9 deletion)
- `design/runtime/implementation-slice-s66-retiring.md` — runtime's retirement slice (workspace member removal)
- `design/arch/sprint-65-reshape-phase-2-review.md §3` — slice template
- `sprints/SPRINT.md` Phase 4 W4a — wave that authors this slice
