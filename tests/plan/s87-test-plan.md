# Sprint 87 — /qa Sprint-Wide Test Plan (Phase 3 Design)

Owner: `/qa`. Authored Phase 3 (2026-06-20). Tests are NOT written here —
this plan scopes the failing tests Phase 5 Stage 1 will author so the
implementation stages have a concrete acceptance criterion. Persisted under
`tests/plan/` per `qa.md §"Test plan obligation"` (subordinate to `ledger.md`
and `PLAN.md`).

S87 is three stages: **A** (green-and-clear, source-touching), **B** (audit,
design/review only), **C** (stdlib adequacy + rollout, source-touching).

---

## 1. Stage-A entry verification — live red set == exactly the 4 named guards

**Procedure (the `ledger.md §Close-time Verification Protocol` run AT ENTRY, R3).**

1. `cargo nextest run --workspace --no-fail-fast` ONCE, read-only. (`/qa` owns
   the suite; no source change. One agent, one run.)
2. Confirm the summary line: `2829 tests run: 2825 passed, 4 failed, 0 skipped`.
3. Confirm the failing set is EXACTLY these 4 and nothing else:

| Guard test | File | Resolver | Spec |
|---|---|---|---|
| `disasm_command_shows_native_code_for_compiled_fn` | `tests/repl_introspection.rs:1599` | /int | repl/spec.md §3.1 |
| `info_multi_clause_macro_shows_clause_count` | `tests/repl_introspection.rs:1119` | /repl | repl/spec.md §11.2.2 |
| `type_error_names_expected_type_fully_qualified` | `tests/repl_negative.rs:125` | /typecheck | repl/spec.md §5.3 |
| `type_error_names_actual_type_fully_qualified` | `tests/repl_negative.rs:101` | /typecheck | repl/spec.md §5.3 |

4. For each guard confirm: (a) the `fn` still exists at the cited line;
   (b) it is `#[test]` with NO `#[ignore]` (failing-not-ignored);
   (c) it asserts the CORRECT outcome (RED today, flips GREEN on the fix).
5. **Any RED beyond these 4 is a genuine regression** → block Stage A until
   entered in `ledger.md` per the required-fields list. **Fewer than 4 RED**
   means a fix already landed → reconcile the ledger entry (Resolved removal).

> Note: SPRINT.md item 0 lists the macro-count guard as `→/repl`; the test
> physically lives in `tests/repl_introspection.rs` (not a `/repl`-named file),
> exercising the REPL `/info` card. Resolver skill = /repl; file = introspection.

**VERIFIED at Phase-3 authoring (2026-06-20, SHA `2fd7300`):** the live red set
is EXACTLY these 4 (`2829 run / 2825 passed / 4 failed / 0 skipped`, 25.3 s).
All 4 are `#[test]`, un-ignored, asserting the correct (FQ / count / disasm)
outcome. Stage-A entry gate is calibrated correctly — green-before-audit holds.

---

## 2. Per-fix test plan (Stage A) — mandatory unit test + e2e assessment

Per CLAUDE.md §Testing "every fix lands with a unit test; assess e2e need BEFORE
the fix." The 4 existing guards ARE the e2e record (failing-not-ignored, flip
green on fix). For each fix the **unit test is mandatory** and authored by `/dev`
in the owning crate's `#[cfg(test)]` in the SAME change-set as the fix. `/qa`
does not author unit tests; `/qa` names the locus and asserts the e2e remains
the cross-mode record.

### 2.1 /typecheck — FQ type names in error renderer (2 guards)

- **Root cause (confirmed):** `crates/cranelisp-typecheck/src/unify.rs:117`
  renders `format!("type mismatch: expected {t1}, got {t2}")` via `Type`'s
  Display / `format_type_display`. In `crates/cranelisp-types/src/types.rs:190-193`
  the scalar arms emit BARE strings (`Type::Int => "Int"`, `String => "String"`,
  …); only the `Type::ADT(fqtn, …)` arm (`:202`) emits a fully-qualified name.
  So the error renderer names scalars bare; the value-display path that qualifies
  uses a different formatter or post-qualifies.
- **Mandatory unit test (locus):** `crates/cranelisp-typecheck/src/unify.rs`
  `#[cfg(test)] mod tests` (the renderer's own crate). Construct a mismatch
  (`unify(Int, String)` analogue, or drive the message path) and assert the
  returned `CranelispError::TypeError.message` contains `primitives/Int` and
  `primitives/String`, NOT bare `Int`/`String`. This pins the FIX at the exact
  seam (the renderer), distinct from the e2e which only observes the REPL surface.
  - **/arch Phase-3 advisory (binding):** target the Display path used by the
    *error renderer*, NOT the value-display path that already qualifies. Do NOT
    unify the two if it changes REPL value-display output (separate §-contract).
    A unit test on value-display must stay green — if the fix lives in
    `cranelisp-types` (a shared `format_type_*_qualified` helper), a
    `crates/cranelisp-types/src/types.rs` unit test asserting value-display is
    UNCHANGED is the negative guard against the unification regression.
- **Additional e2e beyond the guards?** NO — the 2 existing guards
  (`..._expected_...`, `..._actual_...`) are the cross-mode record. They assert
  the precondition (type is named) AND the defect (FQ). Sufficient.
- **Negative coverage (already in the guards):** the `assert(contains("Int"))`
  precondition + `assert(contains("primitives/Int"))` defect together verify the
  name is present AND qualified. A bare-`Int`-must-not-leak negative belongs on
  the unit test: assert the message does NOT contain a bare ` Int` /` String`
  token in type position (substring discipline — guard against ` Int,`).

### 2.2 /int — wire `/disasm` to `produce_disasm` (1 guard)

- **Root cause (per ledger):** `src/repl.rs::handle_disasm` reads `intr.disasm`
  (never populated); `cranelisp_backend::produce_disasm` has ZERO call sites in
  `src/` (D41 on-demand re-derivation — dead path, lens (ii) class). Wire the
  handler to call `produce_disasm`.
- **Mandatory unit test (locus):** `src/` binary crate — the `#[cfg(test)]`
  module nearest `handle_disasm` (e.g. `src/repl.rs` tests, or the disasm
  helper's module). Unit-assert that for a JIT-compiled fn the handler produces
  the `; disasm for <name>` header + a `0x` instruction line, and does NOT
  return the dead-path `no disassembly available` string. If `handle_disasm`
  cannot be unit-driven without a live session (it may require a populated
  `intr`/symbol table), the seam to unit-test is the `produce_disasm` call
  wiring — a thin function that takes the compiled-fn handle and returns the
  disasm text; test THAT in `src/`. (`produce_disasm` itself is `cranelisp-backend`
  and presumably already has backend unit coverage — confirm; if not, the
  backend unit test is /dev-on-backend's, not in scope to re-author.)
- **Additional e2e beyond the guard?** NO — `disasm_command_shows_native_code_for_compiled_fn`
  is the REPL e2e record (asserts header + `0x` line present, dead-path string
  absent — already negative). Sufficient.

### 2.3 /repl — `/info` multi-clause-macro clause count (1 guard)

- **Root cause (per ledger):** `/info` on a multi-clause macro omits the
  required `N clauses` count line (spec §11.2.2); clause signatures + docstring
  present, count not. The `/info` macro-card renderer in `src/repl.rs` (the
  introspection card builder) must emit the count.
- **Mandatory unit test (locus):** `src/` binary crate `#[cfg(test)]` — the
  `/info` macro-card renderer. Unit-assert: given a macro entry with N=2 clauses,
  the rendered card text contains `2 clauses` AND the per-clause signatures (so
  the count is additive, not a replacement). If the renderer is a pure function
  `format_info_macro(entry) -> String`, test it directly; if it is tangled into
  the session, the seam to extract+test is the card-text builder.
- **Additional e2e beyond the guard?** NO — `info_multi_clause_macro_shows_clause_count`
  is the e2e record (asserts classification + `[x] -> Sexp` signature present AND
  `2 clauses` present). Sufficient.
- **Negative coverage:** the unit test should also assert a SINGLE-clause macro
  does NOT show a spurious `2 clauses` / shows `1 clause` (or no count) — guard
  against an off-by-one or always-plural bug. (Spec §11.2.2 / §1.2 plural form.)

### Stage-A test summary

| Fix | Owner | Unit-test locus (mandatory, /dev) | Extra e2e? | Existing e2e guard |
|---|---|---|---|---|
| FQ type-error names | /typecheck | `cranelisp-typecheck/src/unify.rs` tests (renderer) + value-display-unchanged neg in `cranelisp-types/src/types.rs` | No | repl_negative.rs (2 guards) |
| `/disasm` wiring | /int | `src/` disasm-call seam tests | No | repl_introspection.rs (1 guard) |
| `/info` clause count | /repl | `src/` `/info` macro-card renderer tests | No | repl_introspection.rs (1 guard) |

All four fixes: failing test(s) first → fix flips green → test(s)+fix in ONE
change-set. The 4 e2e guards flip green; 3+ new unit tests land. **0 intentional
reds at Stage-A exit.** Source-touching → serial (Wave 0), not concurrent.

---

## 3. Stage-C test plan — bare-verb promotion + stdlib self-test rollout

Runs on the green base (after Stage A). `/qa` writes e2e in `tests/`; stdlib
self-tests are a DISTINCT mechanism (see §3.2). All `tests/` e2e stay
zero-stdlib-dependency (CLAUDE.md §Stdlib separation) — bare-verb e2e use a
QA-owned custom prelude fixture, NOT `stdlib/prelude.cl`.

### 3.1 Bare-verb promotion — `count`/`get`/`conj`/`assoc`, `first`/`rest`

De-risked: DEF-1 (re-export-only `defn` body dropped from the consuming codegen
batch) was fixed in S86 — the repro
`tests/spec_08_modules.rs:1856::def1_prelude_provided_defn_called_bare_enters_codegen_batch`
is GREEN today (confirmed: not in the 4-red set). That is the pipeline guard the
promotion rests on. The Stage-C e2e PROVE the verbs resolve bare through a
re-export AND that constitutional invariants survive.

**Positive (verbs resolve bare via re-export):** for each promoted verb, an e2e
(`tests/spec_11_stdlib.rs` or a new `tests/stdlib_verbs.rs`) using a QA-owned
custom prelude fixture that `(export [collections.vec [count get conj]])`-shape
re-exports the verb, then calls it BARE through `--run` and REPL (and `--link`
via `run_through_all_modes` where the verb is value-position):

- `count_resolves_bare_through_reexport` — `(count [1 2 3])` ⇒ 3.
- `get_resolves_bare_through_reexport` — `(get [10 20 30] 1)` ⇒ 20.
- `conj_resolves_bare_through_reexport` — `(conj [1 2] 3)` ⇒ `[1 2 3]`.
- `assoc_resolves_bare_through_reexport` — `(assoc [1 2 3] 1 9)` ⇒ `[1 9 3]`.
- `first_rest_resolve_bare_through_reexport` — list `first`/`rest` bare.

> R4 sequencing constraint: FIXME 0402 (/spec curated-overload naming
> reservation) resolves in Stage A FIRST. The promotion set MUST NOT pre-bind a
> reserved Phase-H trait-dispatched name — promote module-qualified / via the
> de-risked re-export, NOT as the reserved trait names. The e2e fixture must use
> the re-export form, not a bare trait-name binding, or it pre-binds the reserved
> surface (a /spec violation). Confirm against 0402's resolved reserved set
> before authoring fixture names.

**Negative — constitutional invariants survive (these are negative coverage):**

- `_neg_` **FQ `primitives/<name>` still works** — after promoting `count`,
  `primitives/vec-len` / `collections.vec/count` FQ resolution is UNCHANGED
  (`primitives/<name>` reachable regardless of imports, spec §8.9.1).
- `_neg_` **empty prelude still valid** — `PreludeVariant::None`: a bare program
  with NO prelude typechecks + runs; bare `count` is UNDEFINED (the promotion is
  prelude-provided, not core). Asserts the curation invariant (spec §8.11.4 /
  §8.8.1: empty prelude valid; nothing prelude is load-bearing).
- `_neg_` **reachability unchanged** — the promoted verb's re-export does NOT
  leak the underlying raw primitive (`vec-len`) as a bare name (de-leak invariant
  from S86 still holds). `(vec-len [1 2 3])` bare → undefined; only the curated
  `count` resolves bare.

These negatives upgrade the spec §8.8.1 / §3.1 annotations to `[Tested+Neg]`.

### 3.2 Stdlib self-test submodule rollout — distinct mechanism

CLAUDE.md §Stdlib separation: `tests/` and `examples/` stay
**zero-stdlib-dependency**. Stdlib's own `(mod test)` self-tests therefore are
NOT exercised by the `tests/` suite directly — they are a distinct mechanism:

- **What they are:** `(mod test …)` submodules inside stdlib modules
  (e.g. `stdlib/compare/eq.cl` §Self-tests), using
  `testing.assertions` (`assert-true`/`assert-false`; `assert-eq` cross-module
  call was 0354-blocked — confirm current state) and run via the in-language
  runner `testing.runner` / `discover-tests` (a DEV-SESSION-ONLY host extern,
  test-discovery.md §4.5 — runs in a LIVE REPL, NOT as a `--run`/cache dep).
- **How `/qa` guards the rollout (e2e, still zero-stdlib-DEP for the harness):**
  the e2e harness invokes the BINARY against the real `stdlib/` via
  `CRANELISP_LIB` pointed at the stdlib dir (the production binary may depend on
  stdlib — only `tests/`/`examples/` source may not), in a REPL session that
  runs the in-language runner over the rolled-out self-test modules:
  - `stdlib_self_tests_run_green` (new `tests/stdlib_selftest.rs`) — REPL session:
    load stdlib prelude, `(discover-tests [...rolled-out test modules...])` via
    the runner, assert `N passed in` with the expected count and `0 failed` /
    no `FAIL`/`PANIC` lines. This is the mechanism CLAUDE.md §Stdlib separation
    permits: the binary uses stdlib; the TEST source is the harness + assertions,
    not a stdlib import.
  - The S86 blockers (D3 trait-module `(mod test)` re-defines parent trait; D4
    super-imported parent trait as constraint) are GREEN today
    (`tests/spec_08_modules.rs::mod_test_child_in_trait_module_does_not_redefine_parent_trait`,
    `::mod_test_child_super_imported_parent_trait_resolves_as_constraint` — both
    not in the red set), so the rollout is de-risked. If a self-test surfaces a
    NEW compiler defect, `/qa` reduces it to a narrow failing-not-ignored repro
    in `tests/` (stdlib-free) and hands off to the owning compiler skill per the
    defect protocol — the self-test green is not the regression guard, the narrow
    repro is.
  - `discover-tests` dev-session scope: the self-test e2e MUST run via the REPL
    (where the extern resolves), NOT `--run`/`--link` (where `testing.runner`'s
    discover path is unresolved by design, test-discovery.md §4.5). The pure
    helpers run in every mode; the runner's discover/run path is REPL-only.

> Caching gotcha (stdlib CLAUDE.md): a stale `./.cranelisp-cache` masks stdlib
> edits. The e2e harness already runs in a fresh per-test tmpdir
> (`Cranelisp::new` + `.runs/`), so no stale cache; if a self-test e2e reads the
> repo-root stdlib, it must NOT inherit a root `.cranelisp-cache` (use the
> tmpdir CWD, `CRANELISP_LIB` pointing read-only at `stdlib/`).

---

## 4. Stage-B (audit) — design/review only, NO new tests

Stage B is a fresh-view per-crate audit (`/review` + `/arch`); **design/review
only — no implementation, no new tests** (METHOD §Phase 5, unless
emergent-mandatory). `/qa` authors NO tests for Stage B. The audit produces a
backlog + artefacts (`audits/loc-s87.md`, per-crate `.mmd`,
`audits/s87-findings.md`), not code.

**/qa lens contribution to the audit (the one S86 finding to fold in):**

- **Audit all wall-clock timing witnesses for best-of-N robustness under the
  saturated `--workspace` run.** Single-shot timing assertions are latent
  close-gate flakes: a parallel witness starved of cores under the 16-process
  saturated run measures a false slow time → false RED at close. S86 hardened
  the auto-IO positive witnesses
  (`tests/spec_10_io.rs::auto_io_independent_diff_token_parallelizes_e2e`,
  `::auto_io_par_grouping_uniform_across_modes`,
  `::resource_serial_diff_token_parallelizes` — best-of-N=5 `min` on the
  POSITIVE `< RS_MIDPOINT_MS` assertions only; negatives/serials left
  single-shot, since contention only makes a `> midpoint` guard MORE serial).
  - **Audit deliverable (/qa lens, fed to `audits/s87-findings.md` as a finding,
    NOT a code change):** sweep `tests/` for ANY remaining wall-clock witness
    (`*_elapsed_ms`, `prog_run_elapsed_ms`, `prog_link_elapsed_ms`, `Instant`,
    `< *_MIDPOINT_MS` / time-inequality assertions) that is NOT best-of-N
    hardened on its positive leg, and flag each with `file:line` + severity. The
    S85 map-reduce witness (`spec_12_runtime.rs::lenient_vec_map_reduce_*`) and
    the S86-hardened auto-IO/resource witnesses are the hardened precedent; any
    OTHER single-shot positive timing assertion is a latent flake finding. This
    is a finding for the backlog, actioned (if scheduled) in a future sprint —
    NOT an in-sprint test edit (Stage B is design-only). If the sweep finds a
    witness whose un-hardened state is ALREADY flaking the close gate, that is
    emergent-mandatory and may be hardened in-sprint per METHOD §Phase 5.

No other Stage-B test obligation for `/qa`.

---

## 5. /qa Phase-3 plan (for SPRINT.md "Skill plans / /qa")

**Task.** Author the S87 sprint-wide test plan so the implementation stages have
failing tests to turn green. Stage A: verify the live red set == exactly the 4
named guards (done at Phase-3 authoring — VERIFIED, see §1); name the mandatory
unit-test locus + e2e assessment per fix (§2). Stage C: e2e for bare-verb
promotion (positive resolve-bare + negative constitutional-invariant survival)
and the stdlib self-test rollout guard mechanism (§3). Stage B: confirm no new
tests, contribute the wall-clock-witness best-of-N audit finding to the /qa lens
(§4). Phase 5 Stage 1: `/qa` writes the failing e2e the plan calls for,
sprint-wide, BEFORE per-crate D/D/R cycles (QA-first, METHOD §2.2).

**Design refs.** `tests/plan/ledger.md` (§S86 4-guard entries + §Close-time
Verification Protocol); `tests/plan/s87-test-plan.md` (this file);
`crates/cranelisp-typecheck/src/unify.rs:117` + `crates/cranelisp-types/src/types.rs:182-235`
(FQ-naming root cause); `src/repl.rs` (disasm + /info renderers);
`repl/spec.md §3.1/§5.3/§11.2.2`; `spec/08-modules.md §8.8.1/§8.9.1/§8.11.4` +
`spec/03-types.md §3.1` (bare-verb invariants); `stdlib/prelude.cl:54-108` +
`stdlib/plan-stdlib.md §1.5` (curated surface + DEF-1 fix); FIXME 0402
(curated-overload naming reservation, resolves Stage A first, R4);
`tests/CLAUDE.md §"Sustained-load convention"` + S86 best-of-N ledger entry
(wall-clock witness hardening); `design/arch/test-discovery.md §4.5`
(discover-tests dev-session scope).

**Acceptance.**
- Stage-A entry: live `cargo nextest run --workspace` red set == EXACTLY the 4
  named guards (`2829/2825/4/0`), all failing-not-ignored, asserting correct
  outcome. Any other RED blocks Stage A (entered in `ledger.md` first).
- Stage-A exit: the 4 e2e guards GREEN; each fix carries its mandatory unit test
  (renderer-seam / disasm-call / info-card) in the SAME change-set; 0 intentional
  reds. Close-time ledger re-verification satisfied for the 4 touched entries
  (Resolved → removed from `ledger.md`, noted in close report).
- Stage-C: bare-verb e2e prove resolve-bare-via-reexport (positive) AND
  constitutional-invariant survival (negative: FQ still works, empty prelude
  valid, no raw-primitive bare leak) — promotion set does NOT pre-bind a 0402
  reserved name; stdlib self-test rollout guarded via the REPL-session runner
  e2e (`CRANELISP_LIB`→stdlib, fresh tmpdir, no stale cache), zero-stdlib-DEP
  harness; any NEW defect → narrow failing-not-ignored repro in `tests/` + handoff.
- Stage-B: no `/qa` tests authored; the wall-clock-witness best-of-N sweep is
  delivered as a finding (`file:line` + severity) into `audits/s87-findings.md`,
  not an in-sprint test edit (unless an active flake makes it emergent-mandatory).
- Every new test traces to a spec section (`// spec:`), has a `ledger.md`/`PLAN.md`
  row; `spec_link_check.py` clean on touched files; suite runtime within the 30 s
  cap; per-wave count+runtime reported.

**Next skills.** `/int` (disasm wiring), `/repl` (info card), `/typecheck` (FQ
renderer) for the Stage-A resolvers (each handed the named e2e guard + the
unit-test locus); `/stdlib` for Stage-C rollout (after 0402 resolves);
`/review` + `/arch` for the Stage-B audit (the /qa lens finding feeds the
synthesis).
