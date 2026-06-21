# `src/` Binary-Surface Audit — Sprint 87 Stage B

> **Predecessor.** This refreshes `audits/src-20260423.md` (+ `.mmd`). That audit
> is a point-in-time assessment superseded by Decisions 38–42 (per its own S63
> note); current-state observations there remain historical. This S87 pass is a
> **delta + currency check** on that baseline, NOT a from-zero look, per
> `sprints/SPRINT.md` Stage B mechanism 1.
>
> **Scope.** The `src/` binary surface (REPL / session / CLI / scheduler /
> pipeline orchestration), folding in the 65-line `cranelisp-exe-bundle`
> (`crates/cranelisp-exe-bundle/src/lib.rs`, 146 raw / trivial). `src/` is the
> #1 corrected-LOC surface (13,639 prod LOC, `audits/loc-s87.md`).
>
> **Instrument (R5a same-instrument).** The 2026-04-23 baseline taxonomy was
> seven findings ranked by Impact (god-files, split-brain, dependency-registration
> spread, worker-split, fat `lib.rs`, transitional residue, inline-narrative). The
> S87 lens checklist (i)-(vii) maps onto that taxonomy so "still-open / regressed /
> resolved" is a true diff. Read-only on code; this and `src-s87-current-state.mmd`
> are the only artefacts written.

---

## 1. Baseline reconciliation (every 04-23 finding)

The dominant structural event since the baseline is the **FIXME 0109 §3.3 Wave-C/D
decomposition**: the two god-files the baseline named — `session_v4.rs` (5,417 LOC)
and `worker.rs` (5,041 LOC) — were split. `session_v4.rs` is now 1,428 corrected
LOC; the eval form-chain moved to `eval.rs`, the REPL/slash/display surface to
`repl.rs`, the per-form gap-orchestration to `process_form.rs`. This resolves or
substantially reduces the baseline's three top-Impact findings.

| # (04-23) | Finding | S87 status | Evidence |
|---|---|---|---|
| 1 | `session_v4.rs` god-file (5,417 LOC, 23 fns ≥60) | **Resolved (structural)** — split per FIXME 0109; residual 1,428 corrected LOC is lifecycle + `SharedState` + introspection getters, the named §3.3 residual responsibility set | `src/lib.rs:58-92`; `src/CLAUDE.md §"Session/REPL module decomposition"` |
| 2 | `worker.rs` split-brain god-file + pervasive "mirror"/"shared core" comments | **Largely resolved** — worker.rs now 749 corrected LOC; the macro-clause mirror collapsed to `compile_macro_clause_core` (`process_form.rs:380`) with two thin adapters; `inline_jit_codegen_for_module`/`_for_names` is a documented wrapper-over-core pair, not a mirror | `process_form.rs:380,466,2859`; `worker.rs:777,833` |
| 3 | Dependency-registration / publish-before-register protocol split across ≥3 authorities | **Mostly resolved** — `process_cluster` is now the SOLE crate-crossing for `ResolutionGap`→scheduler; `drive_module_dep` is the single drive seam; eval-thread vs pool-worker retry both converge there. Residual: `register_dep` prologue is inlined at 5 caller sites (F7 below) | `process_form.rs:1662-1726`; `eval.rs`; `src/CLAUDE.md §"Cluster-Atomic Orchestration"` |
| 4 | Worker orchestration split across `worker.rs`/`session_v4.rs`/`scheduler.rs` | **Improved, not eliminated** — the S78 in-call-stack restructure removed `process_module_forms`; nice-worker/object compile still on session (`compile_module_object` `session_v4.rs:2482`) while priority loop is worker-side. The conceptual "worker subsystem" is still two-homed | `session_v4.rs:2482`; `scheduler.rs` |
| 5 | `src/lib.rs` exports 18 modules (not a facade) | **Resolved** — `lib.rs` now exposes only 8 `pub` items (5 binary-facing + `cluster`/`worker_pool`/`cache` facade-cited); the remaining ~21 modules are `pub(crate)`. This is the narrowing the baseline asked for | `src/lib.rs:15-92` |
| 6 | Legacy/transitional residue (`session.rs` v3, "wrapping existing CompilationSession") | **Mostly resolved** — `session.rs` renamed `session_setup.rs` with the v3 god-type deleted (FIXME 0109 Wave A verified); residue now is documented vestigial *parameters* not live shims (F6 below) | `src/lib.rs:58-64`; `process_form.rs:459-491` |
| 7 | Historical narrative inline in hot paths increases scan cost | **Regressed / unchanged** — the narrative density is now extreme: `src/CLAUDE.md` is 39 KB and several production modules carry multi-paragraph sprint-history comment blocks. Not a defect, but the baseline's request to move long narratives to design notes was not actioned | `worker.rs:680-734` (54-line comment block); `process_form.rs` passim |

**Reconciliation counts:** Resolved 3 (F1, F5, F6 structurally; F2/F3 "largely") ·
Improved-not-eliminated 2 (F4 worker two-homing, F3 register_dep residue) ·
Regressed/unchanged 1 (F7 inline narrative). No baseline finding got worse in a
correctness sense; the decomposition the baseline's remediations called for largely
landed.

---

## 2. S87 findings (severity-ranked, capped)

### Important

**F-A (Important) — DEF-1 codegen-batch seam does not consult the prelude outer scope.**
`derive_codegen_batch` (`src/worker.rs:599`, body to ~741) enumerates the codegen
batch by scanning **only the current module's own symbol table**
(`tc_modules.get(module)`, `worker.rs:606`) plus names appearing in `program`. It
never reads `prelude_fallback` and never walks the `prelude` module's table. This is
the exact src/-side seat of S86 DEF-1 (ledger `tests/plan/ledger.md:416-438`,
"LOCALIZED at the batch-derivation seam", owner /int): a plain `defn` reached only
through the implicit-prelude glob typechecks (the §8.8.1 fallback surfaces the name)
but its **body never enters the consuming module's batch**, yielding `codegen error
… undefined function: <name>`. The S86 narrow repro
(`spec_08_modules.rs::def1_prelude_provided_defn_called_bare_enters_codegen_batch`)
was the discovery; the structural fix belongs here. *Why it matters:* this seam is
the codegen-time twin of typecheck's `resolve_terminal_entry_or_prelude` — typecheck
consults the prelude outer scope for **resolution**, but codegen-batch derivation
silently re-implements name collection **without** the same fallback, so the two seams
disagree about what is in scope. *Proposed consolidation:* thread `&prelude_fallback`
into `derive_codegen_batch`; when the bit is ON for `module`, also enumerate the
batch-eligible bodies reachable via the prelude outer scope (the body-carrying `Def`s
the glob surfaces), so the codegen-scope query and the typecheck-scope query share one
definition of "what names are reachable here." See §3 for the seam verdict.

**F-B (Important) — JIT vs cache-restore/`--link` host-primitive resolution is two hand-rolled wirings (lens vii; cite FIXME 0407 / DEF-6 family).**
The same job — "make host-exported, slot-less primitive externs (`sconcat`, the Trace
accessors, `catch-runtime-error`) resolvable to compiled code" — is wired twice, by
two different mechanisms:
- **JIT path:** `build_session_jit`/`cranelisp_backend::jit::Jit::new` resolves them
  through the JIT's exported-symbol fallback (`worker.rs:957-966`).
- **Cache-restore/`--link` path:** the cache `Linker` has no such fallback, so
  `register_binary_exported_primitives` (`worker.rs:1059`) hand-rolls
  `dlsym(RTLD_DEFAULT, name)` (`dlsym_host_symbol`, `worker.rs:1091`) for every
  `DefKind::PrimitiveExtern` (`worker.rs:1081`, called at `:1158`).
*Why it matters:* this is precisely the "where `--run` (JIT) and `--link` hand-roll
host callbacks separately" divergence class (`tests/CLAUDE.md §Sustained-load`,
Risk 11) and the DEF-6 root enabler — a divergence here is invisible until a
cache/`--link` run hits a symbol the JIT fallback would have caught. The two paths can
drift silently because no parity guard binds them. *Proposed consolidation:* a single
"host-exported-extern provider" abstraction consumed by both `Jit::new` and the cache
`Linker`, OR (lighter) a parity test asserting the set of names the JIT fallback
resolves equals the set `register_binary_exported_primitives` resolves. This is a
synthesis-level cross-crate item (int + backend + the 0407 ABI question) — backlog,
not in-sprint. Flagged for the Wave-2 /arch synthesis per the SPRINT R2 directive.

**F-C (Important) — `try_cache_hit_load` is a ~254-line god function with ~9 phases.**
`src/process_form.rs:1829`. Validity check → metadata load → codegen-target check →
symbol extraction → platform re-resolve → schema restore → transitive
import/export recursion → scheduler registration → cache record. Exceeds the
`src/CLAUDE.md §Code Structure` ~100-line budget by ~150 and concentrates the most
delicate cache-restore invariants in one block. *Proposed consolidation:* extract
`verify_cache_validity` / `restore_cached_symbol_table` / `reregister_cached_platforms`
/ `recurse_transitive_cache_deps`.

**F-D (Important) — three over-budget orchestration functions in `session_v4.rs`.**
`CompilerSession::new` (`session_v4.rs:747`, ~216 lines: worker spawn +
`SharedState` construction + symbol-table seeding), `compile_module_object`
(`:2482`, ~174 lines), `discover_tests_extern` (`:3058`, ~190 lines: module
iteration + test enumeration). Each well over the ~100-line budget; each has a clean
extraction boundary (the parenthetical sub-phases). *Proposed consolidation:* split
each along its named phases.

**F-E (Important) — over-budget functions clustered in `process_form.rs` per-form chain.**
Beyond F-C: `process_cluster_once` (`:852`, ~150 lines, Pass-0/1/2 orchestration),
`process_regular_form` (`:1318`, ~131), `classify_form` (`:724`, ~128),
`handle_import` (`:1511`, ~125), `register_macro_in_module` (`:1133`, ~116). Six of
seven top functions in the file exceed budget. The file is the densest pipeline-
orchestration module (1,765 corrected LOC, #2 in the workspace); function-budget
overrun is the file's recurring lens-(iii) signature. *Proposed consolidation:* the
extraction targets are mechanical (each is a multi-phase sequence with documented
phase comments); prioritize behind F-C.

**F-F (Important) — over-budget display/handler functions in `repl.rs`.**
`handle_imports` (`src/repl.rs:1006`, ~118 lines, distinct unfiltered vs filtered
branches), `format_def_entry` (`:1754`, ~107, five entry kinds). `dispatch_command`
(`:454`, ~105) is a structural match — acceptable. *Proposed consolidation:* split
`handle_imports` into the two branch helpers; extract `format_constructor_display`
from `format_def_entry`.

**F-G (Important) — prelude-fallback hop logic inlined twice instead of using the canonical lookup (Principle 7).**
`repl.rs` has a canonical `lookup_with_prelude_fallback` (`:559`) used by
`handle_sig`/`handle_doc`/`handle_info` (`:613,624,830`), but the same current→prelude→root
hop is re-inlined in `describe_symbol` (`repl.rs:307-346`, reading
`prelude_fallback.get(...).unwrap_or(false)` at `:322`) and in
`format_eval_result_body` (`:1690-1712`, same pattern at `:1697`). *Why it matters:*
if prelude-fallback semantics change, two off-canonical sites must be found and
updated in lockstep. *Proposed consolidation:* route both through
`lookup_with_prelude_fallback`. (This is the introspection-display analogue of F-A:
the same "consult the prelude outer scope" logic is implemented in several places
rather than one — see §3.)

### Suggestion

**F-H (Suggestion) — dead-code accessors retained behind `#[allow(dead_code)]`.**
`introduce_module_blank` (`session_v4.rs:1123`, zero call sites),
`cached_module_remove` (`scheduler.rs:1404`, zero call sites — `re_register_module`
calls the setter directly), plus `#[allow(dead_code)]` at `session_v4.rs:1378` and
`scheduler.rs:1448`. The S87 Wave-0 removal of the dead `Introspection.disasm` field
+ `symbol_disasm()` accessor (FIXME 0418, confirmed gone — no `symbol_disasm`/`.disasm`
match in `session_v4.rs`) set the precedent: prefer deletion over a dead-code allow.
*Proposed:* delete each or, if a facade contract requires the surface, justify with a
comment naming the consumer.

**F-I (Suggestion) — vestigial `extra_jit_symbols` parameter threaded through the JIT-codegen pair.**
`worker.rs:783,838` carries `extra_jit_symbols: &[(String, *const u8)]` through
`inline_jit_codegen_for_module`/`_for_names`, explicitly nulled at `:850`
(`let _ = (extra_jit_symbols, shared_state);`) since the S76 W-Collapse retired the
trace-symbol threading. A `*const u8`-bearing dead parameter is a latent foot-gun
(lens vii — host-pointer plumbing). *Proposed:* drop the parameter and its
pass-through; it threads a raw fn-pointer slice that goes nowhere.

**F-J (Suggestion) — `register_synth_adt` is a documented cross-crate mirror of typecheck (lens i/v cross-crate-duplication seed).**
`src/bootstrap.rs:131` (~131 lines, also over budget) reconstructs
`cranelisp_typecheck::register_type_def_with_ctor_infos`'s body inline (product/sum
discrimination, GOT-slot allocation, ctor-scheme building), confirmed by its own
comment and `src/CLAUDE.md`. This is intentional (typecheck's `register_type_def` is
no longer reachable; FIXME 0242), but it is a genuine two-homed authority that will
drift if either side's ADT-registration logic changes. *Proposed:* not an in-sprint
fix; record as a divergence-watch item — the synthetic-mount and typecheck
ADT-registration are candidates for a shared `cranelisp-types` helper so both
construct ADT entries through one builder. Backlog / synthesis input.

**F-K (Suggestion) — single non-test `.unwrap()` on a live-module read.**
`process_form.rs:3100` (`clear_module_codegen`) `.unwrap()`s
`ctx.symbol_tables.get(&ctx.current_module)`. The current module exists by
construction, but `src/CLAUDE.md §Error Handling` forbids `unwrap()` in pipeline
code; an `unreachable!("invariant: …")` or `ok_or_else` is the house style. *Proposed:*
swap to `unreachable!` with the invariant text. (Broad sweep otherwise clean: the
agents found all other non-test `unwrap`/`expect`/`panic` either test-scoped or
already `unwrap_or*`/`unreachable!("invariant: …")`.)

**F-L (Suggestion) — F7 baseline residue: `register_dep` prologue inlined at 5 sites.**
`register_dep` is called with a near-identical file-resolve→parse→hash→source-stash
prologue at `process_form.rs:1598,1709,2205,2376,3015`. Idempotent-on-retry and each
carries caller-specific error framing, so this is not a defect — but it is the
remaining shard of baseline F3 (dependency-registration spread). *Proposed:* extract
the shared prologue, keep error framing at the caller. Low priority.

---

## 3. DEF-1 seam verdict — one seam, or many?

**Verdict: it is one logical seam — "consult the prelude outer scope when resolving a
bare name" — implemented at several uncoordinated sites, and src/ owns one of the
sites the canonical resolution seam does NOT cover.**

- The **resolution** seam is consolidated and lives in typecheck:
  `resolve_terminal_entry_or_prelude` (`crates/cranelisp-typecheck/src/checker.rs:1451`,
  also `program.rs:3272`) is typecheck's single bare-name+prelude chokepoint, and on
  the int side macro **recognition** funnels through one site —
  `expander.rs::recognize_macro_head` (`src/expander.rs:267`), the only place in src/
  that reads `prelude_fallback` for *recognition*, called by both
  `SymbolTableMacroResolver` and `ReadOnlyMacroResolver`. Those are healthy: one seam,
  two thin callers.
- But the **prelude_fallback bit is read at ~10 independent src/ sites** (grep:
  `expander.rs:300`, `eval.rs:489`, `repl.rs:322/574/1697/...`, `process_form.rs`
  several, `worker.rs` threading) — each its own consultation. Most are correct
  (recognition, introspection display), but **two are off-canonical re-inlines**
  (F-G) and **one chokepoint omits the consultation entirely**: `derive_codegen_batch`
  (F-A). The codegen-batch derivation collects names from the current module's table
  only, so it disagrees with the typecheck resolution seam about reachability — that
  disagreement *is* DEF-1.

So the answer to the SPRINT seed ("is the orchestration wiring N chokepoints or one
seam?"): the **intent** is one seam, the **implementation** is N consultations, and
the DEF-1-class risk is exactly the sites that should consult the outer scope but
re-derive scope independently (codegen batch) or re-inline the hop (display). The
durable fix is to make codegen-scope and typecheck-scope ask the *same* "what is
reachable in this module, including the prelude outer scope" question — i.e. thread
`prelude_fallback` into `derive_codegen_batch` and route the `repl.rs` re-inlines
through `lookup_with_prelude_fallback`. This is the cross-crate single-resolution-seam
question the Wave-2 /arch synthesis owns; src/ contributes F-A + F-G as its evidence.

## 4. Host-callback / JIT-vs-`--link` divergence observation (lens vii)

Confirmed real and structural, not incidental (F-B). The host-exported slot-less
primitive externs are made reachable to compiled code by **two separate wirings**:
the JIT's exported-symbol fallback (`build_session_jit`, `worker.rs:957`) and the
cache/`--link` `Linker`'s hand-rolled `dlsym(RTLD_DEFAULT, …)`
(`register_binary_exported_primitives` + `dlsym_host_symbol`, `worker.rs:1059/1091`,
called `:1158`). The same `discover-tests` extern is host-promised via
`Jit::define_symbol` (`worker.rs:961`) with no `--link` equivalent because it is
REPL-only — itself a mode asymmetry, intentional but worth a parity note. This is
the DEF-6 root-enabler pattern (`--run` and `--link` hand-roll host callbacks
separately, no parity guard) and the same family as FIXME 0407. The lighter
mitigation is a parity test (the JIT-resolvable set == the dlsym-resolvable set);
the durable mitigation is a single host-extern provider both backends consume. Feeds
the Wave-2 synthesis per SPRINT R2 (cite 0407, stays open, not actioned in-sprint).

## 5. Prior-findings status counts

- Baseline findings reconciled: **7 / 7**.
- **Resolved:** 3 (F1 session god-file split, F5 lib.rs narrowed to 8 pub items,
  F6 v3 residue / `session.rs`→`session_setup.rs`).
- **Largely resolved:** 2 (F2 worker god-file + macro-clause mirror collapse,
  F3 dependency-registration → `process_cluster`/`drive_module_dep` single seam).
- **Improved, not eliminated:** 1 (F4 worker orchestration still two-homed:
  priority loop worker-side, object/nice compile session-side).
- **Regressed / unchanged:** 1 (F7 inline historical narrative density — higher now).
- New S87 findings: **12** (F-A … F-L) — 7 Important, 5 Suggestion. None Blocker
  (the one DEF-1-class correctness item, F-A, has a committed S86 repro and a named
  resolver; it is a known-defect guard awaiting fix, not a new regression).
