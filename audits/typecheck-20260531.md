# cranelisp-typecheck structural + architectural audit — 2026-05-31

## Lineage note

**Clean-room audit.** Findings below were derived **independently** from the
configuration set (facade + Decisions + Principle 17 + conventions + open
FIXMEs) and a full source walk of `crates/cranelisp-typecheck/src/`, *before*
reading any prior `audits/typecheck-*.md`. The prior audit
(`typecheck-20260530.md`) was read only at the final step; the
"## Reconciliation vs 2026-05-30 audit" section dispositions it honestly without
retrofitting.

**Method.** Configuration-grounded derivation + five-lens completeness walk:
1. Public surface vs facade (`facades/typecheck.md` + `public-api.txt`).
2. Structural duplication.
3. Function/param-size + naming discipline vs `src/CLAUDE.md`.
4. Error-handling discipline (unwrap/expect/panic vs `?`/`unreachable!`).
5. Configuration walk — every type/fn/module identifier named in
   facade/Decisions/Principles checked for existence + stated shape in source;
   Principle-17 module-locality (no universe scans).

Each finding carries five blocks: facade/spec/Decision expects · source does
(file:line) · design intent (Decision/Principle/FIXME) · difference ·
disposition (action + severity + typecheck-internal vs cross-crate).

**Scope exclusions (per task constraints).** `int` is mid-migration and does not
compile — that is out of scope; no `int` breakage is reported as a typecheck
defect. No cargo build/test was run. The audit is read-only except this file.

## State summary

The crate is **architecturally sound and Principle-17-clean**: the production
typechecker performs zero module-universe scans (every `self.modules` access is a
single-key `get`/`get_mut`/`insert`/`remove`/`contains_key`), trait-impl storage
follows Decision 45 (write to trait-defining module; importers chain-follow), the
single read/write wrapper-pair invariant holds, and error discipline is clean
(production paths use `?` and invariant-encoded `unreachable!`; bare
`unwrap`/`panic!` appear only under `#[cfg(test)]`). The live divergences are
**facade-edge debts already owned by open FIXMEs** (module_aliases threading +
ResolveError surface, FIXME 0240) plus two oversize production functions and one
silent-drop branch in `parsed_to_top_level`. No structural debt, no duplication,
no locality violation in production.

## Current metrics

| File | Total LOC | Production | Test | Notes |
|---|---:|---:|---:|---|
| adt.rs | 1217 | ~620 | ~597 | register/lookup/exhaustiveness |
| builtins.rs | 2394 | 0 | 2394 | **entire module `#[cfg(test)]`** (FixtureBuilder, S73) |
| checker.rs | 2144 | 2144 | — | + checker/test_support.rs 544, checker/tests.rs 1114 |
| cluster.rs | 368 | ~280 | ~88 | ClusterContext, SymbolTableRead/Mut |
| form.rs | 790 | ~290 | ~500 | `check_forms` entry |
| infer.rs | 943 | 943 | — | + infer/tests.rs 2186 |
| lib.rs | 64 | 64 | — | facade exports |
| program.rs | 2059 | 2059 | — | + program/tests.rs 4116 |
| resolve.rs | 406 | ~200 | ~206 | closure-injected terminal resolution |
| result.rs | 178 | 178 | — | CheckResult / CheckError / ResolveError |
| scheme.rs | 172 | ~60 | ~112 | instantiate / generalize / mono |
| scope.rs | 166 | ~80 | ~86 | ScopeStack push/pop |
| trace.rs | 161 | 161 | — | trace hooks |
| traits.rs | 2019 | 2019 | — | + traits/tests.rs 1072, primitive_dispatch_tests.rs 83 |
| unify.rs | 339 | ~150 | ~189 | HM unification core |

Largest production functions (effective body, blank/comment-stripped):
`finalize_check_result_inner` ~193 (program.rs), `register_trait_impl` ~127
(traits.rs), `check_forms` ~120 (form.rs), `check_form_body_multi_sig` ~110
(program.rs), `check_form_body_single_defn` ~95 (program.rs).

---

## Findings

### Finding 1 — `check_forms` signature omits `module_aliases`, uses `&DashMap` not `&SymbolTables` (HIGH, cross-crate, OWNED)

**Facade/Decision expects.** `facades/typecheck.md` + Decision 44 (third
amendment) prescribe:
`check_forms(parsed, ctx: &mut ClusterContext<'_,C,L>, symbol_tables: &SymbolTables<C,L>, module_aliases: &ModuleAliases) -> Result<(), CheckError>` — 4 params, a `&SymbolTables` newtype, and an explicit `&ModuleAliases`.

**Source does.** `form.rs::check_forms` (entry ~line 1) + `public-api.txt`: takes
`parsed, ctx, symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C,L>>` — 3
params, the raw `DashMap`, no `module_aliases`. Aliases are instead read/written
through `state.module_aliases` (a `HashMap` on `CheckState`, written by
`register_imports` at `checker.rs:1299`).

**Design intent.** Decision 44 third amendment + Decision 47 (FQ at resolved-stage
boundaries). The `&SymbolTables` newtype + threaded `&ModuleAliases` are the
target boundary shape so the orchestrator owns alias state rather than the
per-call `CheckState`.

**Difference.** Boundary type is the raw collection (newtype not yet introduced);
alias state lives on call-frame state, not threaded as a parameter.

**Disposition.** Already filed + explicitly deferred: **FIXME 0240** (A1/A4) names
the module_aliases threading as breaking for `src/worker.rs` (~6 sites) +
`src/session.rs` (~1) and defers it pending the int migration. No new action;
verify FIXME 0240 carries the `&SymbolTables`-newtype sub-item (it currently
frames the threading, less so the newtype). Severity HIGH because it is the
crate's primary boundary; cross-crate; owned.

### Finding 2 — `register_imports` / `register_exports` free fns lack `module_aliases` param (HIGH, cross-crate, OWNED)

**Facade expects.** `facades/typecheck.md`: `register_imports`/`register_exports`
take `&ModuleAliases`.

**Source does.** `checker.rs:1985`/`2004` free-fn wrappers take
`(symbol_tables, next_id, state, specs)` — no `module_aliases`. The alias map is
mutated on `state.module_aliases` inside (`checker.rs:1299`).

**Design intent.** Same as Finding 1 — Decision 44/47 orchestrator-owned alias
threading.

**Difference.** Aliases flow through call-frame `CheckState`, not an explicit
boundary parameter.

**Disposition.** Same owner as Finding 1 — **FIXME 0240**. Single threading change
lands all three signatures together. No new action; HIGH; cross-crate; owned.

### Finding 3 — `ResolveError` is public but not named in the facade "Types originated here" (MED, cross-crate, OWNED)

**Facade expects.** `facades/typecheck.md` "Types originated here" enumerates the
crate's owned public types; `ResolveError` is **not** listed.

**Source does.** `result.rs` defines `pub enum ResolveError` (5 variants:
`TraitNotFound`/`TypeNotFound`/`ConstructorNotFound`/`QualifiedModuleUnknown`/
`PrivateInaccessible`) with `From` projections into `CheckError`; `lib.rs` exports
it; `public-api.txt` confirms it public.

**Design intent.** FIXME 0172 (CLOSED source-side, S72 W3b) renamed the resolver
fns to `resolve_type`/`resolve_trait`/`resolve_constructor`; `ResolveError` is the
result type of that surface. Decision 47 FQ-binding cascade implies the facade
text should enumerate it.

**Difference.** Source surface evolved (ResolveError landed); facade enumeration
is stale — an un-cascaded edge per the Decision-cascade discipline.

**Disposition.** Facade-text catch-up, owned by **FIXME 0240** (names the
rename-cascade + facade staleness). No new action; MED (compiles, surface is
real, only the doc lags); cross-crate (facade is `/arch`-owned); owned.

### Finding 4 — `parsed_to_top_level` silently drops `ParsedEntry::Macro` / `Constructor` via `None` + `_ => None` catch-all (MED, typecheck-internal, NEW)

**Spec/facade expects.** `check_forms` consumes `Vec<ParsedEntry>`; every entry
that reaches typecheck should be either checked or explicitly, legibly rejected.

**Source does.** `form.rs:284-287`:
`ParsedEntry::Macro { .. } | ParsedEntry::Constructor { .. } => None,` plus a
catch-all `_ => None` for `#[non_exhaustive]` forward-compat. Entries returning
`None` are filtered out of the form list with **no diagnostic** — they vanish.

**Design intent.** Macros are expanded upstream (frontend) and constructors are
synthesised by `register_type_def`, so neither should arrive as a standalone
`TopLevel` here. The `None` is intentional. But the **`_ => None` catch-all** is a
silent-drop hazard: a future `ParsedEntry` variant would be dropped without any
signal, masking a frontend/typecheck contract break (the class of bug Principle-17
and the "no silent universe behaviour" discipline guard against).

**Difference.** Correct-today behaviour, but the catch-all converts a future
contract violation into silent data loss rather than a loud failure.

**Disposition.** **typecheck-internal.** Replace `_ => None` with an explicit
arm per known-skipped variant + a debug-assert/trace on the truly-unexpected
case (or `unreachable!("invariant: variant X is frontend-expanded")`), so a new
variant forces a compile-time match-exhaustiveness decision rather than silent
drop. Severity MED (latent, not active). NEW — not in scope of any open FIXME.

### Finding 5 — Two production functions materially exceed the ~100-line convention (LOW, typecheck-internal, NEW)

**Convention expects.** `src/CLAUDE.md`: functions ~100 lines; decompose larger
ones into named helpers.

**Source does.** `program.rs::finalize_check_result_inner` ~193 effective body
lines; `traits.rs::register_trait_impl` ~127. (`check_forms` ~120 and
`check_form_body_multi_sig` ~110 are borderline; the `current_module` 142 raw-line
count was doc-comment inflation — its body is small.)

**Design intent.** The convention favours legibility + testability; `infer.rs` is
the model (one ~15-40-line method per `Expr` variant).

**Difference.** Two post-pass orchestration functions accreted past the threshold;
both are sequential phase-drivers (finalize: drain accumulator → mono → overload →
writeback; register_trait_impl: resolve trait home → validate methods → write
`impl$..$..`).

**Disposition.** **typecheck-internal.** Extract named sub-phase helpers
(`finalize_check_result_inner` → per-pass helpers; `register_trait_impl` →
`resolve_trait_home` / `validate_impl_methods` / `write_impl_entry`). Severity LOW
(no correctness/locality issue; pure legibility). NEW.

### Finding 6 — Default-rooting to `"user"` in dead-code-gated constructor helpers (LOW, typecheck-internal, latent)

**Principle 17 expects.** `user` has no special status; no probe-user-as-fallback;
short-name resolution is current-module + chain-follow only.

**Source does.** `checker.rs` `lookup_constructor_type` / `is_internal_constructor_check`
default-root to `"user"` when no module context is supplied. Both are
`#[allow(dead_code)]` test-only helpers (not on any production path).

**Design intent.** Principle 17 forbids user-as-fallback in production resolution.
These helpers predate the locality refactor (Decision 46 α) and survive only
because tests reference them.

**Difference.** The `"user"` default contradicts Principle 17 *if* either helper
were ever wired into production; today they are dead-code-gated, so the violation
is latent, not live.

**Disposition.** **typecheck-internal.** Delete the dead helpers, or have them take
an explicit `&ModuleFullPath` (no default). Severity LOW (latent; dead-code-gated).
Latent — surfaced by the clean-room locality walk.

---

## Positives confirmed (5th-lens configuration walk)

- **Principle 17 — production is scan-free.** Every `self.modules.*` in
  checker/adt/infer/traits/program is single-key (`get`/`get_mut`/`insert`/
  `remove`/`contains_key`). No `transitive_import_closure`, no universe iteration.
  Chain-follow is bounded by `IMPORT_CHAIN_DEPTH_LIMIT` (`chain_follow_to_home`).
- **Decision 45 — trait-impl storage compliant.** `register_trait_impl` resolves
  the trait's home (`resolve_trait` → chain-follow) and writes
  `impl$FQTypeName$FQTraitName` into the trait-defining module's table via
  `symbol_table_mut_in`; importers chain-follow (Pattern B). `ImplRegistry` is
  gone.
- **Single read/write wrapper-pair invariant.** Both `ClusterContext` and
  `TypeCheckEnv` accessors return exactly `SymbolTableRead` / `SymbolTableMut`
  (cluster.rs + checker.rs:389); `view()` is staging-first union in Cluster mode.
- **Error discipline.** Production uses `?` throughout; the only production
  `unreachable!` calls are invariant-encoded (`checker.rs:395/432/449/1390`,
  `cluster.rs:107/116/138`). The three production `.expect()` (`traits.rs:36/818`,
  `program.rs:919`) are invariant-documented with spec references. All bare
  `.unwrap()`/`panic!` are inside `#[cfg(test)]`.
- **Builtins fully test-gated.** `mod builtins` is `#[cfg(test)]` (lib.rs:31); the
  2394-line file is entirely FixtureBuilder test-support after the S73 deletion of
  `register_builtins` (FIXME 0241). No production builtin-registration surface
  remains in typecheck — correct per Decision 48 + BC §2.
- **`infer.rs` per-variant dispatch.** One method per `Expr` variant, each
  10-40 lines; the shared `instantiate_ctor` helper (S70 Trigger 2) deduplicates
  pattern-match vs constructor-call typing. Exemplary.
- **`for_each_child_expr` single child-enumeration source** (program.rs:52) — the
  one place `Expr` child structure lives; every walker routes through it.

## FIXME tracking map

| FIXME | Target | Status | Relates to finding |
|---|---|---|---|
| 0240 | /arch | open | Findings 1, 2, 3 (module_aliases threading + `&SymbolTables` newtype + ResolveError/rename facade catch-up) |
| 0172 | /typecheck | CLOSED source-side (S72 W3b) | Finding 3 (resolver rename landed; facade text lag is 0240) |
| 0241 | /arch | open (Tier-1 landed; broader vocab deferred) | builtins.rs deletion confirmed; no live finding |
| 0243 | /typecheck | open (user-deferred S73) | heavy test-fixture debt; no production finding |
| 0239 | /arch | open | instantiate-from-source; settled to "construct from builders"; no production finding |
| 0033 | /typecheck | open | MonoDefn redundant side-maps (not re-surfaced this walk — recommend re-confirm) |
| 0043 | /typecheck | open | ResolvedCall autocurry count (test-coverage; not a structural finding) |

## Prioritized remediation

1. **(HIGH, FIXME 0240)** Thread `module_aliases: &ModuleAliases` through
   `check_forms` + the `register_imports`/`register_exports` free fns, and
   introduce the `&SymbolTables<C,L>` newtype boundary (Findings 1, 2). Confirm
   0240 enumerates the newtype sub-item, not just the alias threading. Single
   change-set; orchestrator-owned per Decision 44.
2. **(MED, FIXME 0240)** Add `ResolveError` to `facades/typecheck.md` "Types
   originated here" (Finding 3) — un-cascaded Decision-47 edge.
3. **(MED, typecheck-internal, NEW)** Replace the `_ => None` catch-all in
   `parsed_to_top_level` (form.rs:286) with explicit per-variant arms + a loud
   failure on the genuinely-unexpected case (Finding 4) — convert silent drop into
   compile-time/loud signal.
4. **(LOW, typecheck-internal)** Decompose `finalize_check_result_inner` (~193) and
   `register_trait_impl` (~127) into named sub-phase helpers (Finding 5).
5. **(LOW, typecheck-internal)** Delete or de-default the `"user"`-rooting dead-code
   constructor helpers (Finding 6).

## Agent traps (guidance for the resolving skill)

- **Do NOT "fix" the `&DashMap` → `&SymbolTables` or the missing `module_aliases`
  in isolation.** They are a single coordinated boundary change owned by FIXME
  0240, breaking ~7 `int` call sites; landing them piecemeal red-bars `int` worse.
  Follow facade-first migration discipline (push the typecheck edge to target,
  accept broken `int`, fix consumers wave-by-wave).
- **`int` does not compile — that is expected and out of scope.** Never read an
  `int` call site as evidence of typecheck's canonical surface; the facade is
  definitive (per `feedback_facade_definitive_not_consumer_source`). `int` is
  mid-migration.
- **`builtins.rs` is `#[cfg(test)]` in full.** Its 2394 lines are fixture
  machinery, not production. Do not audit it for production discipline or
  Principle-17 locality — it is allowed to seed a synthetic world. The heavy-fixture
  debt is explicitly user-deferred (FIXME 0243); do not "fix" it unbidden.
- **`unreachable!` and invariant `.expect()` are the sanctioned discipline**, not
  defects. `src/CLAUDE.md` prescribes `unreachable!("invariant: ...")` over silent
  fallthrough; the production sites here are correct.
- **The `"user"`-rooting helpers (Finding 6) are dead-code-gated.** Do not wire
  them into production as a "convenience" — that would introduce a live Principle-17
  violation. Delete or require explicit module.
- **Decision 45 is Pattern B (chain-follow), not closure-walk.** When touching
  `register_trait_impl` / impl discovery, preserve chain-follow-to-trait-home; do
  not reintroduce an `ImplRegistry` or a transitive closure scan.

## Bottom line

The typechecker's **internals are in good architectural health** — locality-clean,
duplication-free, error-disciplined, with exemplary per-variant inference. The only
HIGH-severity items are the **facade-edge boundary debts already owned by FIXME
0240** (module_aliases threading + `&SymbolTables` newtype + ResolveError facade
catch-up), all blocked behind the `int` migration and correctly deferred. The two
NEW typecheck-internal items — the `parsed_to_top_level` silent-drop catch-all
(MED) and two oversize post-pass functions (LOW) — are small, owned, and
actionable without cross-crate coordination. No new structural debt; no
Principle-17 production violation.

---

## Reconciliation vs 2026-05-30 audit

*(This section authored after reading `audits/typecheck-20260530.md` — clean-room
findings above were fixed before this read.)*

**Headline divergence: the codebase moved between the two audits.** The 2026-05-30
audit observed Phase-B-close state with file sizes roughly **double** what I
measured (program.rs 7,006 vs my 2,059; checker.rs 3,904 vs 2,144; traits.rs
3,220 vs 2,019; builtins.rs 2,863 vs 2,394). Between the two dates, **S73 Tier-3
landed** (commit `e7470e1` + the `check_program`/`check_repl_input` deletion +
test-module splits into `*/tests.rs` sibling files). My prod-only figures and the
prior prod+test figures are not directly comparable, and — more importantly —
**three of the prior audit's six structural findings were closed or substantially
reduced by that intervening work.** I report this divergence as real, not as a
methodology gap: my clean-room walk saw a different (later) codebase.

### Disposition of the 2026-05-30 reconciliation table (its findings of the 2026-04-23 set)

| Prior # | Prior status (2026-05-30) | My clean-room finding (2026-05-31) | Disposition |
|---|---|---|---|
| 1 — `program.rs` multiple pipelines | PERSISTS (+ cluster shim layer) | **`check_program`/`check_program_inner`/`check_repl_input`/`_inner` are GONE.** Only `check_via_forms` (`#[cfg(test)]` driver, program.rs:1267) survives. Public + internal entry is single: `check_forms`. | **CLOSED** since 2026-05-30. The intervening pipeline-collapse landed. I did not surface this as a finding because the multiplicity no longer exists. `parsed_to_top_level` + `map_cranelisp_error` remain but are thin per-form translation, not parallel pipelines (I flag only the `parsed_to_top_level` silent-drop, my Finding 4). |
| 2 — duplicated `Expr` traversal | PERSISTS (no shared walker) | **`for_each_child_expr` + `_mut` now EXIST** (program.rs:52/101) and are the single child-enumeration source; `resolve_deferred_trait_calls` (infer.rs:605), `collect_constrained_calls` (program.rs:2001) route through them. | **CLOSED** since 2026-05-30 (this was the prior audit's own remediation #4, now landed). `apply_subst_to_expr`/`annotate_expr_from_maps` still hand-roll, but the shared helper exists. I list `for_each_child_expr` as a positive. |
| 3 — dual `traits.rs` impl-method flows, duplicated tails | PERSISTS | `check_impl_method_with_sig` (578) + `check_hkt_impl_method` (801) still coexist, **BUT `finalize_impl_method_writeback` (723) now factors the shared writeback tail.** | **PARTIALLY CLOSED.** Tail factored; the two front-half flows remain. I did not raise this as a finding (the residual dual-flow is legible HKT-vs-non-HKT branching, not a duplication debt). RE-SEVERITY: prior HIGH → not-a-finding. |
| 4 — manual `ModuleEntry::Def` construction (159 sites) | WORSE (132→159) | **Raw `ModuleEntry::Def {` literals dropped to 78; `ModuleEntry::def(` builder appears 15×.** The Tier-1 `DefBuilder` (FIXME 0241, S73) landed and is being adopted. | **PARTIALLY CLOSED + actively improving.** Builder exists and is in use; migration of remaining literals is in flight. I did not raise it as a finding (mechanism exists; this is migration progress, owned by 0241/0242, much of the residue is in `#[cfg(test)]` builtins.rs). RE-SEVERITY: prior WORSE → in-progress-resolution. |
| 5 — scattered full-scan lookups; `known_type_names` | PARTIALLY CLOSED (`known_type_names` deleted; whole-module scans persist) | `known_type_names*` confirmed gone. The "whole-module scans" (`lookup_type_def_in_module` 489, `lookup_trait_decl_in_module` 1682, `has_impl_in_module` 1752) are **single-module-scoped** (`read_view(module_path)`), NOT universe scans. | **CLOSED on the locality axis.** Per Principle 17, bulk introspection *of the current/named module* is a sanctioned access shape — these are intra-module iterations, not the universe scans Principle 17 forbids. The prior audit's framing as a residual debt over-counts: a `TypecheckIndexView` facade is **not** owed; the helpers are compliant. DIVERGENCE: I disposition this as a non-issue where the prior audit left it as Low-Med residue. |
| 6 — large mixed prod/test files | PERSISTS | Test modules are now **split into sibling files** (`checker/tests.rs`, `infer/tests.rs`, `program/tests.rs`, `traits/tests.rs`); `builtins.rs` is **fully `#[cfg(test)]`**. Production files are correspondingly smaller (program.rs 2,059 prod). | **CLOSED** since 2026-05-30 (prior remediation #6 landed). Production files remain large but are no longer prod/test-mixed. I raise only true oversize *functions* (my Finding 5), a narrower and more accurate concern than "large files". |

### Disposition of the 2026-05-30 nits N1–N5

| Nit | Prior | My finding | Disposition |
|---|---|---|---|
| N1 — `form.rs` stale module doc ("Wave 3b follow-up") | Minor doc-currency | The form.rs doc I read (lines 1-20 region) is current; no "Wave 3b follow-up" stale text observed in the surviving doc. | **CLOSED** (doc refreshed in intervening work) or relocated. Did not re-surface. |
| N2 — `result.rs` rustdoc references singular `check_form`/`TypeChecker::check` | Minor doc-currency | Did not specifically re-walk result.rs rustdoc prose for this string; result.rs structure is current (CheckResult/CheckError/ResolveError). | **PERSIST (unverified)** — recommend `/typecheck` confirm result.rs rustdoc prose names `check_forms`. Low. |
| N3 — `cluster.rs` `panic!` vs `checker.rs` `unreachable!` mismatch | Nit | **`cluster.rs:107/116/138` now use `unreachable!`** (not `panic!`); harmonized with checker.rs. | **CLOSED.** The invariant guards match convention. I list this under positives (error discipline). |
| N4 — `check_forms`/module_aliases facade↔baseline drift (FIXME 0240) | Important, tracked | **AGREE — my Findings 1+2+3.** Independently re-derived from facade + public-api.txt. | **PERSIST + AGREE.** Same root (FIXME 0240). |
| N5 — `result.rs` 0 unit tests (accept) | Accept | Concur; pure data + `From` conversions. | **AGREE (accept).** Not a finding. |

### Prior findings I did NOT surface (because they are closed)

Prior structural findings 1, 2, 6 (and the N1/N3 nits) — all closed by the
S73-era intervening work, so they correctly do not appear in my clean-room set.
The prior audit's bottom-line ("the deeper consolidation is the dominant
outstanding maintainability question") is **largely superseded**: the pipeline
collapse, the shared `Expr` walker, the writeback-tail factor, the `Def` builder,
and the test-file split all landed or are in flight. The prior audit's central
thesis was addressed by the work it recommended.

### Findings I surfaced that the prior audit did NOT

- **My Finding 4** (`parsed_to_top_level` `_ => None` silent-drop catch-all) — the
  prior audit mentioned `parsed_to_top_level` only as a "shim" symptom of the
  pipeline-multiplicity thesis (its row 1), not as a silent-drop hazard in its own
  right. With the pipelines now collapsed, the residual catch-all is the
  substantive concern, and it is NEW relative to the prior framing.
- **My Finding 6** (`"user"`-rooting dead-code constructor helpers) — not in the
  prior audit. Latent Principle-17 smell, dead-code-gated.

### Honest divergence summary

The two audits **largely agree on the one HIGH live item** (module_aliases /
`check_forms` boundary, FIXME 0240 — prior N4, my Findings 1-3). They **diverge on
the structural thesis**: the prior audit's six-finding consolidation backlog is, in
my clean-room view of the later codebase, mostly **closed or in-flight**, and its
"whole-module scan" residue (Finding 5) I disposition as **Principle-17-compliant,
not a debt**. This divergence is attributable to (a) the S73-era code changes
between the two dates and (b) a stricter reading of Principle 17's
"bulk-introspection-current-module-only" allowance. I did not retrofit my findings
to match the prior set; where the prior audit's concern no longer holds in source,
I marked it CLOSED with the anchor rather than carrying it forward.
