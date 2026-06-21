# cranelisp-typecheck — Stage-B deep audit (Sprint 87)

> **What this is.** The S87 Stage-B per-crate deep audit for `cranelisp-typecheck`,
> authored by `/review`. It is a **delta + currency check** against the deep
> baseline `audits/typecheck-20260531.md` (the latest of three generations:
> `20260423` → `20260530` → `20260531`), NOT a from-zero re-audit. Method:
> seven-lens checklist (duplication / dead paths / function-budget / RC-symmetry /
> resolution-seam consolidation / interim-arch residue / cross-crate host-callback
> hygiene) mapped onto the baseline's finding taxonomy so "still-open / regressed /
> resolved" is a true diff (R5a same-instrument requirement).
>
> **Scope.** Production code only. Deepest-scrutiny modules per `audits/loc-s87.md`:
> `program.rs` (1966 prod), `traits.rs` (1718, ~1% inline test — densest),
> `checker.rs` (1095), `infer.rs` (785, ~0% test). `builtins.rs` is 100%
> `#[cfg(test)]` test-support (corrected LOC = 1) — skipped as production per the
> baseline + LOC pre-pass. READ-ONLY on code.

---

## 0. Headline

The crate **moved substantially and favourably since 2026-05-31.** The baseline's
three HIGH-severity live items — all owned by **FIXME 0240** (the `check_forms`
boundary: `module_aliases` threading + `&SymbolTables` newtype + `ResolveError`
facade catch-up) — are **RESOLVED.** FIXME 0240 is **gone from the store**
(`design/arch/fixmes/` no longer contains it, nor 0033/0043/0239/0241/0243), the
`int` migration completed (the crate compiles on the Stage-A green base), and the
boundary now matches the facade. What remains is a thin residue of **LOW-severity
typecheck-internal** items (oversize phase-driver functions; one silent-drop
catch-all; one dead-code "user"-default helper) plus one **cross-crate naming
finding** seeded in Wave 0 (the FQ-naming "no impl" renderers). The crate is
architecturally sound: Principle-17-clean (zero production universe scans),
single-seam prelude fallback (DEF-1 verdict: **one gate, correctly wired**),
single `Expr` child-enumeration source, disciplined error handling.

---

## 1. Baseline reconciliation (every prior finding → status)

| Prior # (20260531) | Severity | Prior summary | S87 status | Evidence |
|---|---|---|---|---|
| **F1** | HIGH (cross-crate, owned) | `check_forms` omits `module_aliases`, takes raw `&DashMap` not `&SymbolTables` | **RESOLVED** | `form.rs:96` takes `symbol_tables: &SymbolTables<C, L>`; `form.rs:97` takes `module_aliases: &ModuleAliases`. `SymbolTables<C,L>` type alias materialised in `cranelisp-types` (`lib.rs:42`). FIXME 0240 deleted from store. |
| **F2** | HIGH (cross-crate, owned) | `register_imports`/`register_exports` free fns lack `module_aliases` | **RESOLVED (by removal)** | These are no longer typecheck's public free fns — import/export registration was struck from the typecheck surface entirely (`ParsedEntry` has no Import/Export variant; it is now frontend's StructuralDecl concern — facade audit s69 supersession note, line 3). They survive only as `TypeCheckEnv` methods. |
| **F3** | MED (cross-crate, owned) | `ResolveError` public but absent from facade "Types originated here" | **RESOLVED (by relocation)** | `ResolveError` **migrated to `cranelisp-types`** (`result.rs:59-68`: typecheck's `CheckError` now *projects from* `cranelisp_types::ResolveError` via `From`). It is no longer a typecheck-owned public type, so the facade omission is moot. |
| **F4** | MED (typecheck-internal, NEW) | `parsed_to_top_level` `_ => None` catch-all silently drops entries | **STILL OPEN** | `form.rs:510-512`: `ParsedEntry::Macro \| Constructor => None` then `_ => None`. Unchanged. Latent forward-compat hazard. |
| **F5** | LOW (typecheck-internal, NEW) | Two oversize fns (`finalize_check_result_inner` ~193, `register_trait_impl` ~127) | **STILL OPEN, scope widened** | `finalize_check_result_inner` now ~150 (reduced but still >100); `register_trait_impl` ~127. Audit re-measure surfaced **more** over-budget fns — see Finding S87-2. |
| **F6** | LOW (typecheck-internal, latent) | `lookup_constructor_type` / `is_internal_constructor_check` dead-code helpers default-root to `"user"` (Principle-17 smell) | **PARTIALLY RESOLVED** | `is_internal_constructor_check_in_module` (`checker.rs:725`) now takes an **explicit** `&ModuleFullPath` — no `"user"` default. But `lookup_constructor_type` (`checker.rs:657-659`) **still** defaults to `ModuleFullPath::from("user")`, still `#[allow(dead_code)]`. Its production caller was retired (S79 Option 3a); it survives only for `#[cfg(test)]`. |

**Older lineage (20260530 / 20260423) findings already dispositioned by 20260531:**
the multi-pipeline `program.rs` (old F1), duplicated `Expr` traversal (old F2),
dual `traits.rs` impl flows (old F3), 132-site manual `ModuleEntry::Def` (old F4),
scattered full-scan lookups (old F5), mixed prod/test files (old F6) — all CLOSED
or in-flight as of 20260531 and re-confirmed CLOSED here (pipeline single =
`check_forms`; `for_each_child_expr` is the single walker; test files are sibling
`*/tests.rs`; production is scan-free). No regression on any of them.

**Count:** prior live findings = 6. **Resolved: 3 (F1, F2, F3 — the entire HIGH
tier). Partially resolved: 1 (F6). Still-open: 2 (F4 MED, F5 LOW). Regressed: 0.**

---

## 2. DEF-1 resolution-seam verdict (the headline S86 seed)

**Verdict: ONE seam, correctly wired — NOT N independent chokepoints.** The DEF-1
concern (is there one seam that should consult the prelude fallback, vs N
chokepoints each wired separately?) resolves favourably for this crate.

- **One canonical gate:** `prelude_fallback_target(current_module) -> Option<prelude_path>`
  (`checker.rs`), the single absence-is-OFF + `current != prelude` decision.
- **One shared primitive:** four of the bare-name chokepoints
  (`resolve_current_or_prelude` checker.rs:942; `probe_current_or_prelude`
  checker.rs:1243; `resolve_entry_in_current_module` checker.rs:1378;
  `resolve_terminal_entry_or_prelude` checker.rs:1451) all dispatch through the
  shared `cranelisp_types::resolve_with_fallback` primitive at the types-crate
  boundary — a true single seam.
- **The monomorphisation-collection chokepoint — the one DEF-1 missed — is now
  correctly routed.** `collect_imported_constrained_calls` (`program.rs:~3282`)
  resolves callees through `resolve_terminal_entry_or_prelude` (the fallback-aware
  seam), not a raw current-module-only lookup. The sibling collectors
  (`collect_local_parametric_calls` ~3373, `collect_parametric_fn_value_args` ~3420)
  intentionally use the **non-fallback** `resolve_terminal_entry_and_home` because
  they collect *only local* calls by design — correct, not a gap.

There are **7 call sites of `prelude_fallback_target`** total; 4 route through the
shared primitive, 2 (`lookup_constructor_type_with_state` checker.rs:713;
`find_hkt_param_index_in_registry` traits.rs:~2649) call the gate directly but
apply the **same** I-1 `prelude_terminal_visible` public-head filter, and 1
(`resolve_type_expr_internal` checker.rs:~2186) inlines the retry. The 2-direct +
1-inline are a **minor consolidation opportunity** (see Finding S87-5), not a
correctness fragmentation.

---

## 3. S87 findings (severity-ranked)

### Finding S87-1 — FQ-naming: "no impl of trait T for type X" renderers emit bare type names (IMPORTANT, cross-crate)

**Lens:** (vii) cross-crate hygiene + S86 Wave-0 seed.
**Evidence.** `concrete_type_name` (`traits.rs:2202-2211`) returns a bare
`TypeName`, stripping module qualification: `Type::ADT(fqtn, _) => Some(fqtn.name.clone())`
(line 2208). Two diagnostic sites render through bare names:
- `traits.rs:1156-1159`: `format!("no impl of trait {} for type {}", trait_name, impl_type_name)` where `impl_type_name` is the bare `TypeName` from `concrete_type_name` (line 1143).
- `traits.rs:1803-1806`: `format!("no impl of trait {} for type {}", fq_trait, impl_type)` where `impl_type` is the bare name from `concrete_type_name(&resolved_var)` (line 1796-1799).

**Why it matters.** A user with two same-named ADTs in different modules
(`grid/Cell`, `solver/Cell`) gets `no impl of trait Display for type Cell` — which
`Cell`? The message cannot disambiguate. Note the asymmetry: `fq_trait` at :1805
already renders fully-qualified (`FQTraitName` Display), but the *type* half does
not — the message is half-FQ. This is the adjacent debt logged in Wave 0
(`SPRINT.md:204`).
**Proposed resolution.** Reconstruct the FQ type name at the two error sites: the
`resolved_arg`/`resolved_var` `Type::ADT(fqtn, _)` already *carries* the
`FQTypeName` — render `fqtn` (module + name) in the message instead of calling the
deliberately-bare `concrete_type_name`. Do NOT change `concrete_type_name` itself
(it is correctly bare for mangled-name construction at `build_mangled_name`
traits.rs:2192-2196 — its other call sites *need* the bare name). Add a separate
`fq_type_name_for_diagnostics(&Type) -> Option<String>` for the message path.
**Routing.** `target: /typecheck` (the fix is in-crate); `/qa` owes a narrow repro
(two same-named ADTs, missing impl, assert the FQ name appears) per the
defect-handoff rule. Cross-crate flag is only because the FQ-rendering convention
(Decision 47) is `/arch`-anchored.

### Finding S87-2 — Over-budget phase-driver functions, scope wider than baseline F5 (IMPORTANT, typecheck-internal)

**Lens:** (iii) function-budget overruns.
**Evidence** (effective body, blank/comment-stripped; `src/CLAUDE.md` convention ~100):
- `monomorphise_call` (`traits.rs:~1372-1677`) — **~307 lines.** The single largest
  production fn in the crate; a 7-phase sequential driver (resolve trait home →
  check constraints → recheck body → resolve inner calls → register mono entry →
  verify constraints → annotate AST).
- `check_form_body_multi_sig` (`program.rs:~1201-1455`) — **~180 lines.**
- `check_impl_method_with_sig` (`traits.rs:~652-823`) — **~173 lines.**
- `finalize_check_result_inner` (`program.rs:~1776-1926`) — **~150 lines** (was
  ~193 in baseline; reduced but still over).
- `register_trait_impl` (`traits.rs:~398-575`) — **~127 lines** (unchanged).
- `get_constrained_fn` (`traits.rs:~2076-2197`) — **~121 lines.**
- `check_hkt_impl_method` (`traits.rs:~919-1014`) — **~103 lines** (borderline).

**Why it matters.** Seven over/at-budget functions, all in the two densest modules
(`traits.rs` ~1% inline test, `program.rs` ~6%), all sequential phase-drivers.
`monomorphise_call` at ~307 lines is the standout — it is the cross-module mono
seam (S83/FIXME 0355), the highest-stakes and least-tested logic in the crate, and
the hardest to hold in working memory. Pure legibility/testability concern (no
correctness issue found), but it compounds with low inline-test density.
**Proposed resolution.** Extract named sub-phase helpers, `monomorphise_call`
first: `resolve_mono_trait_home` / `recheck_and_resolve_body` / `register_and_verify`.
The phases are already comment-delimited — the extraction is mechanical.
**Routing.** `target: /dev` (typecheck). LOW→IMPORTANT only because the count
(7) and the `monomorphise_call` size crossed from "two oversize fns" (baseline) to
a systemic phase-driver-bloat pattern in the mono/traits subsystem.

### Finding S87-3 — `parsed_to_top_level` silent-drop catch-all persists (SUGGESTION, typecheck-internal)

**Lens:** (ii) dead paths / silent behaviour. Carries baseline F4 forward.
**Evidence.** `form.rs:510-512`: `ParsedEntry::Macro { .. } | ParsedEntry::Constructor { .. } => None,`
followed by `_ => None` (commented "Catch-all for #[non_exhaustive] forward-compatibility").
Entries returning `None` are filtered out with no diagnostic.
**Why it matters.** The named `Macro`/`Constructor` arm is correct (both are
upstream-expanded). But the `_ => None` converts a *future* `ParsedEntry` variant
into silent data loss — a frontend↔typecheck contract break would vanish rather
than fail loudly, the exact class Principle-17's "no silent universe behaviour"
guards against. Latent, not active (no current variant hits it).
**Proposed resolution.** Replace `_ => None` with an explicit
`unreachable!("invariant: ParsedEntry::X is frontend-expanded before typecheck")`
(or a debug-assert + trace) so a new variant forces a compile-time exhaustiveness
decision. Downgraded from baseline MED → SUGGESTION because it has survived two
audits as latent-not-active and the risk is genuinely forward-compat-only.
**Routing.** `target: /dev` (typecheck).

### Finding S87-4 — `lookup_constructor_type` dead-code helper still defaults to `"user"` (SUGGESTION, typecheck-internal)

**Lens:** (ii) dead paths + (vi) interim residue. Carries baseline F6 forward (its
sibling helper is now resolved).
**Evidence.** `checker.rs:656-660`: `#[allow(dead_code)] pub(crate) fn lookup_constructor_type(&self, ctor_name) { let user_path = ModuleFullPath::from("user"); ... }`.
The production caller (the `infer.rs` pattern-ctor `exists` gate) was retired in S79
Option 3a (product ctors now resolve through their own `Def`); the helper survives
only because `#[cfg(test)]` references it (doc-comment lines 692-696 say as much).
The sibling `is_internal_constructor_check_in_module` (checker.rs:725) was already
de-defaulted to an explicit module param.
**Why it matters.** Principle 17 + Principle 19 forbid `user`-as-privileged-fallback
in resolution. Dead-code-gated today, so the violation is latent — but it is an
attractive-nuisance: an agent wiring it into production "for convenience" would
introduce a live violation.
**Proposed resolution.** Either delete it (and migrate the `#[cfg(test)]` callers
to `lookup_constructor_type_in_module` with an explicit module — the test fixtures
already know their module), or give it a mandatory `&ModuleFullPath` param like its
sibling. Removal is cleaner.
**Routing.** `target: /dev` (typecheck).

### Finding S87-5 — Prelude-fallback gate has 2 direct callers + 1 inlined retry beside the shared primitive (SUGGESTION, typecheck-internal)

**Lens:** (v) resolution-seam consolidation. Surfaced by the DEF-1 seam walk.
**Evidence.** Of 7 `prelude_fallback_target` call sites, 4 route through the shared
`cranelisp_types::resolve_with_fallback` primitive; but 3 do not:
`lookup_constructor_type_with_state` (checker.rs:713) and
`find_hkt_param_index_in_registry` (traits.rs:~2649) call the gate + apply the I-1
`prelude_terminal_visible` filter by hand, and `resolve_type_expr_internal`
(checker.rs:~2186) inlines the current-module-miss → prelude-retry loop.
**Why it matters.** The I-1 public-head filter is replicated at the 2 direct sites.
Three copies of "gate → probe prelude head → filter on `prelude_terminal_visible`
→ retry" is below the rule-of-three extraction threshold *today* (two of them, plus
the inline), but it is the seam that DEF-1 fragmented once already — keeping the
filter-discipline in one helper hardens against the next missed chokepoint. Not a
correctness issue (all three apply the same discipline correctly).
**Proposed resolution.** Extract a `probe_prelude_head_visible(current_module, name)
-> Option<entry>` that bundles gate + probe + I-1 filter, and have the 2 direct
callers + the inline site use it. Defer until a 4th direct caller appears if
preferred (it is at the threshold).
**Routing.** `target: /dev` (typecheck).

---

## 4. Positives confirmed (currency check)

- **Principle 17 — production scan-free (re-confirmed).** Every `self.modules`
  access in checker/infer/program/traits is single-key (`get`/`get_mut`/`insert`/
  `remove`/`contains_key`/`ensure_module_exists`). No `.iter()`/`.values()`
  universe scan in production. `checker.rs:518/555/572` `unreachable!` guards are
  invariant-encoded single-key reads.
- **DEF-1 seam single + correctly wired** (§2). The S86-missed mono-collection
  chokepoint now routes through the fallback-aware seam.
- **Single `Expr` child-enumeration source.** `for_each_child_expr` /
  `_mut` (`program.rs:52/101`); `apply_subst_to_expr` (168),
  `annotate_expr_from_maps` (196), `collect_constrained_calls` (~3471) all route
  through them; `infer.rs` (`resolve_deferred_trait_calls`,
  `resolve_value_position_trait_methods`) routes through the shared helper too. No
  hand-rolled walker.
- **`infer.rs` per-variant dispatch (exemplary).** `infer_expr` dispatches one
  method per `Expr` variant; no production unwrap/expect/panic/unreachable in the
  whole file.
- **Error discipline intact.** Production uses `?` throughout; the only production
  `unreachable!`/`.expect()` are invariant-encoded with justification comments
  (checker.rs:518/555/572; traits.rs:37/936; program.rs:1305/1326). All bare
  `unwrap`/`panic!` are `#[cfg(test)]`.
- **`builtins.rs` 100% test-support** (corrected LOC 1) — confirmed not a
  production surface.
- **`SymbolTables<C,L>` newtype materialised** in `cranelisp-types` — the F1/F8
  "both-move" landed; the boundary shorthand is now real, not textual-only.
- **"mirror" comments are intentional symmetry, not duplication.** The `traits.rs`
  "mirror" comments (lines ~648, ~764, ~1406, ~1864) all annotate the
  enter-module → work → restore-module state-management pattern shared across
  `monomorphise_call` / `recheck_body_for_mono`, not copy-pasted logic blocks.
  No Principle-7/8 mirror debt found.

---

## 5. Prioritized backlog (Stage-B output for the scope-decision gate)

1. **(IMPORTANT, `/typecheck` + `/qa` repro)** FQ-naming "no impl" renderers
   (Finding S87-1) — half-FQ diagnostics, user-visible disambiguation failure.
   Smallest user-facing fix; pairs with a 2-same-named-ADT narrow repro.
2. **(IMPORTANT, `/dev` typecheck)** Decompose `monomorphise_call` (~307) first,
   then the 6 other over-budget phase-drivers (Finding S87-2) — highest-stakes,
   least-tested code; pure legibility/testability.
3. **(SUGGESTION, `/dev`)** `parsed_to_top_level` `_ => None` → loud failure
   (S87-3); `lookup_constructor_type` `"user"`-default removal (S87-4); prelude
   filter-discipline extraction (S87-5). Three cheap typecheck-internal hardenings.

**No Blocker.** The baseline's only HIGH tier (FIXME 0240) resolved; nothing in
this crate gates Phase H. No emergent-mandatory refactor (no third-duplicate, no
live mirror) was found that would force an in-S87 landing per METHOD §Phase 5.

---

## 6. Cross-cutting note for the /arch synthesis pass

The DEF-1 seam in **this crate** is single and correct (§2). The recurrence risk
DEF-1 names is *cross-crate* — whether the *same* prelude-fallback discipline that
typecheck centralizes here is replicated (or diverges) in the backend/int
resolution paths. That comparison is the /arch synthesis lens, not this single-crate
pass. The only typecheck-side residue feeding it is Finding S87-5 (2 direct + 1
inline gate caller beside the shared primitive) — small, in-crate, below threshold.
