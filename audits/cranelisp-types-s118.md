# `cranelisp-types` whole-context assessment — Sprint 118

**Date:** 2026-07-26
**Scope:** `crates/cranelisp-types/` (source + unit suites + `public-api.txt` +
crate `CLAUDE.md`), `design/arch/bounded-contexts.md` §7, `design/arch/interfaces.md`
context, the pending S119 deltas that name this crate
(`trait-impl-cache-carrier.md`, FIXME 0898 `ConcreteType::result_root`,
FIXME 0748 injective GOT mint, `ownership-stratum-options.md`), and the prior
assessment `audits/cranelisp-types-s87.md`. Read-only; no cargo commands were
run (serial proxy chain active; W8 re-gate certified all `public-api.txt`
baselines CLEAN at `4ed43430`).

**Measured surface.** 10,814 raw lines across 24 production modules (comment
mass is a large share — see §2.3); 5,840 lines of sibling `{module}/tests.rs`
suites plus four inline `#[cfg(test)]` mods; `public-api.txt` 1,878 lines.
Since S87 (3,035 corrected LOC) the crate has absorbed, each by explicit
ruling: the concrete boundary (`concrete.rs`, `mono_expr.rs`), the typed
resolution carriers (`VarRef`/`ApplyRef`/`ViewBuildError`, S114), the
ownership carriers (`ownership.rs`, S102–S103), `value_layout` (S103), the
resolution primitive + `ResolutionScope` (S76/S108), the ADT-entry builder
(S110), the S116 carrier work (`Sexp::Annotated`, the trait-method sig
triple, `drop_glue_symbol_name`), and cache-schema evolution to 23.

## 1. Verdict

| Attribute | Grade | Acid-test verdict |
|---|---|---|
| Design quality (fitness) | **Strong** | The structural-invariant vocabulary is exactly what a second implementation would design deliberately: illegal states unconstructable (`UserFnState`, `PrimitiveBody`, `ConcreteType`/`MonoExpr` with no `Var` path), closed sums where exhaustive matches ARE the contract (`VarRef`/`ApplyRef`/`ViewBuildError`, the mode enums), single-mint helpers for every identity grammar (`member_key`, `bare_member_name`, `drop_glue_symbol_name`, `render_type`, `value_layout`, `build_adt_entries`), and one resolution walk with the prelude fallback decided once at scope construction. Growth lands here by ruling, not by drift — the crate is the project's chief instrument against its worst defect classes (mirror duplication, phantom slots, ambiguous defaults). |
| Design realisation | **Adequate** | The code realises the design almost everywhere, but this crate's canonical facade IS its rustdoc (facades retired S69), and that facade carries falsified narrative: a phantom `SymbolTable.dll: Option<D>` / `D: DllStore` generic described at four sites that exists nowhere in the workspace; pipeline "carrier types threaded between int and backend" that have zero consumers; a `next_seq → AtomicU64` "facade target" citing S-DRIFT findings against a facade retired ~50 sprints ago; a Decision-39 append carrier (`StructuralDeclEntry`) that int bypasses with direct field pushes. |
| Simplicity and volume — code | **Strong** | The semantic surface is lean for what it carries; every helper spot-checked has real multi-crate consumers (e.g. `got_data_symbol_name` 19 files, `member_key` 15, `ensure_module_exists` 17, `value_layout` 9). The exceptions are five dead public exports (§2.3) — the identical class S87 Finding 2 removed once already. |
| Simplicity and volume — design | **Adequate** | BC §7 and `interfaces.md` are current and precise. The rustdoc-as-facade, however, is roughly two-thirds of `module.rs`'s 2,996 lines and much of it is changelog-grade archaeology: retired-variant narratives told in three or more places, sprint/submission numbering as section headers, retired-document citations. Over-documentation is decay-in-waiting, and here the decay is already visible as the falsified narratives above. |
| Simplicity and volume — tests | **Strong** | 5,840 lines, submodule-attributable per the seam map, shaped by defect history rather than symmetry: the drop-glue injectivity battery, the FIXME-0567 head-vs-terminal prelude pins, the FIXME-0620 `storage_key_*` family, the alias-cycle depth-cap pin, Principle-16 punctuation guards, serde-skip and pre-S94 default pins. A rewrite would want essentially this suite. |
| Duplication | **Strong** | The crate is the workspace's single-source home and is internally clean: one chain-follow walk plus a view-aware same-module arm that delegates cross-module hops to it; one `Type` walk; one ⊤-on-absence home. The residual twins are already ruled with scheduled cures — `result_root` (FIXME 0898, S119) and `trait_impl_key` (trait-impl-cache-carrier §4, S119). No redundant language surface originates in this context. |
| Risk-weighted coverage | **Adequate** | Most invariants are pinned on production paths (§2.4). Two holes: the GOT data-symbol mint is a KNOWN non-injective identity (FIXME 0748) whose witness still pins the *collision* (`assert_eq`, to invert on fix) — the R4 register row for this family is undischarged; and the serde-shape ⇒ `CACHE_SCHEMA_VERSION`-bump contract is convention-guarded (CLAUDE.md + review), not test-forced from either side. |
| Maintainability | **Adequate** | Seams, naming, and the two `unsafe impl`s (GOT `Send`/`Sync` with a real justification; `ModuleEntry` documented as informational) are in good order. The hazard is the doc mass: a reader of the canonical facade must sift history layers, stale cross-references, and phantom fields to find the live contract. |
| Memory freshness | **Adequate** | The crate `CLAUDE.md` is one of the best in the project — the serde-is-the-cache-contract rule, the accessor read-throughs, the resolution traps, and the `#[non_exhaustive]` exception classes are all current and load-bearing. Its line-number citations have drifted, some substantially (`callable_got_slot` cited at `module.rs:1318`, actually 1445; `not_found` cited at `resolve.rs:803`, actually 1097), and the `PlatformSpec.name` note still points at an S69-era "wave-3 concurrency-cluster brief". |

**Overall.** Would the second-time solution look like this? For the
architecture: very nearly verbatim. The newtype discipline, the
syntactic/resolved stage split (`TraitRef`/`TypeRef`/`SymbolRef` vs the FQ
triple), callability-as-kind, the concrete boundary, the typed resolution
carriers, and the one-mint identity helpers are the accumulated lessons of
118 sprints expressed structurally — this is the crate the acid test was
written to reward, and each recurring defect class has been closed by
representation rather than by patch. What the rewrite would NOT reproduce:
the five dead exports and the bypassed append carrier; the inline
archaeology that makes the canonical facade partly fictional (phantom
`dll`/`DllStore`, the 31-sprints-stale `AtomicU64` concurrency target that
S87 Finding 3 already flagged as "the limbo is the finding" — still in
limbo); and a known-non-injective symbol mint sitting one screen away from
the crate's own model injective mint. The priority is not redesign; it is
truth-restoration of the facade and finishing the two ruled identity items.

## 2. Current state

### 2.1 Prior-assessment trail (S87)

The S87 pass (by `/review`; predates the disposition-trail protocol) had six
findings:

- **F1 (five-fold `Type`-render duplication) — RESOLVED.** `render_type` +
  `PrimitiveNaming`/`VarNaming` landed (FIXME 0420);
  `crates/cranelisp-types/src/types.rs:142` is the one walk, `Display`
  delegates (`types.rs:101`), BC §7 "Type rendering" records the settlement.
- **F2 (dead `format_type_display`/`format_type_with_vars` exports) —
  RESOLVED.** Both removed; the lettered-var capability survives as
  `VarNaming::Lettered`. *The class recurred* — see §2.3.
- **F3 (SymbolTable concurrency target un-migrated, "the limbo is the
  finding") — STILL OPEN, now 31 sprints past S87.**
  `crates/cranelisp-types/src/module.rs:146-151` still documents `next_seq`'s
  "facade target is `AtomicU64` … the conversion lands as part of the broader
  SymbolTable concurrency cascade (S-DRIFT-19/20/21)". The facade it targets
  was retired (S69 Sub 42); no migration has landed S70–S118; the as-built
  `&mut SymbolTable`-behind-outer-`DashMap` model has carried every sprint
  since. The evidence is now overwhelming that the simpler model is the
  end-state and the target should be retracted (→ R2).
- **F4 (`concrete_type_name` strips the module in no-impl messages) —
  typecheck-side; not re-verified in this pass (out of context).
  `concrete_type_name` still exists as typecheck's dispatch-key derivation
  (`crates/cranelisp-typecheck/src/traits/dispatch.rs:57`).**
- **F5 (two justified `unreachable!`s) — HELD.** `got.rs:82` and
  `ast.rs:479` unchanged, still justified; not re-flagged.
- **F6 (`module.rs` concentration watch-note) — WATCHED, grew as predicted.**
  `module.rs` is now 2,996 non-test lines (tests moved to a 1,914-line
  sibling) and has additionally absorbed the alias types, chain-follow
  primitives, and the symbol-naming grammar (`got_data_symbol_name`,
  `drop_glue_symbol_name` + encoders). Cohesion is still arguable ("the
  symbol-table model and its identities") and no split is recommended this
  pass, but the natural seam if S119's `WrittenTraitImpl` + `trait_impl_key`
  land here too is a `module/naming.rs` (identity mints) split.

### 2.2 Design quality and realisation

What the second-time solution would keep, verified in source:

- **Illegal states unconstructable.** `UserFnState` (slot ⟺ concrete,
  `module.rs:2281`), `PrimitiveBody::Inline` with no slot field
  (`module.rs:2192`), `ConcreteType` with no `Var` variant (`concrete.rs:44`),
  `MonoExpr` with non-optional `ConcreteType` and non-optional typed
  `resolution`/`dispatch` carriers with no serde default (`mono_expr.rs:270`,
  `:319`) — absence unrepresentable, per design.
- **Closed sums as contract.** `VarRef`/`ApplyRef`/`ViewBuildError`
  deliberately not `#[non_exhaustive]` ("unresolved has no constructor",
  `mono_expr.rs:109-191`), the ownership mode enums likewise
  (`ownership.rs:35-54`), with the exception classes recorded in the crate
  `CLAUDE.md` — a nuanced, correctly-argued deviation from the crate-wide
  `#[non_exhaustive]` policy.
- **One-mint identity grammars.** `member_key`/`bare_member_name`
  (`resolve.rs:1044/1065`) with Principle-16 guards; `drop_glue_symbol_name`
  with length-prefixed hex encoding (`module.rs:2654-2699`) — injective by
  construction, the R15/R16 authority, pinned by a five-test battery
  (`module/tests.rs:1772-1885`); `build_adt_entries` as the single ADT
  registration derivation (`adt_build.rs:133`).
- **The resolution primitive.** `ResolutionScope` with fallback decided once
  at construction (`resolve.rs:91-124`), the two-identity `Resolved`
  (`fq` vs `storage_key`, the 0620 rule, `resolve.rs:413-442`), the §8.6.4
  definition seam (`reject_def_over_binding`, `resolve.rs:208`), and the
  same-module staging-aware chain-follow arm (`resolve.rs:875-942`) that
  corrects the S76 "beyond the first hop everything is committed" premise.

Realisation failures — all documentary, all in the canonical facade:

1. **Phantom field.** Four rustdoc sites describe `SymbolTable.dll:
   Option<D>` via a `D: DllStore` generic (`module.rs:622`, `:1193`, `:1836`,
   `:2518`). No `dll` field and no `DllStore` trait exist anywhere in the
   workspace.
2. **Dead surface documented as live.** `lib.rs:130-132` describes
   `CompileResult`/`CallEdge`/`CallInfo`/`CallGraph` as "discrimination +
   carrier types threaded between int and backend"; none has a single
   consumer (§2.3).
3. **The retired concurrency target.** `module.rs:146-151` (S87 F3, above).
4. **Bypassed carrier.** `StructuralDeclEntry` + `append_structural_decl`
   (`module.rs:728`, `:2566`) — the Decision-39 "one enum-carrier method, no
   parallel per-section appends" — has zero out-of-crate callers; int pushes
   the pub Vec fields directly (`src/process_form/form_dispatch.rs:86,96`,
   `src/save.rs:1971`). Either the seam is enforced or it is fiction.
5. **Recorded-but-unlanded narrow.** `PlatformSpec.name` is still bare
   `String` (`module.rs:2529`) with rustdoc assigning the `ModuleName` narrow
   to an S69-era "/dev wave-3 concurrency-cluster brief" that no longer
   exists as a live plan.

Pending S119 deltas confirm the crate is where the architecture expects new
contract to land: `WrittenTraitImpl` + `trait_impl_key` +
`enrol_written_trait_impl` (trait-impl-cache-carrier §2/§4, schema 23→24,
the sole ruled window), `ConcreteType::result_root()` (FIXME 0898 ruling),
and the injective GOT mint (FIXME 0748). The option paper's typed-handle
tranche A is explicitly ruled **no `cranelisp-types` impact**
(`ownership-stratum-options.md:250` — the handle newtypes stay internal to
the runtime pair); this crate becomes the home only if a shared cross-crate
handle vocabulary later emerges.

### 2.3 Simplicity, volume, and duplication

**Dead public exports (the recurring S87-F2 class).** Verified
zero-consumer across `src/` + all crates (definition + `lib.rs` re-export
only):

- `ImplSexp` (`module.rs:2497`) — "stored impl S-expression for deferred
  processing"; nothing constructs or reads it.
- `CompileResult` (`pipeline.rs:23`) — references a pipeline-v3-era shape.
- `CallEdge`, `CallInfo`, `CallGraph` (`pipeline.rs:74-93`) — "populated
  during typecheck, consumed by codegen"; neither happens (the live call
  graph is `ModuleEntry::Def.callees`).
- `StructuralDeclEntry` + `append_structural_decl` — zero out-of-crate
  callers (production writes bypass it; see §2.2 item 4).

Everything else spot-checked earns its place (consumer-file counts:
`ensure_module_exists` 17, `got_data_symbol_name` 19, `member_key` 15,
`ModuleStrategy` 17, `CodegenBehaviour` 14, `substitute_module_alias` 5,
`reject_def_over_binding` 6, `drop_glue_symbol_name` 7, `value_layout` 9;
single-consumer items are each deliberate: `is_strict_type_concrete` is the
FIXME-0689 fence, `synthetic_local_from_expr` the FIXME-0685 licensed door,
`with_static_backing` the primitives link-symbol path).

**Doc volume.** `module.rs` is the concentration: ~2/3 comment mass, with
retirement narratives repeated across sites (the `ModuleEntry::Macro`
retirement is told at `module.rs:1175-1187`, again in `into_concrete`'s
comments, again in the `DefKind::Macro` rustdoc `:2025-2114`, again in
`parsed.rs:63-105`; the `PlatformDecl` retirement twice), sprint/submission
numbers as narrative anchors, and citations to retired documents
(`design/arch/facades/int.md` at `module.rs:281`,
`facades/frontend-audit-s70.md` at `:309`, a malformed self-citation
``design/arch/`view.rs` rustdoc`` at `view.rs:16`). Because this crate's
rustdoc IS its facade (BC §7 "Per-surface documentation"), archaeology here
is not harmless colour — it is the surface record decaying in place.

**Duplication.** Internally clean (one walk per question; the small
recursive-walk family in `types.rs` — `contains_var`/`is_concrete`/
`free_vars`/`max_type_var_id`/`collect_var_ids_ordered` — is deliberate
intent-separation, each documented). The two cross-crate residuals are ruled
with S119 cures: the IO result-root strip rule (two literal encodings,
backend + int; FIXME 0898 rules `ConcreteType::result_root()` here) and the
hand-rolled `impl$` key at two typecheck sites (`trait_impl_key`,
trait-impl-cache-carrier §4).

### 2.4 Risk-weighted coverage

| Risk | Production-path evidence | Verdict |
|---|---|---|
| Phantom-slot / callable-kind regression (the S82/S101 SIGSEGV class) | `module/tests.rs::callable_got_slot_is_structural`, `::inline_primitive_is_slotless_but_callable_target`, `::wave0_defined_symbols_filter_is_correct`, `::polymorphic_template_excluded_from_defined_symbols` — the exact filter + read-through production consumers use. | **Pinned** |
| Drop-glue symbol identity injectivity (R15/R16 dependency) | Five-test battery `module/tests.rs:1772-1885`: injectivity, nesting, length-prefixing, arity/result and ADT-argument boundary separation. | **Pinned** (the register's tier-2 model) |
| GOT data-symbol identity injectivity (R4) | `a.b` vs `a_b` collide (`module.rs:2645-2651`); FIXME 0748 open; the backend witness pins the COLLISION (`assert_eq`, to invert on fix). Live defect, correctly routed (FIXME + pinned witness), unfixed. | **Not discharged** |
| Resolution correctness: prelude head-vs-terminal visibility (0567), storage-vs-reference identity (0620), qualified-current-module (0655), alias cycles, punctuation literals (0328) | `resolve/tests.rs` — `scope_i1_*` (`:642`, `:664`), `storage_key_*` five-case family (`:1028-1176`), `qualified_current_module_*` (`:263-333`), `same_module_alias_cycle_is_a_miss_not_a_stack_overflow` (`:814`), `split_qualified_bare_operator_is_not_qualified` (`:364`). | **Pinned** |
| View-build gate: Unresolved-vs-NotConcrete routing, verdict-before-type, synthetic carve-out, lenient seam panics | `mono_expr/tests.rs` (851 lines) + the always-on tier-3 asserts in `lenient_from_expr` / `assert_all_synthetic` (`mono_expr.rs:875-885`, `:1099`). | **Pinned** |
| `value_layout` soundness coupling (Copy ⟺ flatten; the Wave-3a UAF blockers) | `heap/value_layout_tests.rs` (329 lines) covering 0-field/≥2-field exclusions, recursion cycle guard, `Vec` exclusion; single-ctor-name resolver delegation (`type_ctor_names`). | **Pinned** |
| ⊤-on-absence ownership reads + ABI equality | `ownership/tests.rs`; accessors are the sole read path per CLAUDE.md; `abi_eq_opt` None ≡ conservative. | **Pinned** |
| Serde/cache-contract behaviors (skip fields, defaults, pre-S94 polarity) | `module/tests.rs::wave0_symbol_table_got_present_and_serde_skipped`, `::code_serialise_round_trip_skips_field`, `::platform_effect_poll_shape_defaults_to_false_for_pre_s94_cache`, `::symbol_table_schema_version_defaults_to_zero_for_legacy_cache`, `::primitive_reshape_serde_shape`. The bump-on-shape-change rule itself remains convention-enforced (CLAUDE.md + review), not test-forced. | **Pinned (behaviors); convention (discipline)** |
| ABI layout contracts crossing the C boundary (`ConcurrencyDescriptor`, `Poll`, `HeapHeader`) | Const asserts `heap.rs:35-37`; offset/size pins `scheduling.rs:454-479`. | **Pinned** |

No new live behavioural defect was found in this pass; the one live defect
in-context (non-injective GOT mint) is pre-existing, filed, and witnessed.

### 2.5 Maintainability and memory

Unsafe usage is minimal and justified (`got.rs:66-70` with a real lifetime
argument; `module.rs:1261-1279` documented as informational delegation to
`C: CodeStore`). Accessor discipline (`callable_got_slot`,
`is_callable_target`, `type_def_info`, `mode_summary`, the `ModeSummary`
⊤-reads) gives every cross-field invariant exactly one read path, and the
crate `CLAUDE.md` names each one — that file is genuinely the "voice of the
code" it claims to be. Its decay: drifted line-number citations
(`callable_got_slot` 1318→actual 1445, `is_callable_target` 1354→1485,
`defined_symbols` 676→782, `not_found` 803→1097, `mode_summary` 1377→1549,
`PlatformSpec.name` 2348→2529), which in a fast-moving 3,000-line file argue
for symbol-name citations over line numbers.

## 3. Recommendations

### R1 — Delete the dead exports; decide the structural-decl append seam

**Kind:** dead surface / design realisation (the recurring S87-F2 class)
**Evidence:** zero-consumer `ImplSexp` (`module.rs:2497`), `CompileResult`,
`CallEdge`, `CallInfo`, `CallGraph` (`pipeline.rs:23-93`), all still
narrated as live at `lib.rs:130-132`; `StructuralDeclEntry` +
`append_structural_decl` bypassed by int's direct field pushes
(`src/process_form/form_dispatch.rs:86,96`, `src/save.rs:1971`).
**Cost:** small
**Proposed owner:** `/arch` (owns the crate), with a `/dev`(int) rider only
if the route-through option is chosen for the append seam
**Done:** The five zero-consumer types are gone from `lib.rs` and
`public-api.txt` (regenerated in the same change-set, baseline-diff
discipline). The Decision-39 append carrier is resolved one way — either int
routes structural-decl appends through it (and direct pushes outside the
crate become a review flag) or the carrier + method are deleted and the pub
Vec fields are recorded as the contract. A residual half-measure (deleting
the types but leaving the `lib.rs` narrative, or keeping both append paths)
does not meet the bar.

### R2 — Restore facade truth: retract the concurrency target, delete the phantom `dll` field narrative, land or re-home the `PlatformSpec.name` narrow

**Kind:** design realisation / design feedback (closes S87 F3)
**Evidence:** `module.rs:146-151` (`AtomicU64` "facade target",
S-DRIFT-19/20/21, 31 sprints unmigrated — the as-built `&mut`-per-table
model has carried S70–S118); phantom `SymbolTable.dll`/`DllStore` at
`module.rs:622,1193,1836,2518`; retired-doc citations
(`facades/int.md` at `:281`, `facades/frontend-audit-s70.md` at `:309`,
the malformed `view.rs:16` citation); `PlatformSpec.name: String`
(`module.rs:2529`) pointing at a dead S69 brief.
**Done:** The rustdoc describes only the as-built model. The
DashMap-inner/atomic/`&self`-write target is either formally retracted (one
line in BC §7 recording the retraction and why the simpler model is the
end-state) or given a live design home with a sprint — no third state. The
four `dll` mentions match reality (either the field's actual int-side home
is named, or the narrative is cut). `PlatformSpec.name` either narrows to
`ModuleName` in a small change-set or its rustdoc records a standing
decision with a real trigger.
**Cost:** small-to-medium
**Proposed owner:** `/arch`

### R3 — Land the injective GOT data-symbol mint (FIXME 0748) in the S119 types window

**Kind:** live-defect scheduling (already filed + witnessed; this is
scheduling weight, not a new filing)
**Evidence:** `got_data_symbol_name` (`module.rs:2645`) maps `a.b` and
`a_b` to one symbol — a constructible cross-module wrong-slab dispatch, the
same R4 class as the fixed drop-glue keying; the backend witness currently
pins the collision (`assert_eq`, to invert); the model injective mint
(`drop_glue_symbol_name`) is 10 lines away; FIXME 0748's binding
constraints (alphanumeric fixed points for the `__cranelisp_got_primitives`
link literal; `_entry` outside the escape image; one change-set with the
`.o`-corpus/link-fixture cascade) are already worked out.
**Done:** The types-home mint is injective; the backend witness inverts to
`assert_ne` and a types-side round-trip/fixed-point battery lands beside the
drop-glue one; the R4 register row for the GOT family reads `witnessed`.
S119 already opens this crate (0869 carrier window, 0898) — riding that
window costs least.
**Cost:** small-to-medium (mechanical mint + cascade)
**Proposed owner:** `/arch` (ruling per 0748) + `/dev`

### R4 — History-compaction pass over the rustdoc facade

**Kind:** volume optimality (docs) — over-documentation as decay-in-waiting
**Evidence:** `module.rs` ~2/3 comment mass; the `Macro` retirement narrated
in four places (`module.rs:1175-1187`, `into_concrete` comments,
`DefKind::Macro` rustdoc `:2025-2114`, `parsed.rs:63-105`); sprint/submission
changelog framing throughout (`"S69 Submission 35"`, `"Sprint 58 Wave 3b"`
as load-bearing anchors); duplicated Decision-45 placement narrative
(variant rustdoc + `TraitImpl` + BC §7).
**Done:** Each item's rustdoc states the current contract plus at most a
one-line provenance pointer (git / BC §7 / the ruling doc); retired-shape
narratives compress to single lines; no citation targets a retired document.
Doc-only — `public-api.txt` unchanged; the S20/S21-class behaviour pins are
untouched. The compaction must NOT thin the genuinely load-bearing contract
notes (serde discipline, accessor read-throughs, exception classes) — the
test is "would a new reader find the live contract without sifting
history", not raw line count.
**Cost:** medium
**Proposed owner:** `/arch`

### R5 — Refresh the crate `CLAUDE.md` citations to symbol-anchored form

**Kind:** memory freshness
**Evidence:** drifted line references — `callable_got_slot`
(cited `module.rs:1318`, actual 1445), `is_callable_target` (1354→1485),
`defined_symbols` (676→782), `not_found` (`resolve.rs:803`→1097),
`mode_summary` (1377→1549), `PlatformSpec.name` (2348→2529); the
`PlatformSpec` note's dead-brief pointer.
**Done:** Citations name symbols (optionally file-only), not line numbers,
or the numbers are refreshed with a note that symbol names are preferred;
every pointer resolves. Fold into R2/R4's change-set if those are accepted
(same files, same pass).
**Cost:** small
**Proposed owner:** `/arch`

## 4. Disposition trail

*(appended at S119 Phase 1 by `/sprint` + the user; not by `/audit`.)*

## Next skills

- `/sprint` — file this assessment as S119 Phase-1 input; process R1–R5 with
  the user (accept → FIXME per recommendation, or decline with rationale
  recorded here). Note R3 is scheduling weight on the already-open FIXME
  0748, and the S119 types window (0869 carrier + 0898 `result_root`) is the
  natural landing slot for R1–R3.
- `/arch` — proposed owner of all five recommendations; R2/R4/R5 are one
  coherent facade-truth pass if accepted together.
- No new live defect requires `/qa`/`/testing` routing: the one live defect
  found in-context (non-injective GOT mint) is already filed (FIXME 0748)
  with a pinned witness.
