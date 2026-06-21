# cranelisp-types — Sprint 87 Stage-B deep audit (delta + currency pass)

> **What this is.** The S87 Stage-B per-crate deep-audit pass for `cranelisp-types`
> (the `/arch`-owned cross-crate interface crate — boundary DTOs, `Type`,
> `FQSymbol`/`FQTypeName`, error types, `SymbolTable`/`GotTable`/`View` facade).
> Run by `/review` per `sprints/SPRINT.md §"Stage B"` (Wave 1b, the 7-lens pass).
> READ-ONLY on code; findings route to `/arch` (the crate owner) via the Stage-B
> backlog / FIXME store. This is a **delta + currency check** on the deep baseline
> `design/arch/facades/types-audit-s69.md`, NOT a from-zero look.

**Audit surface**: `crates/cranelisp-types/src/*.rs` — corrected **3,035** non-test
LOC (`audits/loc-s87.md`); `module.rs` (685 corrected) is the one concentration;
otherwise broadly distributed, consistent with a DTO/interface crate.

**Baseline**: `design/arch/facades/types-audit-s69.md` (59 findings; the S69 facade
audit, the deepest prior look at this crate).

**Date**: 2026-06-20 · **Auditor**: /review (cranelisp-types narrow deployment)

**Headline.** The crate is in **strong structural health** on six of seven lenses —
clean boundary hygiene (every module `pub(crate)` with explicit `pub use`),
near-zero production panics, newtype discipline intact, no interim-arch residue in
the DTO core. **The one material finding is lens (i) duplication: the type→string
rendering logic has proliferated to FIVE implementations across three crates with
TWO divergent primitive-mapping conventions.** This is the S86 FQ-rendering-
triplication seed, and it is now worse than "triplicated." The consolidation
recommendation below is the deliverable for the Wave-2 /arch synthesis.

---

## 0. Baseline reconciliation (S69 → S87 currency)

The S69 audit's 59 findings resolved to these disposition classes: 27 source-moves,
7 facade-moves, several RESOLVED-by-deletion, etc. **Two things have changed the
landscape since S69:** (1) the facades were all retired (`facades/types.md` retired
S69 Sub 42 → `bounded-contexts.md §7` + source rustdoc), so "facade drift" findings
no longer have a facade target — they reconcile against BC §7 + rustdoc; (2) the
S87 lens checklist is interior-structural, not facade-vs-source, so the reconciliation
is "did the source-move land / does the smell persist," not "do the two docs agree."

| Baseline finding (cluster) | S69 disposition | S87 status | Evidence |
|---|---|---|---|
| **SymbolTable concurrency complex** — H3/H5/H6/H7, S-DRIFT-19/20/21, C-HOLE-5 (DashMap inner storage + `&self` interior-mutable writes `write_code`/`insert_or_update`/`install_import_bindings`/`write_structural_decls` + `next_got_slot: AtomicUsize` + `next_seq: AtomicU64`) | **source moves** (the biggest cluster) | **STILL OPEN — un-migrated** | `module.rs:102` `symbols: HashMap<Symbol, ModuleEntry<C>>` (not DashMap inner); `:106` `next_got_slot: usize`; `:128` `next_seq: u64` (the rustdoc at `:118` explicitly says facade target is `AtomicU64`, conversion deferred); writes are `&mut self` (`insert` `:603`, `allocate_got_slot` `:577`, `append_structural_decl` `:590`) — none of the named `&self` methods exist |
| **FQTypeName binding (Decision 47)** — S-DRIFT-1/9/13, H8 | source moves | **RESOLVED / held** | `Scheme.constraints: HashMap<TypeId, Vec<FQTraitName>>` (`types.rs:154`); `Type::ADT(FQTypeName, …)` (`types.rs:24`); `Type::adt` is the one bare-name→FQ lift, pinned by `test_adt_construction_is_fully_qualified` (`types.rs:421`) |
| **H1** — operator.rs relocation to primitives | source moves | **RESOLVED** | no `operator` module in `cranelisp-types/src/` |
| **U22 / HeapCategory relocation to backend** | RESOLVED by relocation | **RESOLVED** | `heap.rs:1` stub comment confirms relocation; only `HeapHeader` retained (`lib.rs:267`) — the genuine cross-crate layout contract |
| **C-HOLE-4** — `string_newtype!` inner `pub String` | mechanical (drop `pub`) | **RESOLVED** | `newtype.rs:11` `pub struct $name(String)` — private inner |
| **C-HOLE-6** — `pub mod → pub(crate)` submodules | mechanical | **RESOLVED** | `lib.rs:177-204` all submodules `pub(crate)`; only `pub mod test_support` (`:214`, justified) |
| **FQ-rendering split kept distinct** (the post-Wave-0 /arch advisory) | S86 seed / Wave-2 question | **OPEN — proliferated further** | see Finding 1 |

**Reconciliation summary.** Of the baseline clusters, the **SymbolTable concurrency
complex remains the single largest open source-move** — three full sprints (S70–S86)
have passed without the DashMap-inner-storage + interior-mutable-`&self`-write
migration landing. The mechanical/relocation findings (H1, U22, C-HOLE-4/6) **all
resolved**. FQTypeName binding **held**. The one finding that has gotten *worse*
since the baseline is FQ-rendering duplication (Finding 1).

---

## Findings (severity-ranked)

### Finding 1 — [IMPORTANT] Type→string rendering is FIVE implementations across three crates with TWO primitive conventions (lens i — duplication; Principle 7) — **THE HEADLINE**

**This is the S86 FQ-rendering-triplication seed, and it is now five-fold, not three.**

The five renderers, all walking the same 7-variant `Type` enum:

| # | Function | Location | Primitive convention | `Type::Var` | Status |
|---|---|---|---|---|---|
| 1 | `impl Display for Type::fmt` | `crates/cranelisp-types/src/types.rs:108` | **bare** (`Int`) | `t{id}` | live |
| 2 | `format_type_display` → `format_type_with_vars` | `crates/cranelisp-types/src/types.rs:182,188` | **bare** (`Int`) | `a,b,c…` | **DEAD export** (see Finding 2) |
| 3 | `format_type_fq` | `crates/cranelisp-typecheck/src/unify.rs:141` | **FQ** (`primitives/Int`) | `t{id}` | live (Wave-0) |
| 4 | `format_type_qualified_inner` | `src/display.rs:181` | **FQ** (`primitives/Int`) | `a,b,c…` | live |
| 5 | `format_type_with_inline_constraints` | `src/display.rs:239` | **FQ** (`primitives/Int`) | `a,b,c…` | live |

**The divergence is real and load-bearing.** Two output conventions for the primitive
variants: renderers #1/#2 emit bare `Int`/`Bool`/`String`/`Float`; renderers #3/#4/#5
emit `primitives/Int` etc. (per `repl/spec.md §5.3`). Both conventions are *correct
for their context* — #1's bare `Display` feeds debug/internal sites; #3/#4/#5's FQ
feeds user-facing type-error and REPL display. But the **structural walk over the
`Type` enum is copy-pasted five times.** Each renderer independently matches all 7
variants (`Int`/`Bool`/`String`/`Float`/`Fn`/`ADT`/`Var`/`TyConApp`), independently
formats `(Fn [params] ret)`, independently formats `(ADT args)` / bare-ADT, and
independently recurses. The `unify.rs:141` rustdoc even *documents* the duplication
as deliberate ("This deliberately duplicates the primitive→`primitives/…` mapping…
the /arch Phase-2 keep-distinct advisory").

**The recurrence tell** (per `memory/feedback_review_root_cause_and_duplication`): the
Wave-0 fix (`format_type_fq` @ `unify.rs`) was individually correct — it fixed the
type-error renderer to emit FQ names per spec §5.3. But it is a **symptom patch that
deepened the duplication**: a fourth (now visible as the third FQ-convention) walk of
`Type` was *added* rather than the existing FQ walk in `display.rs` being shared. The
SPRINT.md Wave-0 task note acknowledges this ("the /arch Phase-2 keep-distinct
advisory") — the keep-distinct decision was made *consciously*, but it is a
five-copy-walk debt that the Wave-2 synthesis must now adjudicate. The "adjacent
instances" SPRINT flagged for Stage B (`unify.rs:135` occurs-check; `traits.rs:1157`/
`:1804` no-impl via `concrete_type_name` which **strips the module**, `traits.rs:2202`)
are the *same* class — every type-name-into-a-message site reinvents the walk.

**Why it belongs HERE (cranelisp-types).** `Type` is defined here. Every one of the
five renderers depends on this crate. This is the **one place all five could call**
— and the only place a shared helper does not create a new cross-crate dependency
(typecheck and src/ both already depend on types; a shared helper in types is
dependency-free for them). Renderer #1 (`Display`) and #2 (`format_type_*`) already
live here.

**Proposed consolidation (the Wave-2 recommendation — see §"FQ-rendering recommendation").**
Introduce ONE parameterised walk in `cranelisp-types::types` that takes a small
config (primitive-naming: bare vs `primitives/`-qualified; var-naming: `t{id}` vs
lettered-via-`type_var_names`); the five sites become thin callers selecting the
config. The structural `Type`-walk lives once; the two conventions become two
argument values, not two copy-pasted match blocks. `Display` delegates to it (bare
config); `format_type_fq` and `display.rs`'s two renderers delegate to it (FQ
config). This is the textbook Principle-7 single-source consolidation, and the
"keep-distinct" advisory survives intact — the *output conventions* stay distinct
(they're config values), only the *walk* unifies.

**Severity rationale**: Important, not Blocker — the duplication is correct-as-shipped
(no behavioural bug) but is the highest-leverage maintainability debt in the crate's
dependency cone: a new `Type` variant (or a change to `Fn`/`ADT` rendering) today
requires editing five sites in three crates, and the two-convention split invites
exactly the kind of "fixed it in one place, the others still wrong" drift the S86
defect campaign surfaced. Routes to **/arch** (Type is `/arch`-owned; this is a
cross-crate consolidation decision for the synthesis).

---

### Finding 2 — [IMPORTANT] `format_type_display` / `format_type_with_vars` are DEAD public exports (lens ii — dead paths; the `produce_disasm` class)

`format_type_display` (`types.rs:182`) and `format_type_with_vars` (`types.rs:188`)
are `pub` and re-exported (`lib.rs:228`, in `public-api.txt:1526-1527`) but have
**zero production consumers anywhere in the workspace.** The only call sites are
their own in-crate tests (`types.rs:647-688`) and the internal `format_type_display
→ format_type_with_vars` delegation. `src/repl.rs:1824/1897`'s `format_type_display`
is an **unrelated** `pub(crate)` method on the REPL struct (different signature:
`(&self, type_name: &str, module)`), not the free function.

This is exactly the dead-path class the S87 lens (ii) names (the `produce_disasm`
zero-call-site finding, and the live precedent of FIXME 0418 — the `symbol_disasm`/
`Introspection.disasm` dead machinery deleted in Wave 0). These two functions are
the bare-primitive lettered-var renderer that nobody calls: the user-facing path uses
`display.rs`'s FQ renderers (#4/#5), and the internal path uses `Display` (#1).

**Note the entanglement with Finding 1**: `type_var_names` (`types.rs:163`, also
exported) **IS** live — `src/display.rs:116,150` call it. So the consolidation must
*keep* `type_var_names` while *retiring* `format_type_display`/`format_type_with_vars`
(or folding their lettered-var capability into the Finding-1 unified walk as a config).
They are not independently load-bearing; they exist only because the unified walk
doesn't.

**Proposed resolution**: delete both `pub fn`s + their `lib.rs:228` re-export +
their `public-api.txt` lines + their tests, OR fold their lettered-var behaviour into
the Finding-1 unified renderer (preferred — the capability is wanted, the standalone
dead exports are not). Per the baseline-diff discipline (`design/arch/CLAUDE.md`),
the `public-api.txt` regeneration lands in the same change-set. Routes to **/arch**
(public surface of an `/arch`-owned crate), bundled with Finding 1.

---

### Finding 3 — [IMPORTANT] SymbolTable concurrency complex un-migrated 3 sprints past the baseline source-move ruling (lens vi — interim-arch residue; Principle 8)

The S69 baseline's single largest source-move cluster (H3/H5/H6/H7, S-DRIFT-19/20/21,
C-HOLE-5) target-states: DashMap-inner storage, `&self` interior-mutable writes
(`write_code`/`insert_or_update`/`install_import_bindings`/`write_structural_decls`),
`next_got_slot: AtomicUsize`, `next_seq: AtomicU64`. The configuration grounds this
unambiguously (Decisions 31/32/41/44 + the `concurrency-symbol-table-entry.mmd`
sequence diagram). **Source remains at the pre-migration shape:**

- `module.rs:102` — `symbols: HashMap<Symbol, ModuleEntry<C>>` (the outer container
  IS a DashMap — `SymbolTables = DashMap<ModuleFullPath, SymbolTable>` at `:288` —
  but the per-entry inner storage the baseline targets is a plain `HashMap`).
- `module.rs:106` — `next_got_slot: usize` (target: `AtomicUsize`).
- `module.rs:128` — `next_seq: u64` (target: `AtomicU64`; the field's own rustdoc at
  `:118-120` admits "The facade target is `AtomicU64` … the conversion lands as part
  of the broader" migration — a documented-deferred interim).
- Writes are `&mut self` (`insert` `:603`, `allocate_got_slot` `:577`,
  `append_structural_decl` `:590`); **none** of the named `&self` interior-mutable
  methods exist.

This is **Principle-8 interim-architecture residue by the letter**: the field rustdoc
documents a known-deferred conversion. It is not a *defect* — the `&mut self` +
plain-`HashMap` model is internally consistent and the suite is green — but it is the
crate's largest standing debt against its own committed target, and it has now
survived S70/S71/S72/.../S86 untouched. **The currency question for /arch:** is the
DashMap-inner + atomic + `&self`-write target still the intended end-state, or has
the architecture converged on the simpler `&mut self`-per-`SymbolTable`-behind-outer-
DashMap model as *sufficient* (in which case the baseline ruling + the rustdoc
deferral notes + the sequence diagram should be retracted)? Three sprints of
non-migration is itself evidence the simpler model may be adequate. Routes to
**/arch** — this is a target-state currency decision, not an implementation defect.

**Severity rationale**: Important. Either the migration is owed (then it should be
scheduled) or the target is stale (then the Principle-8 residue framing + the
deferral rustdocs should be cleaned up). The limbo is the finding.

---

### Finding 4 — [SUGGESTION] `concrete_type_name` (typecheck) strips the module — the no-impl message regression seam (lens i — adjacent to Finding 1)

`crates/cranelisp-typecheck/src/traits.rs:2202` `concrete_type_name` maps
`Type::ADT(fqtn, _) → Some(fqtn.name.clone())` — **dropping the module**, then the
no-impl trait error (`traits.rs:1143`, `:1796`) renders the bare local name. This is
the SPRINT-flagged "deeper reconstruction" adjacent instance of the §5.3 FQ concern:
a `(no impl of Eq for Color)` message shows bare `Color`, not `user/Color`, which
is exactly the ambiguity the Wave-0 `format_type_fq` fix corrected for type-mismatch
messages. It is a *sixth* place type-name-into-a-message logic lives, and it has a
*third* convention (strip-to-bare-local). When Finding 1's unified renderer lands,
this site should consume it (with the FQ config) rather than `concrete_type_name`'s
strip. Flagged here for the Wave-2 synthesis as part of the same root-cause family;
the fix is typecheck-local (**/dev typecheck**) once the shared renderer exists.

---

### Finding 5 — [SUGGESTION] Two `unreachable!`s in production paths are invariant-guards (lens iii/vi — acceptable, recorded for completeness)

Production code is otherwise panic-free. Two `unreachable!` sites:
`got.rs:82` (`.unwrap_or_else(|_| unreachable!("invariant: vec has GOT_TABLE_SIZE
elements"))` — fixed-size array conversion, structurally guaranteed) and
`ast.rs:436` (`Defn::body_mut()` on a multi-sig defn — caller-contract guard with a
descriptive message). Both carry justification messages and guard genuine invariants
(not error cases). **No action** — these meet the bar (`expect`-with-justification
equivalent). Recorded so the next pass doesn't re-flag them.

---

### Finding 6 — [SUGGESTION] `module.rs` at 3,707 raw / 685 corrected is the crate's one concentration (lens iii — function/file budget)

`module.rs` holds `SymbolTable`, `ModuleEntry`, `DefKind`, `ImportSpec`/`ExportSpec`/
`ImportNames`, `StructuralDecls`, `ModDecl`, `PlatformSpec`, and the lifecycle
primitives — the entire symbol-table state model in one file. At 685 corrected LOC
it is not over-budget for a *file* (the inline tests are 852 LOC, 55% — a healthy
test-to-prod ratio), and the cohesion is real (it is "the symbol-table model"). **No
split recommended** — flagged only as the one place future accretion should be
watched. If `DefKind` / the import-spec family grows further, a `module/entry.rs` +
`module/import.rs` split would be the natural seam. Boundary hygiene is clean (the
module is `pub(crate)`; only named items re-export). No finding beyond the watch-note.

---

## FQ-rendering consolidation recommendation (the S86 seed → Wave-2 /arch deliverable)

**Recommendation: CONSOLIDATE the structural walk into `cranelisp-types`; keep the
output conventions as configuration, not as separate copies.**

The Wave-0 /arch advisory ("keep them separate") was correct *about the output
conventions* — bare-`Int` (debug/`Display`) and `primitives/Int` (user-facing §5.3)
are genuinely different contracts and must not collapse into one. But "keep separate"
was applied to the *implementations*, producing five copy-pasted `Type`-enum walks
across three crates with the structural-walk logic (the `(Fn […] …)` / `(ADT …)`
formatting, the recursion, the 7-variant match) duplicated each time. That is not
sustainable: it is the Principle-7 violation the S86 campaign repeatedly paid for, and
adding `format_type_fq` in Wave 0 *deepened* it.

The reconciliation that honours both: **one parameterised walk in
`cranelisp-types::types`** taking a config — `{ primitive_naming: Bare |
Qualified, var_naming: Numbered | Lettered(&var_names) }` (and, if the
`display.rs` inline-constraints renderer #5 is folded in, an optional constraint
map). The five sites collapse to thin config-selecting callers:

- `impl Display` (#1) → unified walk, `Bare` + `Numbered`.
- `format_type_fq` (#3, typecheck) → unified walk, `Qualified` + `Numbered`. **The
  cross-crate boundary disappears** — typecheck calls a types-crate fn instead of
  re-implementing.
- `display.rs` #4/#5 → unified walk, `Qualified` + `Lettered`. (#5's inline
  constraints stay a `display.rs`-local concern layered over the shared walk, or
  become a third config field.)
- `format_type_display`/`format_type_with_vars` (#2, Finding 2) → **deleted**; their
  lettered-var capability becomes the `Lettered` config.

**Why types, not typecheck or src/.** `Type` is defined in types; both other crates
already depend on types; a helper here is dependency-free and is the single point all
five renderers reach. Renderers #1 and #2 already live here. Placing it anywhere else
either creates a new dependency or leaves `Display` (which must stay in types) as a
sixth copy.

**Net for the synthesis:** one structural walk, two (or three) named conventions as
values, the keep-distinct advisory preserved *at the output level*, the
cross-crate duplication of the *walk* eliminated, and Finding 2's dead exports
retired in the same change-set. This is the same single-resolution-seam shape the
synthesis is chartered to find on the DEF-1 side (`SPRINT.md §"S86 hot-spot seeds"`)
— here applied to type rendering. **Severity: Important; owner /arch; scope:
cross-crate (types + typecheck + src/); ships with `public-api.txt` regen per the
baseline-diff discipline.**

---

## Prior-findings status counts (baseline reconciliation summary)

Reconciled against the S69 baseline's named clusters (not all 59 individual findings —
the facade-vs-source findings no longer have a facade target post-retirement; they
reconcile against the source-move direction):

| Status | Count | Clusters |
|---|---|---|
| **RESOLVED** (source-move landed / relocation done / mechanical fix applied) | 4 | H1 (operator relocation), U22 (HeapCategory→backend), C-HOLE-4 (newtype inner-`pub`), C-HOLE-6 (`pub(crate)` submodules) |
| **HELD** (target shape in place, no regression) | 1 | FQTypeName binding (D47 — S-DRIFT-1/9/13, H8) |
| **STILL OPEN — source-move un-migrated** | 1 | SymbolTable concurrency complex (H3/H5/H6/H7, S-DRIFT-19/20/21, C-HOLE-5) → Finding 3 |
| **OPEN — proliferated since baseline** | 1 | FQ-rendering duplication (the S86 seed) → Finding 1 + Finding 2 |

**New (S87-surfaced, not in the S69 baseline):** Finding 2 (dead `format_type_*`
exports), Finding 4 (`concrete_type_name` strip-to-bare seam), Finding 5/6
(acceptable invariant-guards / file-concentration watch-note).

---

## 7-lens coverage ledger (this pass covered all seven)

| Lens | Result |
|---|---|
| (i) duplicated code paths / mirrors | **Finding 1** (FQ-rendering ×5), **Finding 4** (`concrete_type_name` seam) — the crate's headline debt |
| (ii) dead paths (the `produce_disasm` class) | **Finding 2** (`format_type_display`/`format_type_with_vars` dead exports) |
| (iii) function/file-budget overruns | **Finding 6** (`module.rs` concentration — within budget, watch-note); no over-budget function found |
| (iv) RC-symmetry (Decision 24) | N/A for this crate — types holds DTOs + `HeapHeader` layout contract, no RC-consuming-inc sites (RC lives in backend/intrinsics) |
| (v) resolution-seam consolidation | `resolve.rs` `split_qualified` (`:493`) is the single shared qualified-name seam with the FIXME-0328 non-empty-part guard intact (`:486-494`, `canonical_symbol` `:604`); **clean — single seam, no duplication** |
| (vi) interim-arch residue (Principle 8) | **Finding 3** (SymbolTable concurrency complex documented-deferred); **Finding 5** (acceptable guards) |
| (vii) cross-crate-boundary / host-callback hygiene | Boundary clean — all submodules `pub(crate)`, explicit `pub use` re-exports (`lib.rs:177-291`), only `pub mod test_support` (justified), no `cranelisp_*` re-exports of sibling crates' items (Principle 3 clean, bottom-of-DAG hygiene holds). **The one cross-crate hygiene concern is Finding 1** — typecheck reaching past the boundary by *re-implementing* a `Type` walk instead of calling one |

---

## Next skills

- `/arch` — owns this crate + the cross-crate consolidation decision; Findings 1, 2,
  3 all route here; Finding 1 + the consolidation recommendation are the Wave-2
  synthesis input (FQ-rendering single-seam, the type-rendering analogue of the DEF-1
  resolution-seam question).
- `/dev typecheck` — Finding 4 (`concrete_type_name` no-impl message) once the shared
  renderer from Finding 1 exists.
