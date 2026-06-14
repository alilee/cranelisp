# Sprint 83: Clean & Green III — representation-first data model + ledger-zero before Phase H

**Status**: PHASE 5 LANGUAGE (ACTIVE) — Wave 0

**Goal**: Pay the root cost of the recurring "180-locations" cross-field-invariant churn by making `ModuleEntry` callability *structural* (illegal state unconstructable), land the cross-module constrained-fn-call feature that reshape naturally enables, and clear every remaining actionable carry — the 2 reds, the display leak, the ResourceSerial fixture, and the post-D43 audit — so Phase H opens against a zero ledger.

## Scope

S82 ("Clean & Green II") closed at **2607 pass / 2 fail / 0 skip** — the 2 reds being the `0351` guards. The reinstated Phase-6 assessment also surfaced `0354` (a cross-module constrained-call SIGSEGV), fixed in-sprint with an **SSOT-accessor stopgap** (`callable_got_slot()` reads around the illegal state). The user's close-note pushed on the structural root: construction is buildered but reads are ~514 raw `ModuleEntry::Def` pattern-matches / ~435 `got_slot` mentions with no read chokepoint, so a cross-field invariant ("constrained template ⟹ no callable slot") is enforced only by read-discipline and recurs whenever a reader forgets.

This sprint is the **full pre-Phase-H decks-clear** (user direction, S83 planning) with the **full structural reshape now** (user direction, S83 planning). Three workstreams.

### Workstream A — Representation-first data model (the architectural spine)

The `0357`→`0356`→`0355` bundle, sequenced so the Principle decision gates the reshape and the reshape lands with the feature (avoids churning the same surface twice — the FIXMEs explicitly argue bundling).

1. **`0357` (/arch) — decide the candidate Principle (gating first step).** *Model a cross-field invariant as a sum type whose variants are exactly the legal states* ("parse, don't validate"); intent-accessor + sole-writer is the explicit FALLBACK only where the sum-type collapse is genuinely blocked. Decide the Principle + its discriminator boundary (correlated-few-states → sum type; genuinely-independent → leave flat), inventory cross-field invariants in `cranelisp-types` boundary types (start `ModuleEntry`/`SymbolTable`), and pick the `got_slot` representation. **/sprint + /arch read: Option A** (move `got_slot` INTO `DefKind` — slot on callable kind variants; `ConstrainedTemplate`/`Macro` slot-less). **Amends Decision 0035** (flat single-`got_slot`-field SSOT) — record the amendment, don't reverse silently.

2. **`0356` (/arch→/dev) — make callability structural.** Restructure `DefKind`/`ModuleEntry` (**Option A** — `got_slot` onto the callable `DefKind` variants) so `Def{got_slot:Some} + constrained_fn:Some` is **unconstructable**; the `callable_got_slot()` accessor becomes a trivial present-or-absent read on the matched kind variant (contract unchanged, body changes), and the S82 stopgap (`mark_constrained_template` flip-and-clear + `assert_well_formed` phantom-slot assert) retires. **Timing wall RESOLVED (Phase 2): defer slot allocation past Pass-2 detection** (no `Pending` variant) — Pass-1 `register_defn_signature` registers without a slot; the slot allocates at the determination point (end of Pass 2 for unconstrained; per-mono-variant for constrained). **Preserve the redefinition `existing_slot` carry-forward** (use-after-free guard — reuse, don't reallocate). Cascade is **~50–75 reader sites** (one semantic reader: backend `resolve_got_target`; rest storage/serde/codegen — mechanical), NOT ~180. Canonical surface = `module.rs` rustdoc + `bounded-contexts.md §7` + `interfaces.md`; regenerate `cranelisp-types/public-api.txt` (DefKind variant-payload shape changes — check cache-version bump for the serialized `DefKind` shape).

3. **`0355` (/typecheck + /backend) — cross-module constrained-fn calls RUN.** Make constrained-fn detection + `pass4_monomorphise` collect call sites for **imported** callees chain-resolving to a constrained `Def`; re-check the mono body in its **defining module's** import context (not the caller's); wire the generated mono entry (`cmp$Int+Int`) + its trait-method callees into the caller's GOT. Upgrade `tests/spec_07_traits.rs::cross_module_stacked_trait_bound_call_runs_to_clean_exit` from "no SIGSEGV" to "runs to exit 2". This is the feature half of the resolved `0354`; the Option-A "concrete-shape-owns-the-slot" model is the natural home for `cmp$Int+Int`'s own slot.

### Workstream B — Clear the reds + display leak

4. **`0351`×2 (/typecheck) — the only 2 current reds.** (a) **Field-name accessor as free callable**: `(deftype Box [:Int v])` then `(v b)` errors `undefined variable: v`. **Spec §5.2.6 already confirms** accessors ARE auto-generated free functions (`x :: (Fn [Point] Int)`) — NO `/spec` gate needed (Phase 2 Revision 1); this is a direct `/typecheck` resolution defect (the accessor exists per spec but is not resolvable as a free variable). (b) **Self-qualified type reference**: `:superp/Box` inside `superp.cl` errors `unknown type` — a module must resolve its own types by FQ name (§8.5). Both have RED repros already (single-file, S82). Fix flips them green.

5. **`0352` (/backend) — `/list` leaks raw type vars.** `/list` renders `id : (Fn [t1] t1)` instead of the normalized `(Fn [a] a)` the definition-display/`/sig` paths produce (violates repl/spec.md §1.4). Route `/list` per-symbol scheme rendering through the same normalize+qualify renderer. Failing e2e repro lands with the fix (`tests/repl_negative.rs::list_neg_no_raw_type_vars`). Flag the unqualified-`Int` question to /repl/spec if abbreviation is by design.

### Workstream C — ResourceSerial fixture + post-D43 audit

6. **`0353` (/platform + /qa) — ResourceSerial token-serialization e2e witness.** Add ResourceSerial functions to `cranelisp-test-capture` (e.g. `test-resource-sleep-ms` taking token + duration, `SchedulingClass::ResourceSerial`); `/qa` authors a timing e2e asserting same-token≈2× and diff-token≈1× wall-clock (`// spec: spec/10-io.md §10.12.4`). The runtime-dispatch remainder of `0135` — no source defect implied, only the missing witness fixture.

7. **`0101` (/sprint schedules; audit-discipline pass) — post-D43 crate audits.** Audit passes over **`cranelisp-primitives`, `cranelisp-intrinsics`, `cranelisp-platform`** (NOT the retired `cranelisp-runtime` — re-scoped at S82 per D43). Produce `audits/{crate}-2026-NN-NN.md` in the established 4-crate format (per-file responsibility map, hidden-coupling check, monolith candidates, HIGH/MEDIUM/LOW findings + remediations, current/target diagrams). File remediation FIXMEs from findings (targets are forward-flow, not necessarily this sprint).

## Out of scope — assigned to Phase H

Phase H (Release Compiler) is the **release phase** — genuinely-new capability + release-polish:
- **Tier-2 backend** (`--release`) — the new-capability item.
- **`0050`** (List/Seq pretty-printer → MUST) — needs a type-directed **display protocol** (display trait + backend dispatch + stdlib impls); release-polish.
- **`0052`** (`/learn` in-REPL guided tutorial) — REPL feature + `user/tutorial/` authoring; release-polish.

These have a home phase; they are not S83 deferrals with TBD targets.

## FIXME debt

| FIXME | Target skill | Status | Workstream |
|---|---|---|---|
| 0357 | /arch | open | A (Principle decision — gates A) |
| 0356 | /arch (→ /dev cascade) | open | A (callability structural) |
| 0355 | /typecheck (+ /backend) | open | A (cross-module mono feature) |
| 0351 | /typecheck (no /spec gate — §5.2.6 settles (a)); (b) may re-point /arch after isolation | deferred (target S83) | B (2 reds) |
| 0352 | **/int (RE-POINTED from /backend — Phase 3: renderer is in `src/display.rs` since S66)** | open | B (/list display) |
| 0353 | /platform + /qa | open | C (fixture + timing e2e) |
| 0101 | /sprint → audit pass | deferred (target this sprint) | C (post-D43 audits) |
| 0050 | /dev src/ | deferred | Phase H (display protocol) |
| 0052 | /repl | open | Phase H (/learn tutorial) |

## Architecture review (Phase 2)

**Reviewer:** `/arch` (Compiler Architect). **Date:** 2026-06-14. **Verdict: APPROVE-WITH-REVISIONS.** The spine (Workstream A) is technically coherent, the user-chosen full-reshape-now direction is sound, and the gating decisions below unblock Phase 3. Three revisions are required (one scope relaxation in B, one estimate correction in A, one wave-sequencing tightening); they sharpen the plan, none invalidate it. Workstreams B and C are coherent and confirmed clear of the spine surface.

### Source-vs-FIXME divergences found (verified against `crates/cranelisp-types/src/module.rs` + workspace grep)

The FIXMEs' field-shape claims are accurate, but two **quantitative** claims are inflated and one **B-workstream gate** is unnecessary:

1. **The "~180 reader sites" / "~514 `Def` sites / ~435 `got_slot` mentions" cascade is overstated.** Actual measured shape: only **51** sites name `got_slot` inside a `ModuleEntry::Def { … }` construct/match, **25** raw `.got_slot` dot-field reads (excluding the unrelated `next_got_slot` allocator counter and `linker.rs`'s own separate `got_slots: HashMap`), and **56** `ModuleEntry::def(` builder call sites. The bulk of `ModuleEntry::Def` matches use `..` rest-patterns and never name `got_slot` — moving the field into `DefKind` leaves them **untouched**. The real cascade is **~50–75 sites**, not 180. (The 435/514 figures conflate the allocator counter, the linker's own concept, and rest-pattern matches.)
2. **There is exactly ONE semantic call-resolution reader** of callability — `cranelisp-backend::compiler::mod.rs:181` (`resolve_got_target` via `callable_got_slot()`). Every other `got_slot` site reads the index for **storage / serde / codegen / allocation** — mechanical. The accessor-read discipline the FIXMEs imply is pervasive is in fact a single production seam (the S82 stopgap was added at exactly that one site).
3. **`0351`(a) does NOT need a `/spec` arbitration.** `spec/05-definitions.md §5.2.6` "Generated Accessors" already states affirmatively: *"For each named field in a type definition, an accessor function is automatically generated in the enclosing scope. The accessor's name is the field name"* with `x :: (Fn [Point] Int)` examples. The question the SPRINT draft routes through `/spec` is already settled in the spec. **Revision 1 below.**

### Gating decision 1 — Principle ratified (Principle 20)

**RATIFIED.** Authored as `design/arch/principles/20-model-invariants-by-representation.md`; index row added to `principles.md`; import line added to all four blocks (arch + design + dev + review per the principles-dir new-Principle discipline). **Discriminator boundary:** *correlated fields with few legal states → sum type; genuinely independent fields → leave flat.* The cross-field-invariant test is "is there a field combination that is constructable but meaningless?" — yes ⟹ sum type, no ⟹ flat. Principle 20 is the **cross-field species of Principle 18** (structural-over-behavioural): the sum type is the structural mechanism for correlated fields; the intent-accessor + sole-writer (Principle 18's single-source-of-truth form) is the explicit, recorded fallback used only where the collapse is genuinely blocked, and is then a *bridge* to the representation form, never the destination.

### Gating decision 2 — representation: Option A (got_slot INTO DefKind)

**CHOSEN: Option A** — move `got_slot` onto the callable `DefKind` variants (`UserFn` concrete-callable form / `Primitive` / `Constructor`); non-callable kinds (`UserFn`'s constrained-template form, `Macro` parent, `PlatformEffect`, `PrimitiveExtern`, `Overloaded` base) carry no slot field. Justification:

- **Principle 7 (single source):** the slot stays the single GOT-indexed home for a callable address; A moves it to where its *determinant* (callability = a kind property; `constrained_fn` already lives in `DefKind`) lives, rather than splitting determinant and datum across sibling fields. B/C both keep two kind-ish discriminators (B grows the outer `ModuleEntry` enum and forces factoring `Def`'s shared payload for a one-field problem; C nests a `Callability` enum that reads less directly than inlining).
- **Principle 18/20 (structural):** A makes `Def{slot}+template` **unconstructable** — the strongest form. B achieves the same but at higher disturbance; C achieves it with an extra indirection.
- **Principle 6 (budget):** A's only honest cost is `got_slot` repeating across callable kinds (acceptable duplication — each callable kind genuinely owns a slot) and the Decision-0035 amendment. B inflates the already-large `ModuleEntry` enum; C adds a type for a problem inlining solves.
- **Source confirms A fits:** `Def`'s shared payload (`scheme`/`visibility`/`docstring`/`param_names`/`callees`/`seq`/`ast`/`code`) is untouched; only `got_slot` relocates. The `DefBuilder` gains a kind-aware slot setter (or the slot rides on the `DefKind` value passed to `ModuleEntry::def`), and the 56 builder sites adapt mechanically.

**Decision 0035 amendment recorded** at its manifestation sites (not a new Decision file, per CLAUDE.md "no separate Decision log"): BC §7 "Callability is structural" paragraph rewritten; `interfaces.md` callable-address paragraph rewritten; `design/arch/CLAUDE.md` Decisions-drain backlog line 0035 annotated with the S83 placement amendment. The amendment is **placement-only** — GOT remains the single source of truth for addresses; the slot index moves from a flat `Def` field to the callable kind variants. The rollback's flat-field choice was correct against the rejected sibling-`fn_ptr` alternative; it is superseded against the correlated-invariant alternative.

### Gating decision 3 — timing wall: DEFER slot allocation past Pass-2 detection

**RESOLVED: defer allocation** (Principle 20 resolution form 1), NOT a `Pending` interstage variant. Concretely: typecheck Pass 1 (`register_defn_signature`, `program.rs:2036`) registers the signature/scheme **without** allocating a GOT slot — the unconditional `st.allocate_got_slot()` + `got_slot` write at that site is removed. The slot is allocated at the point callability is determined: for an unconstrained defn, at end of Pass 2 (constraint detection at `program.rs:867/1040` found no constraints → allocate + construct the concrete-callable `UserFn` variant carrying the slot); for a constrained defn, **no module-local slot** — its mono variants allocate their own slots at `monomorphise_call` (already the case). The entry between registration and determination simply has no slot, which is **correct** — nothing may call it before its callability is known.

**Why not `Pending`:** the deferral is local (one Pass-1 site, two Pass-2 sites) and cheap; the `UserFn` discriminator's `constrained_fn: Option<_>` already names the determined state; the entry is not call-resolvable in the interim regardless, so an explicit interstage variant would add surface for no reader. The S82 `mark_constrained_template()` flip-and-clear sole-writer **retires** (no sibling slot to clear) and `assert_well_formed()`'s phantom-slot assertion retires with it. **Caution for Phase 5:** the redefinition `existing_slot` carry-forward at `program.rs:2030–2036` (use-after-free guard preserving an existing slot across REPL redef) must be preserved — the deferred-allocation path must still reuse an existing concrete callable's slot on redefinition rather than reallocating. This is the one non-mechanical seam in the cascade; flagged for `/design` (typecheck) + `/design` (types) attention in Wave 1.

### Gating decision 4 — cascade is mechanical (one semantic reader)

**CONFIRMED mechanical, with one named semantic seam.** Corrected estimate: **~50–75 sites** (not 180) — 51 `Def{…got_slot…}` constructs/matches + 25 `.got_slot` reads + 56 builder sites, with heavy overlap. Of these, exactly **one** is a semantic callability reader (`compiler/mod.rs:181` `resolve_got_target`), and it reads through `callable_got_slot()` whose **contract is unchanged** (returns the slot for a callable, `None` otherwise) — only its body changes (match the kind variant instead of reading-around a flat field). Everything else is storage/serde/codegen/allocation: mechanical pattern-arm rewrites (read the slot off the matched callable `DefKind` variant instead of the flat field). **Public-API delta to `cranelisp-types/public-api.txt`:** the `DefKind` variant payloads change shape (callable variants gain `got_slot`); `ModuleEntry::Def` loses its `got_slot` field; `mark_constrained_template` removed, `assert_well_formed` simplified/removed, `callable_got_slot` retained. Regenerate `public-api.txt` per the baseline-diff discipline in the SAME change-set as the reshape (Wave 1). `serde` round-trip: the `#[serde(default)]` on the old flat field is replaced by the variant-carried slot — cache `.meta.json` shape changes; confirm cache-version bump if the serialized `DefKind` tag/shape changes (flag for `/design` backend-cache).

### Gating decision 5 — 0355 interface impact: NO new boundary item

**0355 needs NO new `cranelisp-types` boundary item beyond the Option-A reshape.** It is a typecheck-internal mono-collection change + a backend GOT-wiring change against the existing surface:
- **Typecheck (internal):** constrained-fn detection + `pass4_monomorphise` collect call sites for *imported* callees that chain-resolve to a constrained `Def` (follow the import chain via `resolve_terminal_entry_and_home`); `recheck_body_for_mono` re-checks the mono body in its **defining module's** import context. This is logic inside `cranelisp-typecheck`, no boundary type added.
- **Backend (existing surface):** the generated `cmp$Int+Int` mono entry is an ordinary concrete `UserFn` `Def` owning its own `got_slot` (Option A's "concrete-shape-owns-the-slot" — the reshape is exactly the natural home), and its trait-method callees wire into the caller's GOT via the existing per-module GOT mechanism. **Clean `/backend` follow-on once the correctly-scoped mono entry exists** — no new interface item. The only dependency is ordering: the mono entry must be correctly scoped (typecheck) before backend can wire it.

### Required revisions to scope

1. **Workstream B, item 4 (`0351`(a)) — drop the `/spec`-confirms-first gate.** `spec/05-definitions.md §5.2.6` already states field accessors are auto-generated free functions (`x :: (Fn [Point] Int)`). Reframe as a direct `/typecheck` resolution fix (the accessor exists per spec; it is not resolvable as a free variable — a typecheck/resolution defect). Optionally file a confirmatory `/spec` note, but it does **not** gate `/typecheck`. This removes a Wave-0 dependency edge.
2. **Workstream A — correct the cascade estimate from "~180" to "~50–75 sites, one semantic reader".** The reshape is smaller than the FIXMEs framed; the wave plan should not budget 180-site effort.
3. **Wave 1 sequencing — name the two non-mechanical seams explicitly:** (a) the redefinition `existing_slot` carry-forward (deferred-allocation must reuse, not reallocate); (b) the cache/serde `DefKind` shape change (possible cache-version bump). Both go to `/design` (types + typecheck + backend-cache) in Wave 1 before the mechanical cascade.

### Interim-architecture risk (Principle 8)

**The timing-wall resolution is a DURABLE shape, not interim.** Deferring allocation to the determination point is the representation-correct form ("parse, don't validate" at the boundary) — it is the destination, not a bridge. The S82 accessor stopgap was the interim form; this sprint retires it. No Principle-8 concern. The Option-A duplication of `got_slot` across callable kinds is honest (each callable genuinely owns a slot), not interim debt.

### Sequencing recommendation for Phase 4

- **Wave 0 (gates A):** Phase-2 decisions are landed (this section + Principle 20 + BC §7 + interfaces.md + Decision-0035 annotation). Phase 3 `/design` fans out: types (Option-A `DefKind` reshape + builder), typecheck (deferred allocation + carry-forward seam), backend (one-reader rewrite + cache-shape). `0101` audit read-only fan-out runs parallel. `0351`(a) needs NO `/spec` gate (Revision 1) — `/qa` drafts the exit-2 / reds / display / timing failing tests.
- **Wave 1 (the reshape):** `cranelisp-types` Option-A reshape + `public-api.txt` regen (same change-set) + the two named non-mechanical seams resolved FIRST, THEN the ~50–75-site mechanical cascade across typecheck/backend/src (serial, shared tree — suite stays green on the two `0351` guards). The S82 stopgap retires here.
- **Wave 2:** `0355` feature (typecheck cross-module mono + backend GOT wiring against the now-reshaped surface); `0351` typecheck fixes; `0352` backend display. These depend on Wave 1's reshaped surface but are otherwise independent of each other.
- **Wave 3:** `0353` platform fixture + qa timing e2e; `0101` audit findings → remediation FIXMEs.

## Skill plans (Phase 3)

> Phase-3 design fan-out complete (5 read-only planning agents: /design ×4 crates + /qa). Plans condensed below; the recommended design-doc refinements land in Phase 5 Stage 2 (per-crate /design re-fire). **Three Phase-3 findings adjust scope — see "Phase-3 findings" in Notes.** No `/spec` agent fired (no language semantics change — §5.2.6 settles 0351(a); §10.12.4 covers 0353; §8.5 covers 0351(b)).

### /arch — cranelisp-types (owns the reshape; Phase-2 decisions stand)

- **Wave-1 interface detail to nail down:** the exact `DefKind`/`UserFn` encoding. Typecheck flagged this as the **single Wave-1 agreement point** — the representation must support three states: Pass-1 not-yet-determined (slot-less), determined-concrete (`got_slot` mandatory, non-`Option`), determined-constrained (slot-less). Recommended shape: `UserFn` has a concrete-callable form carrying `got_slot: usize` and a constrained form carrying no slot; the Pass-1 interim state is the absence of a determined callable payload (NOT a separate `Pending` enum arm — gating decision 3). `callable_got_slot()` answers `None` for both interim and constrained, `Some` for concrete/`Primitive`/`Constructor`. `mark_constrained_template` + `assert_well_formed` retire. Regen `cranelisp-types/public-api.txt` in the Wave-1 change-set.

### /design+/dev cranelisp-typecheck — 0356 (tc half), 0355, 0351(a)+(b)

- **0356 deferred allocation:** Pass-1 `register_defn_signature` (`program.rs:2029–2061`) registers slot-less (remove the unconditional `allocate_got_slot()`). Slot allocates at the determination point: unconstrained arm (`program.rs:857–862` single / `:1021–1026` multi) → allocate + construct concrete `UserFn`; constrained arm (`:867–883` / `:1028–1042`) → construct slot-less constrained variant. **The one non-mechanical seam:** the redefinition `existing_slot` carry-forward moves from Pass-1 to the determination point — a new `existing_callable_slot(st, name)` helper reads the prior entry's concrete slot and the unconstrained arm REUSES it (use-after-free guard); concrete↔constrained transitions handled explicitly. Keep a `debug_assert` on slot-reuse (replaces retired `assert_well_formed`).
- **0355 cross-module mono (no new boundary type):** broaden `pass4_monomorphise` (`program.rs:2110`) to collect call sites for *imported* callees chain-resolving to a constrained `Def` via `resolve_terminal_entry_and_home` (carry the `home_module` on each call site; relax the `constrained_fn_names.is_empty()` early-return). `recheck_body_for_mono` (`traits.rs:1493`) + `get_constrained_fn` (`:1571`) + `resolve_inner_constrained_calls` (`:1525`) thread `home: &ModuleFullPath` and **save/restore `state.current_module` to the home** around the body re-check (so `show`/`str-concat` resolve in the defining module). The home is a committed import → live view; no staging shadow. Produces a concrete `cmp$Int+Int` `UserFn` Def owning its own slot → backend wires it.
- **0351(a) accessor:** synthesise an accessor `UserFn` `Def` per product field in `register_constructors` (`adt.rs:299`, product arm `:355`) — body = single-arm `match` over the product ctor (backend already lowers `Expr::Match`; NO `FieldAccess` node, NO new boundary type, NO backend change). Born concrete (slot at synthesis, like ctors). Scheme `(Fn [ProductType] FieldType)`. Flips the existing red. **Collision policy is an open edge** (user-binding shadow; cross-type duplicate field names) — negative coverage; file `/spec` clarification only if /dev hits it.
- **0351(b) self-qualified type:** the empty-`from_module` error signature suggests EITHER typecheck key-composition (`resolve_type_expr_in_module` leaf, `checker.rs:2114`) OR a `cranelisp-types::resolve` visibility/self-home bug (`current_module == home` must bypass the private-visibility gate). **Author the cross-crate-isolation unit FIRST** (resolve.rs fixture) to assign ownership; if `cranelisp-types`-owned, file FIXME `target: /arch` (do NOT edit it from typecheck).
- **Dependency:** items 0356/0355/0351(a) gate on the Wave-1 types reshape compiling first. 0351(b) is reshape-independent.

### /design+/dev cranelisp-backend — 0356 (backend half), 0355 (GOT wiring), cache bump

- **0356 one semantic reader:** `resolve_got_target` (`compiler/mod.rs:172–183`) calls `callable_got_slot()` whose **contract is unchanged** — only the accessor body (types-owned) changes. Backend's edit here is **rustdoc-only** (the phantom-slot rationale retires). ~8 mechanical readers (`trace_codegen.rs:308–347`, `cache/mod.rs:374`, `jit.rs:124/138/1386` + test builders) read the slot off the callable variant — pattern-arm rewrites. `allocate_got_slot` counter + `cache/linker.rs got_slots` are unaffected (the false-positives the inflated counts conflated).
- **Cache version bump 4→5** (`cache/mod.rs:142`) — REQUIRED by the no-serde-change-without-bump rule; the `DefKind` payload + `ModuleEntry::Def` shape change. Without it, v4 `.meta.json` could silently load `got_slot=None` for a callable → NULL-slot regression (the exact bug Principle 20 forecloses). Invalidation is automatic (`CacheStale::SchemaMismatch` → recompile). Lands in the Wave-1 change-set with the types reshape.
- **0355 GOT wiring: NO new path** — the generated concrete `cmp$Int+Int` Def is picked up by the existing mono GOT-population path (`derive_codegen_batch` + `jit.rs`), identical to the already-working plain-parametric cross-module mono. Gated on typecheck scoping the entry first.

### /design+/dev src/ (int) — 0356 (int cascade), 0352 (RE-POINTED here), 0355 (no change)

- **0356 int cascade:** ~12 mechanical `got_slot` reader sites in `src/worker.rs`/`exe.rs`/`expander.rs` (sort key, GOT-population, linker registration, `lookup_got_slot`/`lookup_got_target`) — pattern-arm rewrites; ZERO semantic callability readers in `src/`. **The int half of the non-mechanical seam:** the redefinition carry-forward in `worker.rs::commit_staging_to_live` (~`:353–360`) — pairs with typecheck's `program.rs:2030–2036`. The `DefBuilder` slot-setter consumer (`worker.rs:~1505`, `exe.rs`, `expander.rs`) adapts to the Wave-1 reshaped builder API. Cache `CacheStale` already routes to recompile-as-miss at `process_form.rs:~1847` + `session_v4.rs:~1143` (verify-only, no change).
- **0352 (RE-POINTED /backend → /int):** fix at `src/repl.rs::handle_list` (~`:670`, `format!("{}", scheme.ty)` → the normalize+qualify renderer). Extract a shared `format_scheme_type`/`format_def_scheme` in `src/display.rs` (Principle 7 — single source feeding both `/list` and definition-display). Closes BOTH leaks (`t1`→`a` AND `Int`→`primitives/Int`), dissolving the "abbreviation by design?" question. **Independent of the reshape** — can land any serial window.
- **0355:** **NO int code change** — committed-import live view + commit-atomic staging + retry-from-top dep-gap already carry the generated mono variant.

### /design+/dev cranelisp-platform — 0353 fixture

- Add `resource-serial-sleep-ms (token, ms) -> (IO Int)` to `cranelisp-test-capture` (`platforms/test-capture/src/lib.rs`) via `CLIO::effect_on_resource(token, sleep)` — combines the token-placement of `resource_serial_noop` with the timing-observability of `commutative_sleep_ms`. One `declare_platform!` `functions:` entry, `scheduling: SchedulingClass::ResourceSerial`, sig `(Fn [primitives/Int primitives/Int] (primitives/IO primitives/Int))`. Caller-supplied token (lets /qa choose same vs different). No new ADT, no schema/layout-hash churn, no `cranelisp-platform` core change. The fixture GATES the /qa e2e.

### /qa — test plan + harvest of remaining guards

- **Wave-0 failing-first:** 3 new 0351(a) e2e (first-class-value-passable + 2 negatives: user-binding shadow, cross-type duplicate field name) + the 2 existing reds (`generated_field_accessor_resolves_as_free_callable`, `self_qualified_type_reference_resolves_to_local_type`) ride as baseline. **NOT Wave-0:** 0355 exit-2 flip, 0352 repro, 0353 timing — these are alongside-fix (flipping them in Wave 0 would inject reds the pure Wave-1 reshape can't clear, breaking its green gate).
- **Alongside-fix:** 0355 → upgrade `cross_module_stacked_trait_bound_call_runs_to_clean_exit` to `.assert_exit(2)` + a new `--link` companion; 0356 → redefinition slot-reuse unit (the named seam), cache-v4→`CacheStale` NULL-slot guard, constrained-template structural guard (re-point existing `module.rs` test); 0352 → `list_neg_no_raw_type_vars` asserting BOTH `!contains("t1")` AND `contains("primitives/Int")`; 0353 → `resource_serial_same_token_serializes` (elapsed > 1.5× duration) + `..._diff_token_parallelizes` (< 1.5×), `--run`+`--link`, ≥100ms/call, structural-inequality not tight-ratio.
- **Cross-crate-isolation owed:** 0351(b) ownership-assigning unit BEFORE the fix.
- **Fixture risk:** the 0351(a) accessor synthesis adds a free callable per product field → audit `/list`-membership / entry-count fixtures (0243 lineage) for *correct* count growth in the same change-set as the 0351(a) fix.
- **Baseline:** S83 starts 2607 pass / 2 fail (the 0351 reds) / 0 skip; closes at ≥2607+new green / 0 fail / 0 skip. A genuine regression = any red beyond a named in-flight guard, or a pass-count drop on the pure Wave-1 reshape.
- **0101 audits:** read-only audit-authoring (no tests); defect-grade findings → failing-not-ignored repros per the defect protocol.

## Waves (Phase 4)

Phase 2 ratified the shape (see Architecture review §"Sequencing recommendation"). Source-editing serial (shared tree); read-only audit fan-out parallel:
- **Wave 0** — Phase-2 decisions LANDED (Principle 20 + Option A + defer-allocation timing-wall + BC §7/interfaces.md/Decision-0035 annotations). Phase 3 `/design` fan-out: types (Option-A DefKind reshape + builder), typecheck (deferred allocation + carry-forward seam), backend (one-reader rewrite + cache-shape). 0351(a) needs NO /spec gate (§5.2.6 settles it). /qa drafts failing tests (0355 exit-2, 0352 repro, 0353 timing once fixture exists). 0101 audit read-only fan-out runs parallel here.
- **Wave 1** — `cranelisp-types` Option-A reshape (got_slot onto callable DefKind variants; 0356) + `public-api.txt` regen (same change-set); resolve the TWO named non-mechanical seams FIRST (redefinition `existing_slot` carry-forward; cache/serde `DefKind` shape + possible version bump), THEN the ~50–75-site mechanical reader cascade across typecheck/backend/src/ (serial, suite stays green on the 2 known guards). S82 stopgap retires here.
- **Wave 2** — 0355 feature (typecheck cross-module mono + backend GOT wiring against the reshaped surface — no new interface item); 0351 typecheck fixes; 0352 backend display.
- **Wave 3** — 0353 platform fixture + qa timing e2e; 0101 audit findings → remediation FIXMEs.

## Notes

- S83 planning opened from a between-sprints state (S82 closed clean: 2607 pass / 2 fail = the `0351` guards / 0 skipped).
- **User direction (S83 planning):** full pre-Phase-H decks-clear (Workstreams A+B+C, not the focused spine alone); **full structural reshape now** (do 0357 Principle + 0356 Option A *with* the 0355 feature, not the SSOT-accessor-holds path).
- **This sprint moves `cranelisp-types`** (the `got_slot`→`DefKind` reshape) — unlike S82 which required no types change. Baseline-diff discipline applies (regen `public-api.txt` + BC §7 + interfaces.md in the same change-set).
- The S82 SSOT accessors (`callable_got_slot`/`mark_constrained_template`) are the line-holder that this sprint pays down to the representation form; they retire when 0356 lands.

### Phase-3 findings (design fan-out, S83) — adjust scope vs Phase-2

1. **`0352` re-points `/backend` → `/int`.** The scheme renderer migrated to `src/display.rs` in Sprint 66; `cranelisp-backend` has no scheme-display renderer. The fix is wholly an int change (`src/repl.rs::handle_list` → `src/display.rs` shared renderer). FIXME 0352 target updated. The single fix closes both the `t1` and unqualified-`Int` leaks (the "abbreviation by design?" repl-spec question dissolves — no /spec gate).
2. **`0351`(b) may be `cranelisp-types`-owned, not typecheck.** The empty-`from_module` error signature could mask a `resolve` visibility/self-home bug. A cross-crate-isolation unit is authored BEFORE the fix to assign ownership; if types-owned, a FIXME `target: /arch` is filed (do not edit cranelisp-types from typecheck).
3. **`0355` needs NO int code change** (confirmed from the int/scheduler perspective) and **NO new `cranelisp-types` boundary item** (confirmed Phase 2) — it is typecheck (mono collection + defining-module-scoped re-check) + backend (existing mono GOT path). No `0342`-class load-ordering hazard: the home module is a committed import.
4. **The one non-mechanical seam is two-sided:** the redefinition `existing_slot` carry-forward lives in BOTH typecheck (`program.rs:2030–2036`) and int (`worker.rs::commit_staging_to_live`) — they must be reconciled together in Wave 1 (reuse the prior concrete slot; never reallocate / never carry a phantom).
- **Net:** S83 still moves `cranelisp-types` (the reshape) + adds `/int` (0352 re-point); no new boundary type; no /spec authoring.

## Outcome (Phase 7)

### Delivered
- {what shipped}

### Deferred (with rationale)
- {item — why deferred, target sprint, escalation count}

### Findings (record in FIXMEs if not already)
- {unexpected observations, methodology lessons, skill feedback}
