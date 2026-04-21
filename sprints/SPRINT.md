# Sprint 60: Clean & Green — JIT/Object Codegen Convergence + FIXME Drawdown

**Status**: ACTIVE
**Ring**: 4 (Effects — stabilisation)
**Goal**: Zero carried failing tests + FIXME drawdown. Close the JIT vs object codegen divergence as the architectural root cause of the S59 carry cluster, resolve the S59 /review Importants, and clear the priority FIXMEs blocking observability and developer ergonomics. Success opens the path for Sprint 61's FQTypeName migration.

## Scope

Sprint 59 closed at **~1801 passed / 5 failed / 0 ignored**. All 5 failures trace (by working hypothesis) to a single architectural issue: **same source produces different behaviour between the JIT direct-finalize path and the `.o`-relocation + link-loading path**. This violates the intended invariant that JIT and object codegen differ ONLY in the fixup mechanism, not in the emitted code. Sprint 60 is framed to make that invariant real.

Alongside the primary workstream, Sprint 60 clears the highest-value FIXME debt: observability infrastructure blocking diagnosis (CLIF dump), cache-staleness defence against compiler rebuilds (build marker), three S59 /review Importants, and Ring 4 acceptance-criterion gaps (examples `--run` path broken, `/sig` docstring display gap).

### Workstreams

- **A (primary, `/arch` + `/backend`) — JIT/object codegen invariant audit + divergence root-cause.** `/arch`-driven audit confirms the "same source → same code bytes" invariant and identifies where it breaks. `/backend` root-causes against the three hypotheses in `design/backend/defects-456-reduction.md`:
  1. Monomorphised defn codegen context divergence across module boundaries
  2. Auto-curry closure-over-polymorphic-dispatch RC contract mismatch between paths
  3. Cross-module GOT drop-glue `func_addr` interacting with Decision 31 JIT-page reclaim (currently most-likely given the raw-trap-no-stderr signature)

  Expected test flips: `wave6_demo_repros::exemplar_solver_does_not_stack_overflow_on_small_puzzle`, `wave6_demo_repros::run_tests_batched_invocation_no_crash`, `sprint59_defects456_repro::d45_html_min_v1_no_crash`, `sprint59_defects456_repro::d6_exemplar_propagate_only_does_not_segv`, `sprint59_defects456_repro::d45_solution_cell_single_call_no_rc_underflow`.

  Requires a design doc at `design/backend/jit-object-convergence.md` authored in Phase 3 before implementation; `/arch` reviews for Decision 23 (two-GOT model) + Decision 25 (cache shape) + Decision 31 (JIT reclaim) + Decision 36 (linkage) alignment.

- **B (secondary infrastructure, `/backend`) — CLIF-dump observability.** Wire `CRANELISP_CODEGEN_TRACE=1` (or a new `CRANELISP_CODEGEN_DUMP=<module>` variant) to actually dump human-readable CLIF IR for the specified module/function. The S59 `defects-456-reduction.md` Phase-2 conclusion names this as load-bearing for diagnosing Workstream A — without it, reduction past a certain point becomes guess-and-check. Small; lands early in the sprint to unblock A's root-causing.

- **C (secondary infrastructure, `/backend`) — Object-file build marker for cache invalidation across compiler rebuilds.** Extend `CACHE_SCHEMA_VERSION` (Decision 34) with a compile-time build-id derived from `env!("CARGO_PKG_VERSION")` + `option_env!("GIT_SHA")` via `build.rs`. `.meta.json` carries the build-id; cache-load rejects on mismatch. ~50 LOC across `build.rs` + `cache/mod.rs`. Prevents a recurring "mystery cache staleness" diagnosis cost across compiler rebuilds.

- **D (dependent, `/port`) — Defect 7 re-enable.** Blocked on A's Defect 6 closure. Re-enable 3 puzzle tests in `exemplar/solver.cl` once the solver stack-overflow fix lands.

- **E (quality, `/int` + `/backend`) — S59 /review Importants.** Three first-time-deferred items from `design/review/sprint-59-wave-1.md`:
  - **E-1 (`/int`)**: `recurse_into_transitive_deps` at `src/worker.rs:~1637` is a 6th per-dep prologue site that the Workstream-A `register_dep` shim missed. Migrate to the shim.
  - **E-2 (`/int`)**: `register_dep_for_eval` passes `delays_other=false` while worker-side sites pass `true`. Divergence at `src/session_v4.rs:1307`. Reconcile.
  - **E-3 (`/int`)**: Restore the deleted unit guard `compile_dep_inline_publishes_sexps_before_register` under the shim so the structural property remains test-guarded.

- **F (quality, `/stdlib` primary; `/examples` validates) — Examples `--run` path remediation.** Ring 4 acceptance-criterion gap: `cargo run -- --run examples/FOO.cl` fails for 27 of the 27 `.cl` files in `examples/` because they use bare primitive names (`add-i64`, `eq-i64`, etc.) not exposed by the stdlib prelude re-export shell. `tests/examples.rs` currently green via a test-fixture prelude. Resolution: either (a) expose the missing primitive names through the stdlib prelude (if coherent with prelude philosophy), or (b) rewrite the 27 examples to use the prelude-exposed operator names. `/stdlib` + `/examples` co-decide in Phase 3; decision recorded in the design doc (either stdlib prelude update or examples audit).

- **G (quality, `/repl` + `/int`) — `/sig` docstring display gap.** `/sig add` on a docstring'd defn shows `:(Fn [Int Int] Int) add ; defn` — dash + docstring omitted. `repl/spec.md §1.1` mandates the universal format with docstring. Small format fix, likely in `src/session_v4.rs` introspection path. `/repl` spec-audits; `/int` implements.

- **H (prior-ring coverage, `/qa`) — `[Tested+Neg]` promotions.** Phase 1 coverage audit will enumerate candidates; prioritise MUST/MUST NOT requirements currently `[Tested]` but not `[Tested+Neg]`. Target 3–5 promotions this sprint.

### Out of Scope (deferred with rationale)

- **FQTypeName migration** — **Sprint 61 primary workstream** (roadmap updated). Precondition: S60 closes with 0 carried failing tests. Not deferred indefinitely; sequenced immediately after stabilisation.
- **Performance baseline / benchmark infrastructure** — Ring 4 AC `Performance within 2x of prototype` NOT MEASURED. Dedicated S62+ sprint candidate (criterion harness, prototype-parity benchmarks, CI reporting). Incoherent with stabilisation focus.
- **Long-session memory profiling** — Decision 31 Scenario 2 reclaim verified by unit test; field observation of long sessions belongs after stabilisation.
- **Decision 30 module-system redesign** — parent↔child typecheck deadlock lift. Future research, not on roadmap. Workaround (`discover-tests` builtin) documented.
- **Stdlib prelude monolith remediation** — stdlib-focused sprint; may fold into F if the examples resolution requires prelude surgery, otherwise S62+.
- **BL range fix**, **Ring 4 RC-balance adoption completion** — roadmap-deferred to S62+.
- **Phase H / Tier 2 release backend** — post-Ring-4, blocked on Ring 4 baseline green (this sprint's close is a precondition).

### `/int` Burden Assessment

**MODERATE.** Primary load is on `/backend` (Workstreams A + B + C). `/int` carries Workstream E (focused cleanup; 3 small, well-scoped changes), possibly Workstream G (1-line format fix), and review/sentinel duty for Workstream A. No Step-5c-scale sweeps. If Workstream A surfaces integration-layer touches (e.g., `Code` enum adjustments for redefinition edge cases), burden could escalate — `/int` flags during Phase 3 design review and `/sprint` re-scopes with user approval before implementation.

### Direct failure-fixing expectation

| Failure | Owner | Workstream | Expected clearance |
|---|---|---|---|
| `wave6_demo_repros::exemplar_solver_does_not_stack_overflow_on_small_puzzle` | `/backend` | A (Defect 6) | Yes |
| `wave6_demo_repros::run_tests_batched_invocation_no_crash` | `/backend` | A (Defects 4+5) | Yes |
| `sprint59_defects456_repro::d45_html_min_v1_no_crash` | `/backend` | A | Yes |
| `sprint59_defects456_repro::d6_exemplar_propagate_only_does_not_segv` | `/backend` | A | Yes |
| `sprint59_defects456_repro::d45_solution_cell_single_call_no_rc_underflow` | `/backend` | A | Yes |

**Target**: **0 carried failing tests** at close (plus 3+ new passing neg-coverage tests from Workstream H). This is the milestone that unblocks Sprint 61's FQTypeName migration.

## FIXME Debt

Phase 1 scan (preliminary; full inventory in progress). In-scope for this sprint:

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `design/backend/defects-456-reduction.md` §Phase 2 | `/backend` | CLIF-dump infrastructure gap | **Workstream B** |
| (new) `crates/cranelisp-backend/build.rs` | `/backend` | Object-file build marker | **Workstream C** |
| `src/worker.rs:~1637` | `/int` | `recurse_into_transitive_deps` 6th prologue site | **Workstream E-1** |
| `src/session_v4.rs:1307` | `/int` | `delays_other` divergence | **Workstream E-2** |
| (deleted) `compile_dep_inline_publishes_sexps_before_register` | `/int` | Unit guard restoration | **Workstream E-3** |
| `exemplar/solver.cl` (3 puzzle tests) | `/port` | Re-enable after Defect 6 | **Workstream D** |
| 27 × `examples/*.cl` OR `stdlib/prelude.cl` | `/stdlib` + `/examples` | `--run` path broken since S1 | **Workstream F** |
| `src/session_v4.rs` introspection path | `/int` | `/sig` docstring display gap | **Workstream G** |
| `tests/sprint23.rs:1126-1131` | `/int` | Misattribution comment cleanup (S59 Wave 1 finding) | **Bundled into E** |

Pre-existing FIXMEs not in scope: stdlib monolith remediation, `/docs` survey items, BL range fix, Ring 4 RC-balance adoption, Decision 30 research — all roadmap-deferred per the §Out of Scope rationale.

## Architecture Review

**Reviewer**: `/arch`
**Verdict**: APPROVED WITH CONDITIONS

### Coherence

Sprint 60 is a coherent stabilisation increment. The five carry failures share a single working hypothesis ("same source → different behaviour across JIT direct-finalize and `.o`+relocation+link-load paths"), so framing the sprint around a single architectural invariant rather than five independent defect hunts is the right call. The acceptance surface is concrete (5 failing tests flip green + 3+ new neg-coverage tests) and the Sprint 61 precondition gate ("0 carried failing tests before FQTypeName migration lands") is falsifiable at close.

**One realism caveat on the "0 carried" target.** Sprint 59 Pass 2 (`design/backend/defects-456-reduction.md` §Resolution) documents that the crash is intermittent (~75% reproduction rate, raw trap with no stderr) and has resisted two focused fix attempts across two sessions. Workstream A therefore carries genuine root-cause risk: either the invariant audit quickly localises the divergence (best case: the fix is a targeted finalize-path alignment, tests flip, sprint closes on target) or it surfaces a structural change larger than the sprint budget allows (e.g., a codegen-uniformity retrofit). The sprint frames this correctly — Workstream A is design-doc-gated (Phase 3) and the /int burden-escalation path is explicit — but `/sprint` should be prepared at the Phase 3 review to re-plan if the design doc's scope exceeds ~3-day implementation. The "0 carried" target holds; the sprint's feasibility of hitting it depends on Workstream A landing with a bounded fix surface.

Workstream sequencing is sound: B (CLIF-dump) lands EARLY in Wave 1 to unblock A's root-causing — this is correctly specified and is load-bearing per `defects-456-reduction.md` §Phase 2 (CLIF-dump-infrastructure-gap FIXME). C is orthogonal infrastructure. D is correctly gated on A. E is close-time cleanup. F/G/H are parallel-safe quality items.

### Principle 8 (no interim architecture)

Workstream-by-workstream scrutiny:

- **A (JIT/object convergence)** — Converges ON the Decision 23 + 36 target ("same CLIF, two resolvers"). The existing divergence IS the interim infrastructure, and this sprint removes it. Principle 8 compliant.
- **B (CLIF-dump)** — Observability primitive that the `design/backend/defects-456-reduction.md` §Phase 2 FIXME explicitly names as load-bearing for A. Small (env-var-gated hook on the per-defn codegen path), reusable for all future RC/codegen debugging, NOT throwaway. Principle 8 compliant.
- **C (object-file build marker)** — **Needs scrutiny.** The rationale is "prevent mystery cache staleness across compiler rebuilds." This is defensive infrastructure — it addresses a recurring diagnosis cost, not a user-visible correctness defect. Two framings:
  - *Acceptable*: If Decision 34's `CACHE_SCHEMA_VERSION` protocol already specifies that manual bumps are required on shape changes but developer discipline has been imperfect (evidenced by the specific mystery-staleness cost that motivates C), then an automatic build-id extension is a Principle-5 (testability) strengthening of the existing Decision 34 contract — not interim, a refinement.
  - *Unacceptable*: If C is being added because developers want to avoid ever bumping `CACHE_SCHEMA_VERSION` manually, it displaces the manual-bump discipline Decision 34 requires and becomes a substitute rather than a complement.
  - **Resolution**: C is approved provided the commit message / `cache/mod.rs` comment clarifies that the build-id is an **additional** invalidation trigger, not a substitute for `CACHE_SCHEMA_VERSION` bumps on explicit shape changes. See Condition 3.
- **D/E/F/G** — Bugfixes + cleanups against the committed shape. Principle 8 compliant.
- **H** — Tests against committed spec. Principle 8 compliant.

### Design references

Per-skill design-ref completeness:

- **`/backend` (Workstream A)** — Refs listed (`defects-456-reduction.md`, `ring2-rc.md`, Decisions 23/25/31/36) are the right set. **Additions**:
  - **Decision 37** (cache-hit integration lives inside `register_module`'s recursive flow) — the §"canonical recursive flow" and the §"No swallowed failures" discipline are directly relevant to the object-path load-and-register-symbol sequence. If the divergence lives in how the cache-hit path populates GOT slots vs how JIT finalize populates them, Decision 37's contract is the normative reference.
  - **Decision 36** (bare names + `Linkage::Local`) is already listed but the design doc MUST audit whether any residual pre-S58 `user`/`main` asymmetry slipped through — the intermittent raw-trap-no-stderr signature is consistent with a relocation landing on a stale or wrong-linkage symbol.
  - `design/backend/compile-to-module.md` §17 (the `(Arc<Jit>, HashMap<Symbol, *const u8>)` result shape per Decision 35 Layer 2 Option B) — the convergence audit must verify that BOTH finalize paths produce the same shape result, consumed identically by the integration layer.
- **`/backend` (Workstream C)** — `CACHE_SCHEMA_VERSION` / Decision 34 must be cited; the build-id is an extension of the Decision-34 mechanism. Additionally: `build.rs` crate placement belongs in `cranelisp-backend` (where the cache lives), not the root workspace — confirm during Phase 3.
- **`/int` (Workstream E)** — `design/int/dual-path-persistence-collapse.md` §7 update for E-1 and E-2 is correctly called out. `repl/spec.md §1.1` for Workstream G is correct. Also: `design/int/symbol-table-generics.md` Wave 3b carry-forward section for any upsert-site touches.
- **`/qa` (Workstream H)** — No additions. Coverage audit is methodology-driven.
- **`/stdlib` + `/examples` (Workstream F)** — **Missing ref**: the stdlib plan doc (`design/stdlib/plan-stdlib.md` or wherever the prelude-philosophy is stated) must be cited by the co-decision. If no such doc exists, the co-decision must be recorded in a NEW design doc (`design/stdlib/examples-run-path.md`) before implementation.

### Interface gaps

**No boundary-type extensions required, conditional on Workstream A's fix surface staying within the existing interfaces.** The likely fix surfaces — all of which fit existing interfaces — are:

- **If hypothesis 1 (mono-codegen context divergence)**: fix lives inside `compile_to_module`'s monomorphisation path. Interface-internal. No `Code`/`CodeStore`/`SymbolTable<C, L>` change.
- **If hypothesis 2 (auto-curry over polymorphic dispatch)**: fix lives in the closure-codegen path inside `cranelisp-backend`. Interface-internal.
- **If hypothesis 3 (cross-module GOT drop-glue `func_addr` × Decision 31 reclaim)**: fix likely involves routing drop-glue `func_addr` through GOT indirection (per Decision 31's all-GOT-call discipline + the forward-commitment "callback platforms" sub-section). This is a codegen-path change inside `cranelisp-backend`, not an interface change.

**If Phase 3 design surfaces an interface need** (e.g., a new `Code` variant for a third retention-root kind, or a richer `CacheLoadError`, or a `Module` trait method to probe divergence), `/backend` MUST file it as a FIXME(/arch) in the design doc before implementation lands. `/arch` reviews the interface extension before any boundary-type change commits — the existing `SymbolTable<C, L>` shape is post-Wave-3b stable and further churn is high-cost.

### Hypothesis ranking

The draft lists three hypotheses from `defects-456-reduction.md` §"Still to resolve — architectural shape". The signature — **intermittent ~75% reproduction rate, raw SIGTRAP, no stderr, specific to imported polymorphic functions, REPL-typed equivalent works 5/5** — strongly implicates hypothesis 3 (cross-module GOT drop-glue with Decision-31 reclaim interaction) for the following reasons:

1. **Intermittency** matches an allocator/page-reclaim race: if drop-glue `func_addr` points into a JIT page that is reclaimed between evals, whether the call survives depends on whether the allocator has handed out those pages to a subsequent allocation that happens to land different bytes at the same VA. That is precisely the signature.
2. **No stderr** definitively rules out a Rust `debug_assert!` path (they always flush before abort). The raw trap strongly implies execution landed on invalid bytes — either freed JIT pages or a NULL-initialised GOT slot (Decision 37 §"No swallowed failures" anti-pattern).
3. **REPL-typed equivalence passes 5/5** — the REPL-typed defn lands in a single-pass codegen + single JIT batch, so its drop glue and its GOT target are in the same `Arc<Jit>` retention root. The imported version crosses batch boundaries: `cell-at` is in `grid`'s batch, `solution-cell` is in `html`'s batch, and the drop glue for the Cell ADT sits... where? If it sits in `grid`'s JIT but is called from `html`'s code, and `grid`'s `Arc<Jit>` reclaim interacts oddly with the redefinition-carrying upsert, the race opens.
4. **Decision 31 Scenario 2** explicitly names the carry-forward invariant that protects against exactly this class of race (`program.rs:2184-2232`). The fact that REPL redefinition is THE mutator of GOT slots (per Decision 31 safety invariant) and that the crash only appears for imported polymorphic functions is consistent with a path where cross-module imports reach drop glue via a mechanism that does NOT respect the carry-forward.

**Ranking: H3 > H1 > H2.** Hypothesis 3 is consistent with all five signature features simultaneously; H1 and H2 each explain subsets.

**Missing hypothesis — H4: GOT slot population NULL-sink (Decision 37 §"No swallowed failures")**. The pre-S58 `try_cache_hit_load` bug was that `linker.get_symbol(name)` could return `None` and the slot stayed NULL while the worker reported success. S58 Wave 2 deleted that path, but if **any** surviving codegen path still writes to a `ModuleEntry::Def.code` without having verified that the corresponding GOT slot was populated with a non-NULL pointer, calls through that slot will raw-trap. The intermittency could be explained by GOT-slot-population ordering across parallel codegen workers (Decision 37 §"Order-independence rationale" claims slot LAYOUT is pinned at typecheck but slot CONTENTS are written in codegen — if a caller's code lands before the callee's slot is populated, the call finds NULL). This is a Decision-37 surface, not a new phenomenon. Phase 3 design must include an audit of GOT-slot write/read ordering during parallel codegen against Decision 37 §"Order-independence" — not just JIT/object divergence.

### Phase 3 design-doc requirements — `design/backend/jit-object-convergence.md`

At minimum:

1. **§1 Invariant statement** — formal statement of the "same source → same code bytes, modulo fixup mechanism" invariant, citing Decision 23 (two-GOT model) and Decision 36 (bare-Local naming). What exactly IS expected to be identical (CLIF bytes? post-relocation native bytes? GOT slot targets?) and what IS expected to differ (relocation sites vs direct-patch sites).
2. **§2 Hypothesis audit** — walk through H1/H2/H3/H4 and for each, say how the convergence audit verifies or falsifies it. Name the CLIF-dump evidence required to make each determination (Workstream B makes this possible — reference explicitly).
3. **§3 Decision-37 alignment** — explicit section confirming that `compile_to_module`'s JIT and object paths share the same `register_module` recursive flow + codegen-phase symmetry, and that any post-codegen divergence (GOT-slot population, finalize mechanism) is itself the invariant's fixup-mechanism boundary. If the divergence lives at a different boundary, the design doc names it.
4. **§4 Decision-31 carry-forward audit** — examine the upsert at `program.rs:2184-2232` for both paths (fresh batch codegen + cache-hit load). Does the carry-forward fire in both? If not, what populates `Code::Linker` when a cache-hit load resolves a module that was previously fresh-batched? The design doc specifies.
5. **§5 Drop-glue retention audit** — for cross-module drop glue (Cell ADT drop glue called from `html` code), specify which `Arc<Jit>` (or `Arc<Linker>`) retains the drop-glue code pointer, and confirm that the retention root is reachable from every caller. This is the H3 hypothesis audit section.
6. **§6 GOT-slot population audit** — per Decision 37 §"No swallowed failures", audit that every code-writing path verifies non-NULL slot population before reporting codegen success. This is the H4 hypothesis audit section.
7. **§7 Sketch comparison** — per `design/arch/CLAUDE.md` "Sketch Consultation" discipline, the sketch's approach to JIT/object divergence (or its equivalent dual path) must be studied. The sketch's dual-batch/REPL-pipeline divergence was a known structural debt; the reimplementation diverges by construction (Decision 23's single pipeline), but the sketch's codegen-level RC/closure/cross-module patterns are still oracles. Document what the sketch does and why the reimplementation follows or diverges.
8. **§8 Test plan** — name which of the 5 failing tests each hypothesis resolution flips, and what the "convergence regression guard" is (the committed permanent test that would catch a future re-divergence).
9. **§9 Fix scope estimate** — before implementation, estimate LOC + days. If >500 LOC or >3 days, escalate to `/sprint` for potential Sprint 60 rescope.

### Conditions

1. **`/backend` (Phase 3, pre-implementation)** — `design/backend/jit-object-convergence.md` MUST contain the 9 sections enumerated above. `/arch` reviews the design doc before implementation lands. Absence of §4 (Decision-31 carry-forward audit) or §7 (Sketch comparison) blocks Phase 3 advancement.

2. **`/backend` + `/sprint` (Phase 3, post-design)** — The design doc's §9 Fix Scope Estimate is a Phase 3 gate. If the estimate exceeds ~3 days or ~500 LOC, `/sprint` re-plans Workstream A before implementation begins — possibly splitting into a hypothesis-specific fix for S60 + a broader convergence audit carry-forward. The "0 carried failures" target for S60 may need to accept "5 → 2 or 1 carried" if the convergence fix surface is structurally large.

3. **`/backend` (Workstream C, at commit)** — `cache/mod.rs` comment / commit message MUST clarify that the compile-time build-id is an **additional** cache-invalidation trigger, NOT a substitute for the manual `CACHE_SCHEMA_VERSION` bump Decision 34 requires on explicit serialised-shape changes. This prevents C from displacing the Decision-34 discipline.

4. **`/stdlib` + `/examples` (Workstream F, Phase 3)** — The prelude-expose-vs-examples-rewrite co-decision MUST be recorded in a design doc (either `design/stdlib/examples-run-path.md` or the existing stdlib plan doc, at `/stdlib`'s choice). Verbal / in-session decision is insufficient — the decision shape sets a precedent for "what belongs in the prelude" that future stdlib work will cite.

5. **`/sprint` (wave gate)** — Before advancing past the Phase 3 design wave, scan the Workstream A design doc for the 9 required sections (Condition 1) and the Fix Scope Estimate (Condition 2). Absence blocks Wave 1.

### Updates to design/arch/

None required for this review. If Workstream A's Phase 3 design surfaces a new decision (e.g., a "drop glue must route through GOT indirection" rule that generalises Decision 31's callback-platform forward commitment), `/arch` records it as a new Decision 38 at Phase 3 review time, not pre-emptively here.

### Phase 3a Design-Doc Review

**Reviewer**: `/arch`
**Artefact**: `design/backend/jit-object-convergence.md` (Workstream A, authored by `/backend`)
**Verdict**: **APPROVED WITH CONDITIONS** — doc is substantively complete; two FIXME(/arch) items in §9.4 resolved inline (see below); scope stays in-budget under the recommended audit-first phasing.

#### Condition 1 compliance — 9 required sections

All nine sections present and substantive, not heading stubs:

- **§1 Invariant statement** — formal, falsifiable (§1.3 names two concrete CLIF-diff / GOT-slot-address falsifiers). Table at §1.1 / §1.2 draws a tight boundary: one explicitly-bounded fixup-mechanism divergence, everything else bitwise-identical. Correctly cites Decisions 23, 31, 36, 37 plus `compile-to-module.md §17.1.1`. The invariant wording is normative (what MUST hold), not merely descriptive.
- **§2 Hypothesis audit** — H1/H2/H3/H4 each have prediction + audit procedure + falsify/confirm criterion + CLIF-dump dependency. §2.1 ranks H3 > H4 > H1 > H2 with signature-feature justification. H4's refinement (adds the "N_populated before scheduler-notify" invariant) is a useful architectural sharpening of Decision 37 §"No swallowed failures" to the fresh-build path.
- **§3 Decision-37 alignment** — explicitly names the post-register_module "two kernels" (`inline_jit_codegen_for_names` vs `load_cached_module_via_linker`) as the fixup-mechanism boundary. §3.3 correctly identifies three places the invariant can break (inside `compile_to_module`, in the post-call step, upstream of codegen) and names (c) as a `/frontend`/`/typecheck` escalation path if it fires — correct ownership framing.
- **§4 Decision-31 carry-forward audit** — **MANDATORY, present.** §4.3's finding is the most load-bearing architectural observation in the doc: the upsert carry-forward at `program.rs:2184-2232` does NOT fire through `restore_cached_module`'s wholesale table install. The `Arc<GotTable>` swap at install time is the precise shape a pre-existing cached GOT-base reference (baked into a prior JIT batch's finalize) could be invalidated by. §4.3's localisation is accurate and tractable.
- **§5 Drop-glue retention audit** — correctly identifies the three closure-drop-glue options (a/b/c) and recommends (a) GOT-indexed dispatch. §5.2 flags the inlined-vs-trampoline distinction — important: inline ADT field drops are straight-line code (no cross-JIT call), only closure drop-glue and depth-limit-fallback `emit_rc_dec` call the dealloc/glue as a function.
- **§6 GOT-slot population audit** — three silent-skip findings at `worker.rs:2886-2915` are architecturally sharp: they ARE the same shape Decision 37 §"No swallowed failures" closed on the cache-hit path (`worker.rs:3087-3101`), left open on fresh-build. §6.1's fix specification (mirror the cache-hit hard-error pattern + post-loop "every slot populated" assertion pre-notify) is the right remedy.
- **§7 Sketch comparison** — **MANDATORY, present.** §7.1 documents the sketch's two-codegen-paths shape (`sketch/src/codegen.rs` + `sketch/src/cache.rs:351+`). §7.2 correctly frames the reimplementation's divergence as Decision 23 by-construction elimination. §7.5's insight that H3 and H4 are NEW to the reimplementation (sketch had no per-batch reclaim, no parallel codegen) is important — the sketch is not an oracle here; §5.3 and §6.1 are Decision 31/37 extensions, not sketch ports. This section satisfies root `CLAUDE.md` "Sketch Consultation".
- **§8 Test plan** — maps all 5 failing tests to H3-primary with per-test sub-fix dependencies. §8.2's four regression guards (`same_source_produces_same_clif_for_jit_and_object`, `fresh_build_and_cache_hit_produce_matching_got_slot_contents`, `cross_module_drop_glue_routes_through_got_not_direct_func_addr`, `fresh_build_codegen_fails_loudly_if_any_slot_is_unpopulated`) are the durable convergence checks. Each cites the exact design-doc section it protects.
- **§9 Fix scope estimate** — **GATE CLEARED.** Per-hypothesis LOC/days, combined estimate, scope classification against the 3-day / 500-LOC threshold, and an explicit "audit-first phasing" recommendation that keeps Sprint 60 in budget. See Condition 2 assessment below.

No section is a heading stub. Conditions 1(§4) and 1(§7) — the two explicit block conditions — are satisfied.

#### Condition 2 — Fix Scope Estimate assessment

Estimate table (doc §9.1): H3 alone 150–250 LOC / 1.5–2.5 days; H3 + §4.3 + §6.1 combined 240–410 LOC / 2.25–4 days. The upper bound of the combined framing (4 days / 410 LOC) **does** exceed the 3-day threshold on the time axis but stays under the 500-LOC axis.

`/arch`'s Q1 answer below collapses the §4.3 uncertainty: `SymbolTable.got` is already `Arc<GotTable>`, so the fix path is an in-place-merge discipline change (~40–80 LOC) rather than a shape change (would have been 150+ LOC). This pulls the combined upper bound back to ~3 days / ~370 LOC. **Scope stays in budget under the audit-first phasing** the doc §9.3 recommends: Workstream B CLIF-dump lands Wave 1 early; H3 audit uses it; §6.1 fix lands (cheap, high-confidence); H3 fix lands; §4.3 fix lands last only if the audit confirms it triggers. Rescope **not required** provided /sprint honours the audit-first sequencing.

#### Answers to the two FIXME(/arch) in §9.4

**Q1 (is `SymbolTable.got` already `Arc<GotTable>`?)** — **YES.** `crates/cranelisp-types/src/module.rs:124`:
```rust
#[serde(skip, default = "default_got_arc")]
pub got: std::sync::Arc<GotTable>,
```
Wave 0 tests (`module.rs:906-980`) already exercise `got.base_ptr()` / `got.store_slot` / `got.load_slot` and verify base-pointer stability across mutation. The `base_ptr()` accessor returns a stable address for the lifetime of the `Arc<GotTable>` (i.e., until the last clone drops). **§4.3's fix path therefore does NOT require a `SymbolTable` shape change** — it requires a logic change inside `restore_cached_module` to merge slot contents in-place rather than swap the Arc (or equivalently, detect a pre-existing `symbol_tables[M]` entry and preserve its `got: Arc<GotTable>` across the install, populating the new cached table's slot layout into the preserved Arc). No interface review is needed; the fix lives in `src/worker.rs::restore_cached_module` + possibly a helper on `SymbolTable` for merge semantics. Condition 2 LOC estimate recalibrates downward as noted.

**Q2 (does existing `Linkage::Import` + `__cranelisp_got_{M}` mechanism cover drop-glue references?)** — **NO. Fixing H3 requires new codegen.** The current closure-construction site at `crates/cranelisp-backend/src/compiler/control_flow.rs:574-588` emits `builder.ins().func_addr(types::I64, glue_ref)` — a raw function address baked into the closure's `drop_glue_ptr` slot at construction time, resolved by Cranelift at finalize against the glue function's `Linkage::Local` declaration (line 850). The closure is then torn down via `call_indirect` on that raw pointer (`compiler/mod.rs:1229-1256`). The glue function lives in *whatever JIT compiled the closure* — if a closure constructed in `grid`'s JIT is later dropped in `html`'s scope after `grid`'s `Arc<Jit>` has reclaimed (Decision 31 Scenario 2), the raw `drop_glue_ptr` dangles. This is the precise H3 shape applied to closures rather than ADT drop-glue. The existing `Linkage::Import` + `__cranelisp_got_{M}` mechanism is currently used only for user-defn calls (`compile_to_module`'s cross-module call emission); it does **not** cover function-pointer *values* stored in data (closure `drop_glue_ptr` field). Fixing H3's closure-drop path therefore requires either: (a) §5.3 option (a) — replace the raw `func_addr` with GOT-slot-indexed dispatch (closure stores owning-module GOT base + slot index; drop-time call computes the address via GOT load), or (b) §5.3 option (b) — the closure captures clone the owning module's `Arc<Jit>` so retention follows the closure. Option (a) aligns with Decision 36's "Why all-GOT calling" discipline and Decision 31's callback-platform forward commitment (which establishes the same principle for `cranelisp_invoke_closure` host callbacks — GOT-indirect dispatch through the closure's `code_ptr` slot). **`/arch` recommendation**: option (a). This is the natural generalisation of Decision 36 to function-pointer-valued fields. A new Decision 38 will be recorded at Phase 3 close once the fix shape is validated by implementation — deferred to then per the standing Phase 3a rule that new decisions crystallise post-design, not pre-emptively.

**Interface impact of these answers**: none at the `cranelisp-types` boundary. The fix is entirely inside `crates/cranelisp-backend/src/compiler/` (closure codegen revision) + `src/worker.rs` (restore_cached_module + inline_jit_codegen_for_names). No new `Code` variant, no new `Module` trait method, no `SymbolTable` shape change. The closure layout in `heap.rs` may gain a field (owning-module GOT-base pointer + slot index pair in place of the single `drop_glue_ptr`) but that is backend-internal, not a boundary type.

#### Interface-gap check (Condition 1 §9.4)

No FIXME escalation to /arch needed for Wave 1. If Wave 1 implementation surfaces a need for an `Arc<GotTable>` helper method (e.g., `merge_from(&Arc<GotTable>)`) on the `GotTable` type itself (which lives in `cranelisp-types`), that is a types-crate interface extension and /arch reviews at that point. File FIXME(/arch) at the implementation site if so.

#### Phase 3b disposition — parallel launch assessment

**Safe to launch in parallel with Workstream A audit+fix:**
- `/int` Workstream E (cosmetics / carry-forward cleanup) — orthogonal to codegen/convergence.
- `/stdlib` + `/examples` Workstream F (prelude-expose vs examples-rewrite co-decision per Condition 4) — upstream of any JIT/object convergence surface; decision doc is /stdlib-owned.
- `/qa` test plan derivation for Workstream A — the design doc §8 is the input; /qa can author the 4 regression-guard test stubs (`#[ignore = "pending Workstream A fix"]` per the sprint's "failing-not-ignored except when infrastructure pending" conventions, or as `#[cfg(feature = "wave-1-pending")]` stubs) in parallel with the audit wave. The tests flip green as fixes land.

**Should block on Workstream A fix-scope decision:**
- `/backend` Workstream A implementation wave itself (Wave 1). The audit-first phasing in §9.3 is load-bearing: Workstream B CLIF-dump must land before the H3 audit runs, and the audit determines whether §4.3 + §6.1 fold into Wave 1 or carry forward. /sprint coordinates the wave sequencing.

**Conclusion**: Wave 1 for Workstream A proceeds under the audit-first phasing (Workstream B CLIF-dump → H3 audit → §6.1 fix → H3 fix → §4.3 fix if audit confirms). Other workstreams launch in parallel. No sprint-level rescope required.

#### Revisions (if any)

None required from /backend. The two FIXME(/arch) comments in `design/backend/jit-object-convergence.md §9.4` are resolved inline (edited by /arch per Condition 5 review-annotation allowance). Design doc approval stands.


## Skill Plans

*To be filled during Phase 3 by each skill. Compiler skills with implementation work (`/backend`, `/int`) MUST author or update a design doc in `design/{skill}/`. User-proxy skills (`/repl`, `/port`, `/stdlib`, `/examples`, `/docs`, `/platform`) MUST produce a demo update as part of Phase 5b showcase.*

### /sprint
**Task**: Coordinate sprint; track FIXMEs; run Phase 1→6 methodology.
**Approach**: This file; wave organisation after Phase 3; Phase 6 close protocol.
**Acceptance**: Sprint closes with all six archetype gates met (showcase, FIXME scan, coverage audit, tests, ROADMAP update, /review PASS).

### /arch
**Task**: Phase 2 architecture review; Phase 3 review of Workstream A design doc; invariant audit co-lead.
**Approach**: TBD Phase 2.
**Design refs**: `design/arch/CLAUDE.md` Decisions 23, 25, 31, 36; `design/arch/pipeline-v4.md` §6, §9.

### /backend
**Task**: Workstream A primary (JIT/object divergence root-cause + fix); Workstream B (CLIF-dump); Workstream C (build marker).
**Design doc**: `design/backend/jit-object-convergence.md` — **to be written in Phase 3** before implementation.
**Approach**: TBD Phase 3.
**Design refs**: `design/backend/defects-456-reduction.md`, `design/backend/ring2-rc.md`, `design/arch/CLAUDE.md` Decisions 23/25/31/36.

### /int
**Task**: Workstream E (3 S59 /review Importants); Workstream G (/sig docstring format); review-sentinel for Workstream A integration touches.
**Design doc**: Workstream E is small enough to not require a new design doc; update `design/int/dual-path-persistence-collapse.md` §7 with the 6th prologue site migration and the `delays_other` reconciliation.
**Approach**: TBD Phase 3.
**Design refs**: `design/int/dual-path-persistence-collapse.md`, `design/review/sprint-59-wave-1.md`, `repl/spec.md §1.1`.

### /frontend
**Task**: No implementation; review-only sentinel during Workstream A.
**Approach**: TBD Phase 3.
**Acceptance**: Sign-off or explicit "no concerns".

### /typecheck
**Task**: No implementation; review-only sentinel during Workstream A (CheckState/SymbolTable interactions).
**Approach**: TBD Phase 3.
**Acceptance**: Sign-off or explicit "no concerns".

### /platform
**Task**: No implementation; Phase 3 review of Workstream A for platform-registry impact.
**Approach**: TBD Phase 3.
**Acceptance**: Sign-off or explicit "no concerns"; platform demo current if A touches DLL loading.

### /qa
**Task**: Workstream H (coverage audit + `[Tested+Neg]` promotions); Phase 3 test-case derivation from Workstream A design doc; Phase 5b audit.
**Approach**: TBD Phase 3.
**Acceptance**: 3+ passing neg-coverage tests; `[Tested+Neg]` promotions on spec; all carries green.

### /review
**Task**: Code review of every wave producing code. 2x-deferral escalation policy active.
**Approach**: Run at the close of every implementation wave with standard B/I/S classification. Three S59 /review Importants in Workstream E are first-time-deferred; any further deferral requires user sign-off.
**Acceptance**: /review PASS at close; 0 Blockers; Importants resolved or explicitly deferred with rationale.

### /spec
**Task**: Responsive — action FIXME(/spec) comments from Workstreams F/G/H; assist /qa with `[Tested+Neg]` promotions.
**Approach**: TBD Phase 3.
**Acceptance**: Spec updated or explicit defer.

### /stdlib
**Task**: Workstream F co-lead (examples `--run` path — decide prelude expose vs examples rewrite); stdlib demo refresh.
**Approach**: TBD Phase 3.
**Acceptance**: `--run examples/*.cl` all green; stdlib demo plays cleanly.

### /examples
**Task**: Workstream F co-participant; Phase 5b sweep `cargo run -- --run examples/*.cl`.
**Approach**: TBD Phase 3.
**Acceptance**: All examples green; demo script updated.

### /docs
**Task**: Phase 5b — update user-facing docs if Workstreams A/F/G change observable behaviour.
**Approach**: TBD Phase 5b.
**Acceptance**: Docs current; docs demo plays cleanly.

### /port
**Task**: Workstream D (Defect 7 re-enable); exemplar demo refresh.
**Approach**: Blocked on Workstream A Defect 6 closure. TBD Phase 5b.
**Acceptance**: 3 puzzle tests green; exemplar demo plays cleanly.

### /repl
**Task**: Workstream G spec audit; Phase 5b — create `repl/demos/ring4r.demo` demonstrating JIT/object convergence (solver + run-tests + examples green) and /sig docstring fix.
**Approach**: TBD Phase 5b.
**Acceptance**: New demo plays cleanly; all prior demos verified; `repl/demos/CLAUDE.md` conventions followed.

## Waves

Phase 3 closed with all artefacts landed: `/backend` convergence design (APPROVED; Fix Scope ~3d/~370 LOC, in budget); `/arch` Phase 3a review + answers to Q1/Q2; `/int` E+G design updates; `/stdlib` Option A decision (expose 30 primitives through prelude, ~10 LOC); `/qa` §G.20 test plan with 5 `[Tested+Neg]` candidates ranked.

Wave organisation reflects three structural dependencies surfaced in Phase 3:
1. **Workstream B (CLIF-dump) is load-bearing for A's H3 audit** — land first so A can see into the divergence.
2. **Workstream A is internally sequenced** — `B → §6.1 fix → H3 audit → drop-glue GOT fix → §4.3 carry-forward fix` per `design/backend/jit-object-convergence.md §9`. The H3 fix may require closure-layout revision (per /arch Q2 answer: drop-glue `func_addr` is not currently GOT-indirected). This is the load-bearing change of the sprint.
3. **Workstream D blocks on A's Defect 6**, and Workstream F's test sweep is parallel-safe but validates independently.

### Pre-Wave 1: resolve /qa's two Phase 3 FIXMEs

| Skill | Task | Status | Notes |
|---|---|---|---|
| /backend | Clarify pre- vs post-relocation CLIF in convergence design §8 `same_source_produces_same_clif` | pending | FIXME(/backend) filed in `tests/plan/ring4.md §G.20.10`. Small (doc addendum). |
| /int | Confirm redundancy disposition on /sig tests (unit + integration smoke) | pending | FIXME(/int) filed in `tests/plan/ring4.md §G.20.10`. /qa recommendation: author the smoke anyway to guard REPL dispatch wiring. |

Both are doc-level clarifications; /sprint treats as in-line cleanup during Wave 1 kickoff, not a gating wave.

### Wave 1: Quick wins + observability + non-A workstreams (fully parallel)

All independent of Workstream A. /review assesses new code within the wave (not deferred). Gate: /review reports 0 Blockers; all listed tests green; FIXME scan clean.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /backend | **B** — CLIF-dump infrastructure (`CRANELISP_CODEGEN_DUMP=<module>` env var; wire to per-defn codegen) | pending | Lands FIRST (load-bearing for A's H3 audit). Integration test per /qa §G.20.B. |
| /backend | **C** — Object-file build marker for cache invalidation (`build.rs` + `.meta.json` field + cache-load check) | pending | Orthogonal to A. Commit message MUST cite /arch Condition 3 (complement, not substitute for CACHE_SCHEMA_VERSION). |
| /int | **E-1** — Migrate `register_transitive_cached_imports` cache-miss branch to `register_dep` shim (`src/worker.rs:1637-1684`, ~38 LOC deletion + shim call) | pending | Per `design/int/dual-path-persistence-collapse.md §8.1`. |
| /int | **E-2** — Flip `register_dep_for_eval` `delays_other=false` → `true` (`src/session_v4.rs:1311`) | pending | Per §8.2. No-op on hot path today; risk ≈ 0. |
| /int | **E-3** — Re-site deleted unit guard as `register_dep_shim_publishes_before_caller_registers` + optional `debug_assert!` | pending | Per §8.3. |
| /int | **G** — `/sig` docstring format fix (2-line edit at `src/session_v4.rs::format_entry_sig:361`, call existing `append_docstring_comment`) | pending | Per §9. 3 unit tests in `src/` per memory rule. |
| /stdlib | **F** — Expose 30 bare primitives through `stdlib/prelude.cl` (4 `(export [primitives […]])` forms, ~10 LOC) + update `stdlib/CLAUDE.md` line | pending | Per `design/stdlib/examples-run-path.md` decision §3 (Option A). |
| /qa | Integration tests for B, C, E-3, G smoke; subprocess sweep for F (`tests/examples_run.rs`) | pending | Per `tests/plan/ring4.md §G.20` — 4 new files, ~6 new functions. |
| /qa | **H (annotation-only, parallel)** — `[Tested+Neg]` promotions for §8.3.1, §8.3.7, §8.3.9, §12.5 TCO (candidates #1–4; all already tested, just unannotated) | pending | Per §G.20 Workstream H, top 4 are pure annotation work. |
| /examples | Validate `cargo run -- --run examples/*.cl` passes post-F | pending | Wave-1 gate for F. |
| /review | Per-skill code review as each task lands | pending | 0 Blockers required at wave close. |

**Wave 1 gate**: All 10 tasks complete. Test baseline: expected to flip ~4 tests green (F sweep + G smoke + E-3 guard + any C cache tests), plus 4 spec annotations updated. The 5 A-carries remain red — flips in Wave 2. /review report clean.

### Wave 2: Workstream A — JIT/object convergence (sequential, single skill)

`/backend` drives the primary workstream sequentially per `design/backend/jit-object-convergence.md §9`. Other skills (`/frontend`, `/typecheck`, `/platform`) act as review-only sentinels. /int acts as integration-layer sentinel if A surfaces `Code` enum or upsert-site touches — escalates to /sprint for re-scope if so.

| Step | Skill | Task | Gate |
|---|---|---|---|
| A.1 | /backend | **§6.1 fix** — close the 3 silent-skip holes in `inline_jit_codegen_for_names` (`else { continue }` at lines 2891/2896/2908). Error out on unresolved symbol, matching S58 Wave 2's cache-hit-path fix. | cargo check + targeted tests pass. H4 audit confirms no new NULL sinks. |
| A.2 | /backend | **H3 audit using CLIF dump** (Workstream B now usable) — dump drop-glue codegen for `cell-at$grid.Cell`, confirm `func_addr` baked address + Decision-31 reclaim race. Update `design/backend/defects-456-reduction.md` with audit findings. | Audit documented; hypothesis confirmed or refuted. If refuted, /sprint escalates to user re-scope. |
| A.3 | /backend | **Drop-glue GOT indirection** — closure-layout revision: `drop_glue_ptr` becomes GOT-slot index rather than raw address, dispatched via `__cranelisp_got_{M}` per Decision 36 generalisation. Per `design/backend/jit-object-convergence.md §5.3` option (a). This is the load-bearing change. | 5 A-carry tests flip green. /review assesses. |
| A.4 | /backend | **§4.3 carry-forward fix** (conditional on A.2 findings) — merge-rather-than-replace semantics in `restore_cached_module` to preserve `Arc<GotTable>` continuity across cache-hit replacement. ~40-80 LOC logic change per /arch Q1 answer. | Cache-hit tests stable. No regression in Wave 1 test set. |
| A.5 | /review | Full review pass on Wave 2 changes. | 0 Blockers; Importants resolved or explicitly first-deferred. |

**Wave 2 gate**: 5 A-carry tests flip green. Baseline drops to ~0 carried failures. `design/backend/defects-456-reduction.md` updated with audit findings as historical record.

**Wave 2 escalation**: If A.2 audit refutes H3, /sprint pauses and escalates to user with options (hypothesis re-ranking, scope descope, extend sprint by a session). If A.3 scope exceeds estimate by >50%, /sprint re-scopes before A.4 begins.

### Wave 3: Dependent fixes + stretch coverage

| Skill | Task | Status | Notes |
|---|---|---|---|
| /port | **D** — Re-enable 3 puzzle tests in `exemplar/solver.cl` | blocked-by A | Validates A's Defect 6 closure. |
| /qa | Stretch `[Tested+Neg]` promotion (candidate #5: §12.3.1 no-use-after-free or §4.4 if-branch unification — audit whichever is easier) | blocked-by Wave 1 | Target 5 total promotions this sprint. |
| /qa | Final failure-sweep — confirm baseline at 0 carried failures | blocked-by Wave 2 | Sprint 59 close was 5/5; S60 target is 0/5. |

**Wave 3 gate**: 0 carried failing tests. 5 `[Tested+Neg]` promotions landed. Unblocks showcase.

### Wave 4: Phase 5b showcase (user-proxy skills, parallel)

Mandatory per `/sprint` archetype. Every user-proxy skill exposes the sprint's work via demos and docs.

| Skill | Task | Status | Notes |
|---|---|---|---|
| /repl | New sprint demo `repl/demos/ring4r.demo` — convergence (solver + run-tests green) + /sig docstring + examples `--run` | blocked-by Wave 3 | Replay all prior demos for regression check. |
| /port | Exemplar demo refresh — show restored puzzle test surface | blocked-by Wave 3 | Demo plays cleanly. |
| /stdlib | Stdlib demo refresh — show primitives now usable from REPL without explicit `(import [primitives [*]])` | blocked-by Wave 1 | Validates F. |
| /examples | Examples demo refresh — show `cargo run -- --run examples/*.cl` sweep green | blocked-by Wave 1 | Documents Ring 4 AC closure. |
| /docs | Audit `user/` tutorials + guide for observable-behaviour changes; docs demo refresh | blocked-by Wave 3 | /sig docstring format change may touch docstring examples. |
| /platform | Platform demo currency check | blocked-by Wave 2 | No expected impact from A, but re-validate. |

**Wave 4 gate**: New sprint demo plays cleanly; all prior demos play cleanly; all user-proxy demos current.

### Wave 5: Close (Phase 6)

| Skill | Task | Status | Notes |
|---|---|---|---|
| /review | Final /review report — PASS required | blocked-by Wave 4 | Importants resolved or explicitly deferred with rationale. |
| /qa | Pass-2 close-time audit — every spec requirement in scope has a passing test | blocked-by Wave 4 | FIXME scan clean; coverage audit clean; 5 `[Tested+Neg]` promotions confirmed. |
| /sprint | Close checklist (every gate in §Sprint Archetype Phase 6); outcome section; archive; ROADMAP update | blocked-by /review + /qa close items | Status → COMPLETE; file moves to `sprints/archive/sprint-60.md`. |

**Close gate**: all Phase-6 checklist items pass. User approval required before archive + ROADMAP update per `memory/MEMORY.md` "Sprint close" rule.

### Wave ordering rationale

- **Wave 1 fully parallel** because every task is either independent of A (B, C, E, G, F, H-annotations) OR observability infrastructure A depends on (B).
- **Wave 2 sequential within /backend** because `§6.1 → H3 audit → drop-glue GOT → §4.3 carry-forward` is a causal chain: each step informs or depends on the previous.
- **Wave 3 after Wave 2** because D unblocks on A's Defect 6; the stretch coverage promotion is parallel-safe but /sprint batches it here for coherent reporting.
- **Wave 4 after Wave 3** because showcase demonstrates the sprint's delivered capabilities; cannot ship before the cluster is green.
- **Wave 5 single-skill synthesis** — /sprint + /review + /qa only.

## Notes

**Deferral escalation status**: 3 S59 /review Importants are at their first-deferral threshold, now in scope as Workstream E. Further deferral requires user sign-off.

**Sprint 61 precondition**: Target state at close is "0 carried failing tests". If Workstream A does not fully clear the cluster, Sprint 61's FQTypeName migration is deferred until the baseline is clean — the migration touches every boundary type and cannot land on a flaky test suite.

**Scope note**: Workstream B (CLIF-dump) is sequenced to land EARLY in Wave 1 so that Workstream A can use it during root-causing. If Workstream A root-causes without needing dumped CLIF, B remains in scope as observability debt worth clearing.

**Wave 1 finding — prelude discovery gap for `examples/`** (2026-04-21). Workstream F re-exported the 30 primitives correctly, but `cargo run -- --run examples/FOO.cl` without `CRANELISP_LIB=` still fails with "undefined variable: add-i64" because `project_root = examples/` (not the repo root), so `resolve_prelude` + `assemble_lib_dirs` never finds the bundled `stdlib/`. The prelude re-exports are unreachable from the bare `--run` command. This is the REAL Ring 4 AC gap; F solved half of it.

FIXME filed in `design/stdlib/examples-run-path.md §4.4 step 4` with three resolution options:
- (a) Add `examples/Cranelisp.toml` with `lib-dirs = ["../stdlib"]` (project-config approach)
- (b) `--run` falls back to bundled `stdlib/` if no project config found (user-friendly default)
- (c) Update acceptance command to require `CRANELISP_LIB=` (documents around, not a fix)

**Disposition (user decision 2026-04-21)**: NONE of the filed options — decision is to honour the root `CLAUDE.md` "Stdlib separation" principle. Examples are free-standing and MUST NOT depend on `stdlib/` (the in-development stdlib may move/change). /examples owns a minimal `examples/lib/prelude.cl` with just what the examples need (the 30 primitives + whatever traits/macros are used), plus an `examples/Cranelisp.toml` that adds `./lib` to the search path. `/stdlib`'s re-exports stay — they remain correct for REPL/exemplar/production users. Workstream F rescope:

- `/stdlib` — DONE. 30 primitive re-exports in `stdlib/prelude.cl` retained (useful for REPL/exemplar/production). No further work.
- `/examples` — NEW scope: (1) `examples/Cranelisp.toml` with `lib-dirs = ["./lib"]`, (2) `examples/lib/prelude.cl` minimal standalone prelude (content TBD by /examples — the 30 primitives and any traits/macros the examples use, no dependency on `stdlib/`), (3) verify `cargo run -- --run examples/*.cl` sweep green without `CRANELISP_LIB=`.

---

**Wave 1 finding — pre-existing warnings surfaced during Workstream B `cargo check`** (2026-04-21). Consistent with the clean-and-green sprint theme, these are folded into Wave 1 as a cleanup pass (new sub-workstream **W**):

| File | Skill | Issue |
|---|---|---|
| `crates/cranelisp-typecheck/src/program.rs:2821,2827` | /typecheck | unused import `FQSymbol`; dead `fn user_fqtn` |
| `crates/cranelisp-typecheck/src/traits.rs:1843,1845` | /typecheck | unused imports `CheckState`, `TypeCheckEnv`, `FQSymbol` |
| `crates/cranelisp-typecheck/src/checker.rs:1765,1770` | /typecheck | dead methods `get_impls_for_type`, `get_implementing_types` |
| `tests/scheduler.rs:30..315` (18 sites — was mis-cited as `src/scheduler.rs`) | /int | unused `mut` — DONE Wave 1 |
| `tests/cache.rs:1184` (was mis-cited as `cranelisp-backend/cache.rs`) | /qa | unused variable `mtime1` |
| `tests/v4_repl_eval.rs:137` | /qa | dead fn `assert_stdout_contains` |
| `tests/v4_pipeline.rs:93,233,457` | /qa | dead fns `run_old`, `assert_v4_runs`, `run_old_project` |
| `tests/repl_experience.rs:21` | /qa | unused import `format_result_value` |

Each owning skill cleans its own files during Wave 1. Treated as mechanical cleanup — no design review required for pure removal / `_`-prefix / `#[allow]` disposition. File a FIXME(/skill) only if the "dead" code is actually about to be used by Wave 2 (e.g., `user_fqtn` in /typecheck may be called from the upcoming FQTypeName migration — assess before deletion).

**Wave 4 finding — bare primitive at REPL prompt fails codegen** (2026-04-21, `/stdlib` demo refresh). With Sprint 60 Wave 1's `(export [primitives [...]])` re-exports in `stdlib/prelude.cl`, `/sig add-i64`, `/info add-i64`, and `(add-i64 2 3)` all resolve correctly. BUT typing bare `add-i64` at the prompt errors: `codegen error at 0..7: undefined variable: add-i64` — introspection (`/sig`) sees it, call form sees it, bare-value form does not. Trait-dispatched names like `+` and user-bound names resolve fine as bare values. Re-exported `primitives` names behave specially at the prompt's bare-name-value path. Not fixed in demo scope — demo uses `/sig add-i64` instead. FIXME(/int) filed via this note — investigate whether `(export [primitives [...]])` populates the value-expression path in `CompilerSession` the same way it populates the call/introspection paths.

## Outcome

*To be filled at sprint close.*
