# cranelisp-backend + the resolution seam — S110 Whole-Context Assessment

> **Cycle.** Second in-rotation `/audit` assessment of this context
> (`sprints/artefacts.md` §I.7/§II.1). Dated 2026-07-16, S110 Phase 6a,
> dispatched post-W3 per `sprints/SPRINT.md` §7 so the boundary lens assesses
> the **centrepiece end-state**: FIXME 0583 closed — the backend as a pure
> keyed-lookup consumer (`design/arch/backend-keyed-consumer.md`, LANDED;
> Principle 24; BC §3 invariant 10). Disposed at S111 Phase 1.
>
> **Predecessor.** `audits/cranelisp-backend-s107.md` (2026-07-11, 7
> recommendations + acid-test addendum). Its §4 disposition trail was **never
> written** — see §2.3, the single most consequential process finding here.
>
> **Method.** Read-only. Independent grep-gate verification (§2.1, exact
> patterns recorded); `resolution.rs`, `context.rs`, and every keyed-read seam
> read in source; scripted >100-line function census (two passes — the first
> undercounted multi-line signatures; §2.4 uses hand-verified spans for the
> named funnels); design/BC/rustdoc contract homes verified; S107's R1–R7
> re-verified item by item. **No test run** (tree shared with the active
> src-chain; suite state cited from the sprint record, not re-measured).

Crate size at HEAD: 38,500 lines of `.rs` under `src/` (production ≈ 22k;
`compiler/apply.rs` 2,277 the largest module; `compiler/resolution.rs` now
**79 lines**, down from the resolver seam — the W1–W3 waves deleted 993 LOC).

---

## 1. Verdict

| Attribute | Verdict | Grounds |
|---|---|---|
| Design quality (fitness) | **strong** | The resolution boundary is now exactly what the second-time solution would build: ONE keyed fetch (`entry_at`, `context.rs:170`) + kind-arm projections, hard `CodegenError` on carrier/entry miss with design-citing messages, two naming primitives as the only `resolution.rs` survivors. The S107 "strong" verdict is strictly stronger now — the one seam that verdict could not see (the backend running its own precedence rules; 0583) has been excised at the root, not patched. |
| Design realisation | **adequate** | The centrepiece contract is realised in all four permanent homes exactly as designed (BC §2 producer obligation `bounded-contexts.md:144-147`; BC §3 invariant 10 `:234`; `mono_expr.rs:148-150/:337-344` rustdoc; `interfaces.md`). But `design/backend/backend.md` (last real edit `b2038575`, 2026-07-03) still cites the S75-retired `facades/backend.md` as "authoritative" at lines 3/5/7/38/322/418/444, still overclaims the `FunctionArtifacts` deletion (live at `lib.rs:275`), and does not mention the crate's defining transformation at all — the S107 R6 currency pass never ran. |
| Simplicity & volume — code | **adequate** | The −993 LOC resolver excision is the single biggest simplification in the crate's history, and it deleted a whole *class* (ten divergent entry points over one driver). The residue stratum S107 catalogued persists nearly untouched: the Wave-2b cache shims, the duplicate `build_isa`, the production-compiled test front door, the unread `module_aliases` field (§2.4). |
| Simplicity & volume — docs | **weak** | Unchanged from S107's weak: `backend.md` misleads on authority/inventory/deletions; the eight executed one-shots + sketch-voiced docs still sit beside live docs in `design/backend/` despite `archive/` existing. Only the two `CLAUDE.md`s were reset (increment F + the W3 seam-map update — both current and accurate). |
| Simplicity & volume — tests | **adequate** | Positive coverage of the new seam is genuinely good: KC-W0-6 fixture carriers (`test_support.rs:48-74/:440`), the W0.b golden CLIF byte-identity gate (`tests/golden_clif_w0b.rs` — a named, scoped shippability gate), dispatch/value-use unit siblings. The negative side of the new invariant is **absent** (§2.6 risk 1). |
| Duplication | **adequate** (improved from weak) | The largest divergent family ever named in this crate is gone. Remaining: the `build_isa` pair (4th consecutive audit, §2.5) and the drop-glue skeleton ×3 (2 historical defects; unchanged since S107 R5). |
| Risk-weighted coverage | **adequate** | 4 of 6 top risks pinned on production paths (§2.6). Unpinned: the keyed-read **hard-miss negatives** (the design's own §9 acceptance obligation — no test anywhere asserts any of the three `CodegenError` message families) and GOT slot exhaustion (release-mode UB, S107 R7, lapsed un-disposed). |
| Maintainability | **adequate** | The keyed-seam error messages are exemplary (each names the reference, the missing carrier, and the design section). Comment honesty improved (`e7be859d` swept present-tense resolver mentions; survivors verified past-tense). Persisting: `exe.rs:72-77` "currently red post-W2/W3; re-wires S77" on a live function (16+ sprints stale), `jit.rs:26-33` old-protocol `FIXME(W4)` + retired-facade citation, cache "Wave 2b" markers with no referent. |
| Memory freshness | **adequate** | `crates/cranelisp-backend/CLAUDE.md` is current and spot-checked accurate (W3 seam map, schema 19, grep-gate wording, GOT gotcha). `design/backend/CLAUDE.md` was reset 2026-07-11. The weak spot is `backend.md` (graded under realisation/docs above, not double-counted here). |

**The acid-test answer.** Would the second-time backend look like this? **At the
resolution boundary — yes, exactly; this is the rare case where the as-built
now IS the second-time solution.** The keyed-consumer end-state (one carrier,
one fetch, kind arms, loud miss, two naming primitives) is what retained
insight would build from scratch, and the migration even left behind the
verification artifacts the rewrite would want (the golden byte-identity gate,
the per-site S1–S24 inventory). **At the whole-crate grain — no, and for a
process reason more than a code reason:** the stratum the S107 assessment
already catalogued (dup `build_isa`, Wave-2b shims, dead front door + eager
disasm, 325-line dispatch funnel, glue-skeleton mirrors, unpinned GOT UB)
persists essentially untouched, because the §I.7 acceptance gate that exists
precisely to convert assessment prose into filed-or-declined work **was never
run on that assessment** (§2.3). The second-time solution would not carry that
stratum; nothing in this sprint declined to carry it either — it simply
lapsed.

---

## 2. Current state

### 2.1 Grep-zero verification — VERDICT: CLEAN

What was searched (2026-07-16, working tree at `e7be859d`):

1. `grep -rn -E 'resolve_driven|resolve_chain|resolve_got_target|resolve_is_callable_target|resolve_vec_query_primitive|resolve_callee_summary|resolve_platform_effect_target|resolve_poll_effect_target|resolve_extern_target|resolve_func_arity|lookup_constructor|lenient_mono_from_expr|resolve_got_entry' crates/cranelisp-backend/src/` — every hit is a `//`/`///`/`//!` comment line (deletion-narrative, past tense — sampled `apply.rs:627/:805`, `literals.rs:303`, `match_codegen.rs:237-241`, `lib.rs:565/:755`, `context.rs:146-227`, `fn_as_value.rs:108-720`, `resolution.rs:9-15`; all use "deleted"/"replaced"/"former"). **Zero function definitions, zero call expressions.**
2. `grep -rn 'fn resolve' crates/cranelisp-backend/src/` — sole hits: `vec_codegen.rs:510/:573/:1099/:1129` (`resolve_elem_{inc,dec}_fn_ptr{,_into}`) — **type-directed drop-glue synthesis** switched on `signature_heap_category`, no name input, no table walk; not resolvers (the `resolve_` prefix is cosmetic — see R3 note).
3. `grep -rn 'symbol_tables.iter()' crates/cranelisp-backend/src/` — four live sites, **all enumerations, none resolution**: `trace_codegen.rs:308` (trace-descriptor discovery — completeness-by-construction over all entries, `tracing.md` §3.5); `utilization.rs:256` (spark-stats call graph, env-gated); `jit.rs:330` (GOT data-symbol registration at `Jit::new`, one symbol per module key — order-insensitive); `jit.rs:117` (`register_platform_effect_symbols` — JIT-builder jit-name registration walk). None takes a written name as input or applies precedence rules. *Observation, not a finding:* the `jit.rs:117` walk registers by bare name into the JIT's flat namespace and follows `Import` edges; two same-named platform effects in different modules would be last-write-wins by DashMap order. Platform names are globally unique today; noted for the record only.
4. `resolution.rs` (79 lines total) retains **exactly** the two sanctioned naming primitives: `got_data_symbol_name` (`resolution.rs:48`) and `inner_fn_discriminator_for` (`resolution.rs:64`) — both fixed string-composition schemes, both unit-pinned (`resolution/tests.rs` — the 0347/0350 identity pins survive the resolver-test deletion).

**The §3 grep gate holds under independent verification.** The structural
acceptance for the S110 centrepiece is met: the backend performs zero name
resolution and zero bare-type-name resolution.

### 2.2 Keyed-consumer coherence — strong, with two release-mode soft spots

Every keyed-read seam verified hard-fails loudly, per Rev-2/Principle 18:

- **Call seam** — `compile_direct_call` (`apply.rs:1171` carrier-miss, `:1178` entry-miss): distinct, precise messages citing `backend-keyed-consumer.md §1.2/§1.3`.
- **Pattern seam** — `compile_constructor_pattern` (`match_codegen.rs:251` carrier-miss "typecheck keying drift", `:258` entry-miss); the S19 fallback is deleted and the comment states why a `None` is now always drift.
- **Value seam** — fn-as-value GOT read (`fn_as_value.rs:608-618`), operator-as-value §1.4 static-home fetch (`literals.rs:305-316`), the 0585 slot-less-template backstop (`literals.rs:214-224` — "generic value reference '<name>' reached codegen without a mono instance", release builds included).
- **View totalization** — `compile_to_module_impl` hard-errors on a codegen-reached entry with no typecheck-populated view (`lib.rs:765-775`); the backend builds no views on the live path (only `#[cfg(test)]`-reached `jit.rs::compile_defn_with_targets` calls the shared `cranelisp_types::MonoExpr::lenient_from_expr` — ONE view-builder home, closing the S107 A.2 risk-6 *view-construction* half).

No keyed-read-else-resolve hybrid exists anywhere (there is no resolver left
to hybridize with — the strongest possible form of the Rev-2 guarantee).

Two residual soft spots, both release-mode-silent where the discipline says
loud:

- **(B1)** `constructor_metas` (`context.rs:299-334`): the canonical-then-bare probe pair feeding heap classification and drop-glue emission silently `filter_map`-drops a ctor whose both probes miss in **release** — `debug_assert!` only (`context.rs:326-331`; the in-source comment admits "the next keying drift would surface as a wrong heap classification / drop glue, not an error. Fail loud in CI (release skips)"). A release-mode keying drift here means a **leak, not an error**. This is also the one remaining name-*composed* probe (sanctioned — `TypeDefInfo.constructors` is names-only — but its miss posture contradicts the seam's own standard).
- **(B2)** `concrete_field_types` (`match_codegen.rs:596-613`): silent `return Vec::new()` on `ctor_meta_at`/`lookup_type_def` miss. Unreachable-by-construction today (the same key was hard-validated at `match_codegen.rs:251-262` moments earlier in the same arm), so severity is low — but the honest posture for an invariant is `unreachable!`, not an empty vector that would flow into wrong bind classifications if the invariant ever broke.
- **(B3, diagnostic nit)** the value-seam *entry*-miss (carrier `Some(fq)` fetching nothing on a non-callable path) falls through to the generic `"undefined variable: {name}"` (`literals.rs:228-231`) instead of the precise §1.3 entry-miss family the call seam has. Hard error either way; message imprecise.

### 2.3 The S107 disposition lapse — the process finding

`audits/cranelisp-backend-s107.md` §4 ("Disposition trail — appended at S108
Phase 1") contains **only the placeholder**; the file ends with the A.4
addendum. `sprints/artefacts.md:7` explicitly names "S108 Phase 1 disposes
`audits/cranelisp-backend-s107.md`" as an open obligation. No sprint record
disposes it: `sprints/archive/sprint-108.md` Phase 1 processed the /search
increment batch and dispatched the *typecheck* rotation; S109 Phase 1 disposed
`cranelisp-typecheck-s108.md` (its §4 trail is written, R-1/R-2 accepted → FIXMEs
0578/0579, R-3 declined with rationale); S110 Phase 1 disposed `src-s109.md`
(§4 trail written, all six accepted → FIXMEs 0606-0610). **The backend-s107
assessment is the only one the protocol skipped — on its inaugural
application.** Consequence, reconciled against source:

| S107 rec | Status at S110 close | Evidence |
|---|---|---|
| R1 — delete dup `build_isa` | **OPEN — 4th consecutive audit** (04-23 → S87 F1 → S107 → now) | `jit.rs:49` ("Single construction point for the entire backend") vs `cache/object.rs:144` ("Single ISA construction point"); bodies identical modulo `is_pic`; contradictory single-source rustdoc unchanged |
| R2 — Wave-2b shim/marker deletion pass | **OPEN — 4th audit for the cache half** | `#[allow(deprecated)]` ×8 (`cache/mod.rs:412/:429/:476/:538/:589`, `cache/object.rs:37/:188/:333`); `CacheMetadata` envelope re-wrap at `cache/mod.rs:502-506`; `got.rs` (104 ln) + `codegen_types.rs` (13 ln) shims; `exe.rs:72-77` "currently red post-W2/W3; re-wires S77" + `#[allow(dead_code)]` on the live `generate_startup_object` |
| R3-revised — delete `compile_defn` front door, delegate to production seam | **PARTIAL — the view half closed as a W3 side effect; the front door survives** | `jit.rs:587` `compile_defn` / `:610` `compile_defn_with_targets` / `:749` `build_compile_context` / `:35` `CompileArtifacts` all production-compiled (`pub(crate)`, not `#[cfg(test)]`); eager `set_disasm(true)` still unconditional (`jit.rs:687`). Mitigation: view construction is now single-homed in `cranelisp-types` (`jit.rs:637-655` documents no-live-caller), so only *context* assembly can drift, and the probe tier still passes `mode_summary: None` (ownership-summary-driven codegen invisible to it) |
| R4 — split the dispatch funnels | **OPEN — worst offender at its 4th audit** | `compile_resolved_call` `apply.rs:430` ≈ **325 lines** (153 → 271 → 323 → ~325); `compile_to_module_impl` `lib.rs:633` ≈ **395** (373 → 395, grew); `compile_apply` `apply.rs:155` ≈ 200; `apply.rs` grew 2,210 → 2,277 |
| R5 — one drop-glue emission discipline | **OPEN, unchanged** | `lambda.rs:187` (125 ln) / `fn_as_value.rs:1011` / `vec_codegen.rs:803` (167 ln) — three skeletons, two historical identity defects (0350; ledger item 25) |
| R6 — `design/backend/` currency pass | **MOSTLY OPEN** | `backend.md` untouched since 2026-07-03 (retired-facade cites ×7, `FunctionArtifacts` deletion overclaim vs `lib.rs:275`, no keyed-consumer mention); executed one-shots + sketch-voiced trio still un-archived. Done: both `CLAUDE.md`s reset (2026-07-11 increment F; W3 seam-map) |
| R7 — GOT exhaustion surfaced as error | **OPEN — the register's only UB-class risk, still unpinned, in the release-compiler phase** | `cranelisp-types/src/module.rs:609` `allocate_got_slot` unchecked monotone; `got.rs:136/:147` `debug_assert!` only; no 1023→1024 boundary test exists anywhere |

The S107 assessment itself documented this exact failure mode about S87
("everything left as prose in the assessment did not [land]") and named the
§I.7 acceptance protocol as the cure. The cure was then not applied to it.

### 2.4 Simplicity & volume

Function census ≥100 lines (hand-corrected for multi-line signatures): **~28
non-test functions**, statistically unchanged from S107's ~30 — the
keyed-consumer waves replaced resolver *calls* inside the funnels without
splitting the funnels. Top: `compile_to_module_impl` ~395 (`lib.rs:633`),
`compile_resolved_call` ~325 (`apply.rs:430`), `generate_startup_object_checked`
270 (`exe.rs:121`), `load_object` 235 (`cache/linker.rs:229`), `compile_trace`
209 (`trace_codegen.rs:691`), `compile_apply` ~200 (`apply.rs:155`).

New dead weight introduced by the migration itself, both documented in-source
as deferred: the `CompileContext.module_aliases` field is now **threaded but
UNREAD** (`context.rs:79-88` — the resolvers that consumed it are gone;
dropping it moves the `pub compile_to_module` signature and int's call sites,
deferred out of W3 correctly, but must not silently persist), and
`FunctionArtifacts` (`lib.rs:275`) still contradicts its design-doc deletion
claim.

### 2.5 Duplication

The headline: the crate's largest divergent family — ten same-purpose
resolver entry points over `resolve_driven`/`resolve_chain`, plus the twin
backend-vs-typecheck precedence rules they embodied — is **deleted**, and the
S110 waves also deleted the `_or_prelude`-class risk of it regrowing (there is
no driver left to hang a variant on). What remains is exactly the two families
S107 named, unactioned: the `build_isa` pair (§2.3 R1 — now the
longest-standing named finding in the crate, four audits) and the drop-glue
identity+idempotency skeleton ×3 (§2.3 R5 — past the recurring-defect
consolidation threshold since S102). The `resolve_elem_*` family in
`vec_codegen.rs` is four near-siblings (`_into` variants ×2 kinds) that a
consolidation pass could halve, but no defect history — below threshold.

### 2.6 Risk-weighted coverage register

| # | Risk | Verdict | Evidence |
|---|---|---|---|
| 1 | **Keyed-read hard-miss discipline regresses** (a soft fallback / silent `None`-handling reintroduced at any of the ~12 seams) — the new dominant invariant | **Positive path pinned; negative path NOT PINNED** | Fixtures populate carriers (`test_support.rs:48-74/:311-336/:440`), `golden_clif_w0b.rs` pins W0.b byte-identity, dispatch/value-use siblings + e2e cover the flipped kinds GREEN. But `backend-keyed-consumer.md` §9 names the hard-miss negatives as pinned acceptance ("carrier-None on a table-reference kind; `Some(fq)` fetching nothing; slot-less template at a value read — each a distinct pinned `CodegenError` message family") and **no test in the backend unit tier or `tests/` asserts any of the three message families** (grep for the message texts: zero test hits). A regression to silent fallback would today be caught by nothing. |
| 2 | RC over/under-count (the crate's dominant historical defect class) | **Pinned, production path** (unchanged S107 A.2) | e2e leak fences (`tests/ownership_reuse.rs`, `tests/spec_12_runtime.rs`), moded-arg decision matrix (`compiler/apply/moded_arg_rc_tests.rs`) |
| 3 | GOT slot exhaustion → release OOB write (UB) | **NOT pinned — 2nd audit in a row, lapsed un-disposed** | `module.rs:609` unchecked; `got.rs:136/:147` debug-only; no boundary test; Phase H is the release phase and epoch fresh-slot churn accelerates approach |
| 4 | Cache schema drift | **Pinned, production path** | `cache/manifest/tests.rs`, `cache/serialize/tests.rs:93`, `tests/cache.rs`; `CACHE_SCHEMA_VERSION` 19 bumped correctly with the W0 carrier fields |
| 5 | Drop-glue identity collision | **Pinned with the S107 caveat intact** | identity tests still re-compose the name format inline rather than calling the production builder (R5's done-bar addressed this; lapsed) |
| 6 | Release-silent keying drift at the two §2.2 soft spots (wrong drop glue instead of error) | **NOT pinned** | `context.rs:326` debug_assert; `match_codegen.rs:604/:611` silent empties |

### 2.7 Boundary integrity

- **backend↔typecheck**: the carrier contract is honored in both directions. The backend reads `resolved_target`/`resolved_ctor` and the fetched entry ONLY; `ResolvedCall` is consumed solely as supplementary dispatch metadata (trait-method-as-value arity at `literals.rs:143-158` — the §1.1 pin). Local-variable priority precedes every keyed read (`literals.rs:122-126`, KC-N6). The producer obligation is scribed at BC §2 (`bounded-contexts.md:144-147`) and the consumer statement at BC §3 invariant 10 (`:234`) — both accurate against source.
- **backend↔primitives/intrinsics (D43)**: intact. `primitives_inline::try_emit_inline_primitive` remains a name-keyed opportunistic table before the uniform GOT fallback (crate `CLAUDE.md` contract; no `(trait, method, type)` keying found). Extern-by-name int-hosted intrinsics keep the sanctioned fixed-catalog `Linkage::Import` arm (`extern_call.rs:139` documents it against the deleted resolver).
- **cache/persistence**: the five `cache/mod.rs` invariants hold; schema 19 verified (`crates/cranelisp-backend/CLAUDE.md` claim ✓ against `cache/mod.rs`). The submodule's decay is the R2 shim stratum (§2.3), not its invariants.
- BC §3 invariant 10's closing sentence — "this invariant also discharges this crate's CLAUDE.md 'no trait knowledge, one dispatch path' aspiration, which the live resolver contradicted" — verified true in source.

### 2.8 Maintainability & memory freshness

The `e7be859d` comment sweep did its job: sampled resolver mentions are
uniformly past-tense deletion narrative (a *good* history layer, not decay).
The keyed-seam rustdoc (`context.rs:140-253`) is the best-documented seam in
the crate — each projection names the S-site it replaced and its miss
contract. Persisting dishonesty is confined to the §2.3 items: `exe.rs:72-77`
(16 sprints stale, on a live function), `jit.rs:26-33` (old-protocol inline
`FIXME(W4)` + citation of a facade file retired S75), the cache "Wave 2b"
markers whose stated external consumers a workspace grep already disproved at
S107. Crate `CLAUDE.md` spot-checks: all sampled claims accurate (schema 19 ✓,
grep-gate wording ✓, resolution.rs contents ✓, GOT-exhaustion gotcha ✓ — and
honestly flagged "unresolved", which is R7's point).

---

## 3. Recommendations

Eight; #1 is process, #2–#3 are new, #4–#8 are re-proposals of lapsed S107
items with refreshed evidence (they were never accepted OR declined — putting
them through the gate is the point). No live defects uncovered: every
verified miss-path is a hard compile-time error; the two release-silent soft
spots (#3) have no failing observable behaviour today.

### R1 — Dispose BOTH backend assessments at S111 Phase 1; append the missing S107 trail [small, /sprint]
**Evidence**: §2.3 — `audits/cranelisp-backend-s107.md` §4 empty; `artefacts.md:7` named the obligation; four of its seven recommendations hit their 4th audit as a direct result. **Done**: S111 Phase 1 processes this assessment AND retroactively appends the S107 §4 trail (each of R1–R7: accepted → FIXME, or declined + rationale — declining is legitimate; lapsing is not); `/sprint` adds the missed-disposition case to the Phase-7 close checklist item that verifies the audit cycle (the checklist verifies dispatch happened; it must also verify the *previous* assessment was disposed).

### R2 — Pin the three hard-miss `CodegenError` families (the §9 negatives) [small, /qa plan + /testing or /dev(backend) unit tier]
**Evidence**: §2.6 risk 1 — the design's own acceptance surface (`backend-keyed-consumer.md` §9) specifies carrier-miss / entry-miss / slot-less-template as "distinct pinned CodegenError message families"; zero tests assert them. The unit tier already has everything needed: the KC-W0-6 harness hand-builds tables and carriers, so an absent-carrier / dangling-FQ / `Polymorphic`-entry fixture is a few lines each. **Done**: one unit test per family per seam class (call seam `apply.rs:1171/:1178`; pattern seam `match_codegen.rs:251/:258`; value seam `fn_as_value.rs:608` + the 0585 backstop `literals.rs:214`), each asserting the message family — so a reintroduced silent fallback fails a named test, not nothing. This cures the risk (the discipline becomes regression-guarded), not the symptom.

### R3 — Close the two release-silent keying-drift spots [small, /dev(backend)]
**Evidence**: §2.2 B1/B2 — `constructor_metas` (`context.rs:322-331`) silent release drop feeding drop-glue/heap classification (a drift = leak, not error); `concrete_field_types` (`match_codegen.rs:604/:611`) silent empties on an already-validated key. **Done**: `constructor_metas` returns `Result` (or threads the existing error path) and hard-errors on a both-probes-miss in ALL build profiles; `concrete_field_types`' miss arms become `unreachable!("invariant: key validated by compile_constructor_pattern")` or a hard error; optionally the B3 value-seam entry-miss message adopts the §1.3 family. Cosmetic rider at `/dev`'s discretion: rename `resolve_elem_{inc,dec}_fn_ptr*` (`vec_codegen.rs:510/:573/:1099/:1129`) off the `resolve_` prefix now that the grep gate makes the name radioactive.

### R4 — The S107-R2+R3+R1 hygiene batch: shims, markers, dup `build_isa`, `compile_defn` disposition, `module_aliases` drop [medium, /dev(backend); one change-set]
**Evidence**: §2.3 rows R1/R2/R3 + §2.4. The batch is bigger than S107's because W3 added a member: the unread `module_aliases` field (`context.rs:79-88`) whose removal touches the `pub compile_to_module` signature + int call sites (coordinate the baseline regen per the discipline). `compile_defn` disposition per the S107 R3-revised bar: delete or `#[cfg(test)]`-demote `compile_defn`/`compile_defn_with_targets`/`build_compile_context`/`CompileArtifacts`, and drop the unconditional `set_disasm(true)` (`jit.rs:687`) — the remaining exposure is context-construction-only now (§2.3), so the cost is genuinely small post-W3. **Done**: one `build_isa`; zero `#[allow(deprecated)]`/"Wave 2b"/`CacheMetadata` under `cache/`; `got.rs`/`codegen_types.rs` shims gone (slab tests rehomed); `exe.rs` stale allow+comment gone; no production-compiled test front door; `module_aliases` off `CompileContext`; `public-api.txt`s regenerated in the same change-set; `cargo check -p cranelisp-backend` warning-clean.

### R5 — Split the two over-budget funnels that history keeps indicting [medium, /dev(backend), split plan via /design if contested]
**Evidence**: §2.4 — `compile_resolved_call` ~325 (`apply.rs:430`; 4th audit: 153→271→323→~325) and `compile_to_module_impl` ~395 (`lib.rs:633`; grew again). Post-W1 the resolver noise is out of these bodies, so the protocol-boundary split (per-kind arms as named `FnCompiler` methods; per-phase helpers for `compile_to_module_impl`) is cheaper than at any prior audit. **Done**: both under ~150 lines with extracted named arms; CLIF golden corpus byte-identical; `apply.rs` trending down at the next audit.

### R6 — One drop-glue emission discipline (S107 R5, unchanged + its A.4 strengthening) [medium, /design(backend) then /dev]
**Evidence**: §2.5 — three skeletons (`lambda.rs:187`, `fn_as_value.rs:1011`, `vec_codegen.rs:803`), two historical identity defects, discipline re-stated per site. **Done**: one glue-emission helper owns naming identity + idempotency; the consolidated identity test calls the **production naming function** (not an inline format re-composition — the A.4 caveat); the three builders supply only capture/layout specifics.

### R7 — Surface GOT slot exhaustion as a diagnosed error (S107 R7, unchanged; 3rd consecutive naming of the F-family) [small, /arch — the seam is `cranelisp-types`]
**Evidence**: §2.6 risk 3. The only UB-class risk in the register, unpinned, in the release-compiler phase, with the in-source note (`crates/cranelisp-backend/src/got.rs:26-33`) explicitly waiting for exactly this ruling. **Done**: fallible `allocate_got_slot` (or hard-checked `store_slot`) with a session-surfaced error; a 1023→1024 boundary unit test; the residual-risk notes updated to point at the cure.

### R8 — `design/backend/backend.md` truth pass, now including the keyed-consumer end-state [medium, /design(backend); design feedback]
**Evidence**: §2.3 row R6 + §1 realisation. The S107 R6 inventory stands (repoint the ×7 retired-facade citations to BC §3 + source rustdoc; fix the module inventory; reconcile `FunctionArtifacts`; archive the executed one-shots and sketch-voiced trio) **plus one new obligation**: when the next `/arch` archive triage moves `backend-keyed-consumer.md` to `design/arch/archive/` (its trigger is met, parked on the bootstrap R-2 tail), the per-crate master doc must carry the consumer-side narrative — today `backend.md` does not contain the words "keyed" or "resolved_target" at all, so archiving the arch doc would leave the crate's defining design invisible in `design/backend/`. **Done**: every live `design/backend/` doc has resolvable authority pointers and no source-falsified claims; `backend.md` (or a successor lean doc) states the keyed-consumer model with pointers to BC §3 inv 10 + `context.rs` rustdoc; historical docs in `archive/`.

---

## 4. Disposition trail

*(Appended at S111 Phase 1 by `/sprint` + the user — accepted → FIXME number,
or declined + rationale. Not written by `/audit`. Per R1, the S107
assessment's missing trail is appended in the same pass.)*
