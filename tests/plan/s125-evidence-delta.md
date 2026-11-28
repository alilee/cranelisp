# S125 evidence delta

> **Owner:** `qa`. **Readers:** `test`, dispatched against §6 and, in Phase 6b,
> §27.8; `dev`, for
> the module evidence of §5; `sprint`, sequencing it; `review`, checking
> delivered evidence against it.
> **Authority:** the [S125 sprint plan](../../sprints/archive/sprint-125.md) scope,
> architecture review and Phase 2 decisions; the user's rulings of
> 2026-11-26 on FIXME 0694, ACT-1036 and ACT-1081; row IO-T of
> [interfaces](../../design/arch/interfaces.md#opaque-io-row-io-t); the
> designs [binary clean](../../design/int/s125-binary-clean.md),
> [IO typing](../../design/typecheck/io-types.md) with
> [typecheck §12](../../design/typecheck/typecheck.md#12-designed-changes-not-yet-in-source),
> and the backend's `pure` lowering and schema walk, now in
> [IO trampoline §2.1](../../design/backend/io-trampoline.md#21-pure-codegen)
> and [§1.5](../../design/backend/io-trampoline.md#15-io-in-the-platform-schema)
> with the [release contract §5.1](../../design/backend/non-concrete-release-contract.md#51-the-pure-node)
> (the S125 backend opaque-IO record, cited below by section, is in Git history);
> `spec/10-io.md` §10.1, §10.2 and §10.10.1; `spec/07-traits.md` §7.2.3;
> `spec/08-modules.md` §8.2.5 and §8.10; `spec/12-runtime.md` §12.9.1;
> `repl/spec/04-self-documentation.md` §4.1.3;
> `repl/spec/05-error-presentation.md` §5.5;
> `repl/spec/15-session-persistence.md` §15.4.
> **Checkpoint:** `main` at `4c844f62`, with the uncommitted Phase 2 and
> Phase 3 edits of other roles in the tree (none under `src/`, `crates/` or
> `stdlib/`).

Every observation below was made by `qa` with `target/debug/cranelisp` built
from the checkpoint, in scratch directories outside the repository.

| § | Content |
|---|---|
| 1 | The opening suite reading |
| 2 | The hygiene band's `qa` filings, disposed |
| 3 | The trace deferral: cells and bands |
| 4 | Readiness: ambiguities, testability, verdict |
| 5 | The evidence plan for the S125 designs, by risk |
| 6 | The settled delta for `test`, with completion criteria |
| 7 | Census: `match` forms with no constructor arm |
| 8 | Handoffs |
| 9 | W1 acceptance |
| 10 | W2 adequacy |
| 11 | W3 adequacy |
| 12 | W4 decisions |
| 13 | W4: tests part, remaining consumers |
| 14 | W4 close |
| 15 | W5 adequacy |
| 16 | W6 adequacy |
| 17 | W7 adequacy |
| 18 | W7 correction delta |
| 19 | W7 correction adequacy |
| 20 | W7 close |
| 21 | W8 adequacy |
| 22 | W8 close |
| 23 | W9 adequacy |
| 24 | WG: the integrated gate |
| 25 | WG: the final pass |
| 26 | Phase 5 checkpoint: the baseline guard, S125-Q10, the accepted residuals |
| 27 | Phase 6b: bands, audit intake, exemplar, training, demo, stdlib; the handoff for `test`; acceptance of its first items |
| 28 | F2 and F3 repair readiness: the macro guard, poll-leaf reuse, the designs' evidence; acceptance of T-POLL-REUSE |
| 29 | F2 and F3 repairs: adequacy; stack exhaustion intake; the list for `test` |
| 30 | T-STACK accepted; the replay intake; what precedes the full run |
| 31 | The Phase 6b full run: reconciliation and the settling target |

## 1. The opening suite reading

`cargo nextest run --no-fail-fast`, once: **8,109 run, 7,966 passed,
143 failed, 1 skipped, in 250 s.**

- **Every failing test traces to a defect of the
  [S124 register](s124-evidence-delta.md#1415-defects-carried-by-failing-tests)
  or to the document gate.** No genuine regression. The per-defect counts
  equal the S124 close's; the run-dependent ACT-1090 cell failed again.
- **No workspace crate raises a build warning.** The only warning is the
  future-incompatibility note for the external `nix` 0.28.

| Module | Failing | Defects (cells) |
|---|---|---|
| `src/` | 71 | ACT-1089 (14), 1096 (9), 1079 (8), 1005 (6), 1100 (6), 1108 (6), 1106 (5), 1068 (4), 1101 (3), 1092 (2), 1109 (2), 1062, 1087, 1090, 1099, 1102, 1105 (1 each) |
| typecheck | 61 | ACT-1076 (15), 1075 (9), 1071 (7), 1074 (6), 1103 (6), 1080 (4), 1082 (4), 1097 (3), 1104 (3), 1073 (2), 1107 (2) |
| intrinsics | 3 | ACT-0977 |
| Not attributed to a module | 7 | ACT-1018 (5), ACT-1067 (2) |
| Maintenance | 1 | The document gate |
| **Total** | **143** | |

- **Matching.** Each failing test is traced by the identifier in its name or
  its `// defect:` line. The three `spec_10_io::s124_1065_prelude_bind_*`
  cells carry a closed identifier in their names; they are ACT-1075's face
  (T-1065-f of the S124 delta) and count there.
- **The document gate: 518 findings.** 515 are ignored-path findings, with
  the user. Three are in `sprint`'s working packet
  `sprints/s125-architecture-review.md`. None is in a file `qa` owns.
- **ACT-1060's check.** After this run no `ctx.txt` exists anywhere in the
  checkout, ignored files included: the fix at `8667a868` holds.
- **Limits.** One run. Attribution is the S124 register's, re-opened only for
  ACT-1079 (§4.1).

## 2. Hygiene band: `qa` filings

Each row records what was opened first, then the disposition. Deleted
filings are recoverable as `git show 4c844f62:<path>`.

### 2.1 Actions

| Filing | Opened and observed | Disposition |
|---|---|---|
| ACT-0962 coverage assurance | `tests/plan/spec_coverage_reconcile.py`: `--gaps` is parsed and never read, as filed | **Kept.** The user carries it without a date. FIXMEs 0761, 0785, 0811 and 0857, whose tails it held, are disposed of in §2.2 without it |
| ACT-0978 platform test trace claims | `tests/platform_errors.rs` lines 1–2, 24, 63–64, 146 defer to removed FIXME 0289; the deferred `shapes` DLL exists and `tests/spec_platforms_adt.rs` drives it. `tests/concurrency_poll_edge_guards.rs` cites platform-interface §6.8.0 for a `(token, capacity)` node convention that section no longer states; its assertions (no poll-capacity default-edge constructor; ABI 11 at `crates/cranelisp-platform/src/lib.rs:306`) hold. `tests/exemplar_web.rs` lines 6–8 attribute a one-request-then-exit guard to §3a, which states none | **Closed, deleted.** Three stale prose traces, repaired by `test` (T-0978) |
| ACT-0979 platform function types | Spec §10.10.1 rules containment through type arguments and ADT fields (user, 2026-11-15). `src/platform.rs::register_platform_in_tc` checks the IO return (`require_io_return`) and nothing else | **Converted to a failing test** (T-0979), `src/`-attributed, in the focus band (W9). Delete when the cells land |
| ACT-0982 agent module routing | `agent` is a default feature (`Cargo.toml` line 125). The default run executed all 143 `cranelisp agent::` module tests | **Closed, deleted.** The misleading test name at `src/agent/mod.rs:717` is `dev`(`src/`)'s |
| ACT-0985 forward references and HKT dispatch | §5.13.1's guard and T-Q7-d pass. `traits/impl_check.rs:297` rejects by the written spelling. Probe: a user unary type `Float` with a `Fun` implementation is refused, bare and qualified (`Float is not a type constructor`); the same file with `Flt` exits 42. Its four questions are answered: S125-Q2 and Q3 ruled, items 2 and 4 by existing text (appendix D) | **Back to `qa`, deferred to S126** (typecheck): the Q2 and Q3 requirements, the repair of `macro_expanded_begin_impl_neg_before_deftype_is_rejected`, and a reproduction for the rigidity lead. The spelling lead is a defect (T-0985) |
| ACT-0987 primitive identity, impl-method rigidity | The bare-name table is `traits/dispatch.rs::primitive_for_trait_method`, carried by ACT-1103's six cells. The rigidity question is unruled | **Closed, deleted.** Its question moved into ACT-0985 |
| ACT-0994 cached-load claim | `src/scheduler.rs:562` `complete_loaded` notifies by module name, unbound to the registration. [Int §7.1](../../design/int/int.md#71-cache-hit-flow-inside-register_module), *A claim ends inside its registration*, designs two rules and the RED-first scheduler rows | **In the focus band** (sprint, 2026-11-26). Evidence: E-0994 |
| ACT-1001 dotted members and dispatch index | P-1 and P-3 accepted. P-2: `traits/dispatch.rs:116,378` still scan by bare name; [typecheck traits §11](../../design/typecheck/traits.md#11-open-items) records the ruling | **Closed, deleted.** Spec §7.4.2a's band names the untested cases |
| ACT-1003 contested-type listing | No cache. `Qtok`, then `Qwrap (Qtok …)`, then bare `Qtok`: no `; match:` section. Reversed order: the `deftype Qtok` echo itself omits it. Control `Qwrap2 (Qother …)` lists `Qa Qb`. The cache is not the cause | **In the focus band** (sprint). Evidence: T-1003 |
| ACT-1004 missing-entry diagnostic | `tests/cli_missing_entry.rs` (`b89cc7cc`): the `--run`, `--link` and `--test` cells and controls pass | **Closed.** Deleted once `design/int/int.md` drops its link |
| ACT-1015 declared child and in-flight prelude | The reduction as filed, with a public child: 30 of 30 cold `--run`, a warm run and the REPL give 42. Control: with `helper` removed from the prelude, `undefined variable: helper` | **Closed: does not reproduce.** Deleted once `design/int/int.md` drops its link. *Reopened if* a fresh load of that shape refuses a name a reload accepts |
| ACT-1022 match-arm push leak | The original program was never committed. A reconstruction, P1 against the same program without the `match`, both `keep` values, under `CRANELISP_RC_STATS`: balanced in all four, `--run` and the REPL | **Closed: stale.** Residual: the S122 program is not reproduced exactly. Deleted once `audits/cranelisp-backend-s122.md` drops its link |
| ACT-1036 located refusals (carried defect) | Probe: `m.cl` holds a macro whose expansion, at line 3, defines a function referencing `discover-tests`; `p.cl` imports it. Cold `--run`: `m.cl:3:1 … at 87..91`. After a REPL session caches `m`: `m.cl:4:1 … at 1000060..1000060`, a line past the file's end and a synthetic offset | **User, 2026-11-26: reproduce and carry as a defect.** T-1036, RED. Attribution in §6. Deleted when the cell lands |
| ACT-1081 a cycle through a declared child | **User, 2026-11-26:** a `mod` declaration alone is not a dependency edge; importing from the child is. Every REPRO-1081 route accepts (exit 11). Probe of the twin where `P` imports from `P.c`: refused as a cycle by `--run` from each of the three entries and in both REPL orders | **Outcome ruled.** T-1081 adds the outcome clause, the importing twin and the save and restart legs. Deleted when they pass. `spec` scribes the ruling |
| ACT-1085 cache-owner lock | No lock in `src/cache.rs`, `src/cache/` or `src/session_v4/`. [Int §7.7](../../design/int/int.md#77-one-generation-beside-an-entry-act-1083) designs it | **In the focus band** (sprint). Evidence: E-1085, T-OWNER |

### 2.2 Legacy FIXMEs

| Filing | Opened and observed | Disposition |
|---|---|---|
| 0694 run-dependent members | None of its members failed in §1's run. Class II stopped reproducing at S124; every other member is one occurrence with no captured condition | **Closed as residuals, deleted** (user, 2026-11-26). Each member reopens on a recurrence of its recorded signature. Class I is a named residual in [memory-safety coverage §5](memory-safety-coverage.md#5-current-exposure--measured-s123-w5) |
| 0761 exact-balance lane, linked faces | `tests/rc_escape_release_0763.rs:232`: F (closure capturing a closure) is `RUN_ONLY`. `tests/capture_drop_glue_strands_nested_heap_0760.rs` has no linked face | **Allocated** (T-0761). Deleted when the two cells pass |
| 0785 trait-return annotation guard | No process test of `(deftrait Bad (show [x] :String))`. Probe: refused `parse error at 24..25: annotation missing expression`, at the colon; `Bad` is then undefined | **Allocated** (T-0785). Deleted when the cell passes |
| 0811 re-measure an aggregate attribution | The rule is in the QA contract, *Handle defects and gates* item 7. No `exemplar/` record claims the 0720 attribution | **Closed, deleted** |
| 0857 regrade R8's modes | R8 no longer cites `ms_p6_mode_self_tests.rs`. The eight plant triplets are in `crates/cranelisp-intrinsics/src/diagnostics/tests.rs`, drive `alloc::alloc_with_rc` and pass in §1's run, as do `intrinsics_m3_detection_s116`'s two cells | **Regraded** (§2.3), **deleted** (W0): `arch`'s R8 row no longer cites it |
| 0863 macro checkpoints (re-targeted to `qa` by `design`(int)) | Item 2 is resolved by `design`(int). Item 1 lists six checkpoint properties to witness | **Kept, `qa`'s.** The six properties are assessed against the existing `spec_09_macros`, `spec_11_stdlib` and `s76_macro_availability` cells before the Phase 5 exit; a gap becomes a `test` row then. No S125 design changes checkpoints |
| 0889 macro-turn marshal residue (re-targeted to `qa`) | The "resolved in S122" claims hold; the residue was not re-measured | **Kept.** Its trigger, a settling target claiming zero session residue, does not fire in S125 |
| 0907 IO release | Evidence met at S122; no `// defect:` line names it; `ring4s.demo` evaluates to 50; `/info Bind` and `/info IO` introspect | **Closed, deleted.** The stdlib self-tests are `dev`(`stdlib/`)'s plan item |
| 0929 R18 census remainder | No production `unwrap_or(Type::Int)` in `src/` or the backend. One fabrication remains: `crates/cranelisp-types/src/mono_expr.rs:849`, `lenient_from_expr` (`pub(crate)`, ruled for deletion). No census test exists | **Kept, re-targeted to `qa`.** Allocated (T-NC2) |

### 2.3 R8's diagnostic modes, regraded

- **M1, M2, M3 and A1–A4 are detection-proven instruments.** Each has a
  child-process triplet (positive, clean control, negative control) on the
  production allocation funnel, run on every suite run.
- **Limits that bind the grade:** M3's over-free row proves report polarity,
  not a real double free; A2–A4 prove header plausibility, not that a pointer
  is a base.
- **Build variant.** The triplets run under the debug test profile. No suite
  run executes a release build, so the release faces are unmeasured.
- **This regrades the instruments, not R8.** R8's property on programs is
  measured only where a lane arms a mode.

## 3. The trace deferral

TR-1, ACT-1110, ACT-1111, defects 1087 and 1090, and ACT-1093 wait for the
sprint whose focus is the built-ins and primitives. The settling target names
1087's and 1090's cells as its exceptions.

- **No cell moves.** ACT-1109's two cells observe the REPL and count for
  `src/`.
- **No committed cell pins today's trace text for an `IO` value.** Searched:
  every assertion in `tests/trace.rs`, `tests/spec_12_runtime.rs`,
  `tests/link.rs` and `tests/repl_*.rs`. `tests/fixtures/io_trace_snapshot.txt`
  records IO trampoline events and names no constructor. The backend's step 3
  change of trace text breaks no cell.
- **No trace-marker cell is allocated** (withdrawn with the deferral). The
  divergence from §12.9.1 in trace output is recorded on that heading's band.

## 4. Readiness

### 4.1 Ambiguities

**Resolved** (user, 2026-11-26, unless stated):

- S124-Q19 (pure terminology); the trace deferral; IO-T re-decided (`IO`
  has no constructors; `primitives/pure` is a host-promised built-in).
- S125-Q1 (ACT-1081): a `mod` declaration alone is no dependency edge;
  importing from the child is.
- S125-Q4: a macro-introduced reference is checked against the caller's
  visibility.
- S125-Q5 with R1 and R2: a live macro-generated definition is not
  redefined by a later form; an identical re-entry (same macro, same
  arguments) replaces; a reload that drops the call accepts a hand-written
  definition.
- S125-Q2, Q3 and Q6: requirements now, implementation later (§4.2).
- ACT-1036: reproduce and carry. FIXME 0694: residuals.
- By existing text (appendix D, S125 leads): the top-level
  `(primitives/pure (primitives/pure 1))` displays `Executing IO…` then
  `:(primitives/IO primitives/Int) #io`; an index dependency's dropped
  `defmacro` names do not license omitting its ordinary definitions.
- Defect 1079 joins the focus band (`sprint`, 2026-11-26).

**Open, with what is held** (none blocks W1):

| Question | Owner | Held |
|---|---|---|
| Appendix D reads `(primitives/pure)` as `pure`'s zero-argument partial application, contrary to the backend design's premise | `design`(backend, typecheck); `sprint` | No cell in W1, by `sprint`'s direction. If confirmed it is an IO-2 leg |
| The same macro call re-entered after its macro was redefined, generating fewer names: are the names only the earlier expansion produced retired? | `spec` (binary clean §4.4 residual) | No cell |
| §10.1's prose still calls the `IO` constructor "conceptually module-private"; under IO-T there is none | `spec` | Nothing; prose only |

### 4.2 Ruled but scheduled later (no S125 cells)

Their annotation bands carry `[S126 — …]`:

- **S125-Q2** (spec §5.4.5): two `impl` forms for one pair in one cluster
  refuse the cluster.
- **S125-Q3** (spec §7.2.2, §3.7.6): a higher-kinded method whose
  constructor variable occurs only in its result is refused.
- **S125-Q6** (spec §6.1, §6.2.4, §6.5.2, §10.1): a `match` with no
  constructor-pattern arm is refused. About 92 test programs migrate (§7).
- **ACT-0985's answered items** (spec §5.13.1, §3.3.2): the expanded-`begin`
  refusal cell asserts the superseded expectation; the rigidity lead needs a
  reproduction.

### 4.3 Testability

Every changed surface is observable at a public seam, except where named:

- **e2e:** opaque `IO`, `/type`, display, persistence including the
  §9.6.1 refusal, module loading and search, the cycle ruling, the located
  refusal, platform function types, the cache-owner lock.
- **Module tier only** (`dev`, each with a detection proof): the
  constructorless bootstrap, the cache schema bump, the claim–registration
  binding (ACT-0994), the `/type` staging check, the origin carrier and call
  identity of §9.6.1, the 1079 driver and walk.
- **Named residuals, no cell:** two cache generations mixed by two processes
  (ACT-1085); a restored definition absent from source under a matching hash
  (binary clean §4.3).

### 4.4 Verdict

**Go for `test`'s W1 dispatch against §6.**

## 5. The evidence plan

Conditions ranked by the harm of the wrong implementation. **Class:**
**A** acceptance, **F** safety fence, **O** diagnostic observer,
**M** maintenance check. **Layer:** e2e (`test`), unit (`dev`).

### 5.1 Opaque `IO` (1105, 1106, 1107, 1108)

| Id | Condition | Wrong implementation rejected | Layer and seam | Class |
|---|---|---|---|---|
| IO-1 | Every user spelling of an `IO` constructor is refused, in an expression and in a pattern: bare, imported, `primitives/Pure`, `primitives/IO.Pure`, dotted `IO.Pure`, and a scrutinee-picked `(Pure x)` arm; the same for `Effect` and `Bind`. Control: a user `deftype`'s constructors resolve in every spelling | A gate that misses one spelling (1105's face); a residual `IO.*` key; a refusal that stops user constructors | e2e, `--run` and REPL, one linked leg. The 1105–1108 cells already use qualified spellings and assert refusal; they flip at step 3. New: dotted, imported and pattern spellings | A |
| IO-2 | `primitives/pure` applied and as a value: passed to a stdlib-free higher-order function, bound in a `let`, captured, stored in a vector; scalar and heap payloads; REPL, `--run`, linked. A heap-payload node forced twice and dropped balances | A wrong glue word: a leak (heap payload stamped 0) or a wild write (scalar payload stamped with glue) | e2e with `MarginalPair` under `CRANELISP_RC_STATS`, `CRANELISP_RC_DEC_CHECK` armed | A, F |
| IO-3 | `/info primitives/IO` lists no constructors; `/info primitives/pure` shows `(Fn [a] (primitives/IO a))` | An `/info` reading a seeded table | e2e REPL; `s124_io_opaque_pure_info` exists | A |
| IO-4 | Exhaustiveness of a user sum type: all arms covered passes, one missing fails | The deleted flag probe taking a user constructor with it | e2e, existing cells | F |
| IO-5 | A nested `IO` value displays `#io` after step 3: `[(primitives/sleep 0)]`, a box holding `(primitives/pure 1)`, and the top-level `(primitives/pure (primitives/pure 1))` as `Executing IO…` then `:(primitives/IO primitives/Int) #io` | The display walking an empty constructor table; a result owner refusing an `IO a` result | e2e REPL; with D-2 | A |
| IO-6 | The shapes and web platforms load and run after the schema change; their schemas have no `primitives/IO` key; a dylib built before is refused by the layout-hash gate | A stale committed schema; a walk that drops an ADT reached only through an `IO` field | e2e (`spec_platforms_adt`, `exemplar_web`, the `shapes-badabi` gate cells); unit rows in the backend's schema tier, RED first | A, M |
| IO-7 | A cache sidecar written under the previous `CACHE_SCHEMA_VERSION` is a miss | A table naming `primitives/IO.Pure` restored | unit (`dev`) | F |
| IO-8 | The bootstrap seeds no `IO` constructor and no `IO.*` key | A later edit reseeds one | unit (`dev`), RED against today's bootstrap | F |
| IO-9 | Step 1 equivalence: `(Pure x)` and `(primitives/pure x)` emit identical CLIF for an `Int`, a `String` and a nullary-ADT payload | A lowering differing from the path it replaces | `qa`, once, with `CRANELISP_CODEGEN_DUMP`, inside W3 | O |
| IO-0 | **Consumer migration (W4).** Every program text uses `primitives/pure` (or bare `pure` under a primitives import) where it means a lift | A migration that turns a constructor-behaviour test into a vacuous pass | Census: `Pure` in 169 test files (2,822 uses), 42 example files, 59 demo files, 5 user-doc files, 6 stdlib files, 5 exemplar files, 3 platform files. 17 test files name `primitives/Pure`, `IO.Pure`, `Bind` or `Effect` as identities: `test` classifies each use in W1; `qa` approves each deletion of a constructor-behaviour assertion. Step 3 refuses any unmigrated spelling, so completeness is structural | M |

The golden-CLIF corpora change at W4 where a golden reaches the stdlib's
`pure`; that change-set declares a scoped re-baseline (M).

### 5.2 `/type` (1089, memory-unsafe; 1099)

| Id | Condition | Wrong implementation rejected | Layer and seam | Class |
|---|---|---|---|---|
| TY-1 | The 14 1089 cells and `s124_type_macro_expression` | — | e2e, existing | A, F |
| TY-2 | After `/type 1`, the session holds no `__expr` | A check that still commits | e2e REPL; `/list` or `/info user/__expr` after | F |
| TY-3 | `/type (def x 1)` is refused; `x` stays undefined | A definition-producing macro slipping the classification | e2e REPL | A |
| TY-4 | `/type` of a macro whose home was restored from cache gives its type | The `/expand` resolver, which cannot run a cached macro | e2e, a second session over one directory | A |
| TY-5 | `/type` of a reference to an unloaded module is a located error and loads nothing | `/type` loading modules | e2e REPL, then `/modules` | A |
| TY-U | The staging check leaves the live table unchanged | — | unit (`dev`) | F |

### 5.3 Persistence and generated definitions (1068, 1101, 1005, 1102: data loss; S125-Q5)

| Id | Condition | Wrong implementation rejected | Layer and seam | Class |
|---|---|---|---|---|
| PS-1 | The four 1068 cells, the three `s124_save_after_*` cells, the 1005 cells and 1102's cell, with controls. `s124_1005_a_macro` is re-baselined to the §9.6.1 refusal. `persist_import_kept_by_save_stays_in_scope_and_is_written_once_control` stays green | — | e2e, existing | A |
| PS-2 | Authored order holds for a cache-restored module (rule 6), for a file load followed by REPL appends, and for a macro redefinition that newly uses a later macro | Positions reset by restore; appends interleaved with file positions | e2e save, restart, compare the written file | A |
| PS-3 | After a refused save reached through the inline-`mod` guard, a write failure (a read-only backing file) and an inline-`mod` module, the next cached session holds no definition the file lacks | Divergence tracked only for the render refusal | e2e save, cached restart, call | F |
| Q5-1 | A REPL turn redefining a live generated name is refused, located at the redefining form; the generated definition and the backing file are unchanged. For a generated function, a generated type and a generated implementation; a name generated by the file's own macro call; control: a written definition redefined is accepted | Redefinition through the ordinary replacement path; a refusal that still rewrites the file | e2e REPL | A |
| Q5-2 | Identical re-entry replaces: the same call after its macro was redefined replaces the generated definitions and the file keeps one call at its position; the same call through another spelling of the same macro (bare through an import, then qualified) is the same call. Refused: the same macro with other arguments that generates a live name; another macro generating the same name | Identity by macro alone; identity by spelling | e2e REPL | A |
| Q5-3 | A reload whose file replaces the call with a hand-written definition of a formerly generated name is accepted; a following REPL redefinition of it is accepted. In one file, a macro call and a later written definition of a name it generates are refused, in `--run`, linked and on reload | A reload validated against the records it replaces | e2e watched-file REPL and batch | A |
| Q5-U | Origin set from the expander's fact (a same-span expansion still reads `Generated`); call identity equal across spans and head spellings, unequal on any argument; validation; a rebuild carries no origin of a removed call | — | unit (`dev`) | F |
| PS-U | One selector row per `Decl` variant; the cache agreement transitions; publication refused while diverged | — | unit (`dev`) | F |

### 5.4 Display (1062, memory-unsafe; 1109)

| Id | Condition | Wrong implementation rejected | Layer and seam | Class |
|---|---|---|---|---|
| D-1 | `match_field_parameter_order::s124_1062_e_subject_repl`; a parameter no field mentions; a nested out-of-order product; each with an in-order control | Pairing by first appearance | e2e REPL | A, F |
| D-2 | `#closure` and `#io` at the top level and in fields: the two 1109 cells, `(Option.Some f)` → `(Option.Some #closure)`; `closure_value_display_shows_closure_token` migrated | Two marker sites diverging | e2e REPL | A |
| D-3 | A user type named `Vec` displays as its own constructors (lead: `push_adt_value_form` recognises `Vec` by bare name) | A spelling-keyed display decision | e2e REPL; a GREEN result closes the lead | A |

### 5.5 Module loading and search (1079, 1096, 1100, 1092; S125-Q4)

| Id | Condition | Wrong implementation rejected | Layer and seam | Class |
|---|---|---|---|---|
| E-1079 | The six `s124_1079_a/b_subject_*` cells flip with their controls; REPRO-1079-c (`s124_1079_c_chained_mount_reports_cycle_neg` and `s124_1079_c_opt_out_control`, both RED at the checkpoint) flips only with the walk's change. New: a path whose owner is loaded and mounts nothing at that segment is refused once, located at the reference, with no retry loop | A driver that loads the owner but the walk does not; a retry loop that never terminates | e2e; unit rows (`dev`) for the driver and `resolve_pending` | A |
| E-1096 | The four `s124_declared_child_*_not_replaced_*` cells and the five `search::s124_child_index_*` cells, with controls; §8.11.2 root-module cells stay green. Each subject asserts the value on stdout, not only the exit status (the library's value 1 equals a refused compile's status) | A resolver anchored for some callers only | e2e | A |
| E-1100 | The six `s124_macro_sibling_outer*` cells with controls; an `/expand` parity cell; a user-supplied argument naming a using-module symbol stays bare; the selective `stdlib/derive` import re-run under the stdlib-conformance exception | Qualification at the wrong macro; `/expand` diverging from the compiler | e2e | A |
| T-Q4 | An expansion that calls a private companion macro, and one that calls a private helper function, is refused as private from a module outside the defining module's subtree, and accepted from its submodule. Control: a public companion resolves | A qualified head bypassing visibility | e2e, `--run` and REPL | A |
| E-1092 | The two `s124_search_reach_*` cells; `neg_missing_dependency_no_row` and `index_typecheck_mutates_no_live_shared_state` stay green; a module that imports a macro by name from an unloaded module still has its ordinary definitions indexed | Session-dependent omission | e2e and the S124 module row | A |

### 5.6 Cache, platform and loading hazards

| Id | Condition | Wrong implementation rejected | Layer and seam | Class |
|---|---|---|---|---|
| T-0979 | Platform function types (spec §10.10.1) refused at load | Checking only a direct parameter; not following ADT fields | e2e (§6) | A |
| E-0994 | Int §7.1's two scheduler rows: a loaded completion after re-registration marks nothing in memory; the settle wait holds while a claim is outstanding; negative legs settle at once | Completion keyed by module name only | unit (`dev`), RED first | F |
| E-1085 | Int §7.7's *Owner* rows with a removal-RED, and T-OWNER as stated in the [S124 delta](s124-evidence-delta.md#143-allocated-to-test) | No exclusion; a lock that waits; a lock that outlives its owner | unit (`dev`) and e2e | F |

## 6. The settled delta for `test` (W1)

One dispatch. Every cell is e2e, unignored, and carries its `// spec:` line;
a defect cell also carries its `// defect:` line. A RED fails on its clause,
not on setup. No cell uses the standard library except E-1100's named
stdlib-conformance leg.

| Rank | Row | Spec | Shape | Expected at the checkpoint |
|---|---|---|---|---|
| 1 | **T-0979** | spec §10.10.1 | A test-only platform beside `platforms/shapes` declaring `(Fn [(Fn [Int] Int)] (IO Int))`, `(Fn [Int] (IO (Fn [Int] Int)))` and a parameter of a `deftype` with a function field; each refused at platform load, naming the function. Control: an ordinary signature in the same DLL loads and runs. `--run` and REPL | RED |
| 2 | **IO-1** new legs | spec §10.1 | Dotted, imported and pattern spellings of `Pure`, `Effect`, `Bind` refused; a user-constructor control in each spelling | RED |
| 3 | **IO-2** | spec §10.2 | `pure` applied, passed, bound, captured, stored; scalar and heap payloads; three modes; the marginal pair for the twice-forced node | RED |
| 4 | **IO-5** | repl §1.2.1, §1.5 | The box of `(primitives/pure 1)`, the nested vector, the top-level double `pure` | RED |
| 5 | **TY-2 to TY-5** | repl spec §3 (`/type`) | As §5.2 | TY-2 RED; the rest as observed |
| 6 | **Q5-1 to Q5-3**, and `s124_1005_a_macro` re-baselined | spec §9.6.1; repl §15.6, §18 | As §5.3 | Q5-1 and refused legs of Q5-2 RED; Q5-3's one-file leg GREEN; the rest as observed |
| 7 | **PS-2, PS-3** | repl §15.4 | As §5.3 | as observed; report each |
| 8 | **D-1, D-2 new legs; D-3** | spec §12.9.1, repl §1.5, §4.1.3 | As §5.4 | D-1, D-2 RED; D-3 as observed |
| 9 | **E-1079** negative cell | spec §8.5.4, §8.6.6 | As §5.5 | as observed |
| 10 | **T-Q4** | spec §9.3.4 | As §5.5 | the private legs as observed; report |
| 11 | **E-1100, E-1096, E-1092 additions** | spec §9.3.4, §8.2.5; repl §17.19 | As §5.5 | as observed |
| 12 | **T-1003** | repl §4.1.3 | REPL, no cache: (a) `Qtok`, `Qwrap (Qtok …)`, then `Qtok`; (b) reversed, asserting `Qtok`'s echo. Both list `Qa Qb`. Control `Qwrap2 (Qother …)` | RED |
| 13 | **T-1081** | spec §8.10.1, §8.10.2 | REPRO-1081 gains the outcome clause (every route exits 11). The twin where `P` imports from `P.c` is refused as a cycle from each batch entry and in both REPL orders. A session-save leg and a restart leg agree with the cold routes. Do not assert the chain's text | GREEN |
| 14 | **T-1036** | repl §5.5, §16.6 | `m.cl`: a macro whose expansion at line 3 defines a function referencing `discover-tests`; `p.cl` imports it. A REPL session caches `m`; then `--run p.cl`. The refusal is located at `m.cl:3:` with no offset of 1000000 or more, as the cold `--run` control is | RED |
| 15 | **T-0985** | spec §7.2.3 | User `(deftype (Float a) (Wrap [:a v]))`, unary `Fun`, `(impl (Fun f) (Fun Float) …)`; bare and qualified exit 42; `Flt` control 42; `(Fun primitives/Int)` stays refused | RED |
| 16 | **T-NC2** | root `AGENTS.md` §Assurance (R18) | A repository gate like `citation_drift.rs` over `src/` and the types, typecheck and backend crates outside test modules, for discarded `ConcreteType::from_type` results and `Type`/`ConcreteType` defaults. Allow-list: `mono_expr.rs::lenient_from_expr`, citing FIXME 0929; and, until W5 deletes them, the two `IO`-case inputs of §9.2 (`compiler/apply.rs` `constructed_ty`, `control_flow/fn_as_value.rs` `adt_ty`), citing the backend opaque-IO design §3. An allow-list entry that matches no site fails the gate. Detection proof in the same file, including the stale-entry leg | GREEN |
| 17 | **T-OWNER** | int §7.7 | As the S124 delta states | RED |
| 18 | **T-0761** | spec §12.3.1 | `rc_escape_release_0763.rs` F under `BOTH_MODES`; the 0760 vector-of-strings capture with a `--link` face | GREEN |
| 19 | **T-0785** | spec §7.1.1 | `(deftrait Bad (show [x] :String))`: `annotation missing expression` at 24..25; `Bad` undefined; `(show [x] String)` control | GREEN |
| 20 | **IO-0 classification** | — | The 17 identity-naming test files: each use classified as a lift or as constructor behaviour, with the proposed migration of each constructor-behaviour assertion | report to `qa` |
| 21 | **T-0978** | — | Comment-only repairs in `platform_errors.rs`, `concurrency_poll_edge_guards.rs`, `exemplar_web.rs` | — |

**Attributions for the RED cells.**

- **T-0979:** `src/platform.rs::register_platform_in_tc`, read in source; it
  checks only the IO return. Focus band. *Refuted if* a function-typed
  parameter is refused there today.
- **Q5-1, Q5-2:** `src/` (binary clean §4.4): the binary records no origin
  for a generated definition, so the commit's validation cannot refuse.
  Focus band (W7).
- **T-1003:** provisional. `src/repl/format_type.rs` reads the listing
  through `cranelisp_types::lookup_type_def_chain`, which resolves the bare
  spelling; the hypothesis is that it finds `Qwrap.Qtok`. *Refuted if* the
  lookup returns `Qtok`'s definition for the subject. Focus band (W9).
- **T-1036:** provisional, **not `src/`.** The restored declaration carries
  the expansion's synthetic span because the stored module records no
  definition origin (the cache schema in
  `crates/cranelisp-backend/src/cache/serialize.rs`; the remedy is a backend
  schema and facade change through `arch`). *Refuted if* the restored
  declaration holds the written span and the binary renders it wrongly.
  Carried on its cell. Class `error-swallow` is the nearest; `test` may
  request a vocabulary entry.
- **T-0985:** `crates/cranelisp-typecheck/src/traits/impl_check.rs:297`,
  with the renamed control. Class `spelling-keyed-decision`. Carried.

**Completion criteria.**

- Each row's clause map is reported: which assertion carries which clause,
  and which wrong implementation it rejects.
- Each RED is reported with the assertion it failed on; `qa` reads it
  before `dev` builds on it.
- Each expected GREEN is green; an unexpected RED, or an "as observed" cell
  that is RED, is defect intake for `qa` with its output.
- IO-0's classification is delivered as a list `qa` can approve row by row.
- `tests/plan/spec_link_check.py` reports no mis-cited or malformed anchor.
- Nothing under `src/`, `crates/` or `stdlib/` changes.

## 7. Census: `match` forms with no constructor arm

Input to the user's ruling on a general refusal. Measured at the checkpoint
by a reader over every `.cl` file in `examples/`, `stdlib/` and `exemplar/`,
and over the Cranelisp program text in string literals of `tests/*.rs` and
`tests/**/*.cl`. A pattern is a constructor pattern when it is a list headed
by a capitalised or dotted name, or a bare capitalised or dotted name.

| Area | `match` forms read | No constructor arm | Of which: variable only | wildcard only | literal and wildcard |
|---|---|---|---|---|---|
| tests | 744 | 92 | 80 | 8 | 3 (plus one empty) |
| examples | 81 | 0 | — | — | — |
| stdlib | 173 | 0 | — | — | — |
| exemplar | 50 | 0 | — | — | — |

- **stdlib.** The reader found three, all in `stdlib/derive/helpers.cl`
  quasiquoted templates whose pattern is spliced in (`~s`); each expands to
  a constructor pattern. None is a real case.
- **By scrutinee type, tests (from the scrutinee's text):**
  - `Vec`, about 75: `match` used as a binder in ownership and counting
    cells (`uniform_counting.rs` 39, `binding_indirection_consume.rs` 11,
    `join_forwards_its_binder.rs` 7, and others). Scrutinees are vector
    literals, `vec-set` results and vector parameters.
  - `Int`, about 10: literals and integer parameters (`spec_06_pattern_matching`,
    `spec_03_types`, `dotted_binder_reject_0702`, `generic_value_use_mono`,
    `vec_assoc_param_mutate_return_uaf`, `trace`).
  - A user ADT matched only by `_`, 3 (`spec_08_modules`: `Shade.Blue`,
    `Red`, `(shapes/Hid 8)`).
  - `Bool` and `String`, one each, with literal patterns in
    `spec_06_pattern_matching`.
  - **`IO`: none.**
- **Limits.** Programs assembled by `format!` or split across several string
  literals are not read: `(match ` occurs 792 times in the test sources and
  744 forms parsed. The 7 forms whose arms the reader could not classify are
  excluded. Scrutinee types are read from the text, not inferred.
- **What a general rule would touch:** no example, stdlib or exemplar
  program; about 92 test programs, nearly all ownership cells that use
  `match` as a binding form.

## 8. Handoffs

- **`test`:** §6 (W1).
- **`dev`:** the unit rows of §5 (IO-7, IO-8, TY-U, PS-U, Q5-U, the 1079
  rows, E-0994, E-1085), each observed RED before its fix; the rename at
  `src/agent/mod.rs:717`; ACT-1060 can be deleted (§1).
- **`design`(backend, typecheck):** the zero-argument partial application
  of `pure` (§4.1).
- **`spec`:** the two open questions of [§4.1](#41-ambiguities).
- **`design`(intrinsics):** the diagnostic-modes design's *Open: FIXME 0857*
  line can cite the [regrade](#23-r8s-diagnostic-modes-regraded); 0857 is
  deleted.
- **`design`(int):** `design/int/int.md` links ACT-1004 (line 508) and
  ACT-1015 (line 2394), both closed.
- **`audit`:** `audits/cranelisp-backend-s122.md` line 38 links ACT-1022,
  closed.
- **`dev`(`stdlib/`):** `stdlib/plan-stdlib.md` §6.2's gate (FIXME 0907) is
  open; its cases are written with `primitives/pure`.

## 9. W1 acceptance

`test`'s W1 record (Codex session `932a3a55`; deleted at W4's close and
recoverable from Git history) held the clause map, per-cell results and the
IO-0 token ledger. `qa` read each
RED's failing assertion against §6.

### 9.1 The full run, outside the sandbox

`cargo nextest run --no-fail-fast` by `qa`, on the W1 tree: **8,271 run,
8,037 passed, 234 failed, 1 skipped, 229 s.**

- **234 = the opening 143 + 91 W1 cells.** Every opening failure still
  fails; none passes. Of the 91, 90 are REDs the W1 record lists. The
  91st, `generated_definition_persistence::s125_ps3_inline_module_no_ghost_restore`,
  is GREEN in the W1 record and RED here: after a refused save of an
  inline-module file, the cached restart evaluates `(m/unsaved)` to 42.
  It is ACT-1102's face through the inline-`mod` guard (§9.2); the record's
  GREEN came from the sandboxed run and is superseded.
- **No allocated RED passes, and no other test fails.** The eight HTTP
  cells and three reactor module tests that failed in `test`'s run pass
  here: their failures were the sandbox (port binding refused; the
  backstop), not the product.
- **No genuine regression.**

### 9.2 Classification of the unexpected REDs

- **PS-3, `s125_ps3_inline_no_ghost_restore` (SIGSEGV): ACT-1102, the
  designed gap.** The signal is not in the first session. Observed by a
  logging wrapper around the binary under the cell, and by hand: the first
  session (a file holding a function and an inline `mod`, then one REPL
  definition) exits 0 and its save is refused (the file lacks `unsaved`);
  the cached restart's call `(unsaved)` ends on signal 11. Control: the same
  restart with `--no-cache` exits 0. The cell's restart clause is therefore
  the face itself, observed as a crash. Mechanism: binary clean §4.3, the
  inline-`mod` early return of `regenerate_backing_file`, read in source by
  `design`(int); W7. Its sibling, `s125_ps3_inline_module_no_ghost_restore`,
  is the same face without the crash (§9.1).
- **T-NC2 production gate: the two sites are the `IO` case W5 deletes.**
  `compiler/apply.rs` (the `constructed_ty` of `compile_var_apply`) and
  `compiler/control_flow/fn_as_value.rs` (the `adt_ty` of the constructor
  wrapper) each default to `ConcreteType::ADT(fqtn, [])`. Their only
  consumer is `append_runtime_ctor_fields`, which reads the type only for
  `primitives/IO`'s `Pure` (`pure_payload_type` returns `None` for every
  other type), and for `Pure` it refuses an argument-less `IO` loudly. So
  the placeholder never reaches a gate as a concrete fact. Both are
  inputs the backend design §3 deletes at W5. **Amended (§6 row 16):** both
  join the allow-list until W5, citing that design; an allow-list entry
  that matches no site fails the gate, so W5 must remove them. Row 16 is
  GREEN once that lands.
- **The remaining "as observed" REDs** are faces of band defects, not new
  defects: TY-4 (a cached macro under `/type`, 1099, W6); D-1's unused
  parameter (`<invalid-string:42>`, 1062, W2); D-3 (a user type named
  `Vec` displays `[]`, the bare-name lead in `src/display.rs`, W2);
  E-1100's parity and selective-derive cells (1100, W8); E-1092's
  unloaded-macro import (1092, W8); T-OWNER (W8).
- **REDs that wait on a later wave are accepted as RED for the missing
  surface:** IO-2's builtin cells and IO-5's box and double-`pure` faces
  stop at the absent `pure`; they are re-read after W3 before their clauses
  are credited. The payload observers' detection proof and the twice-forced
  fixture control are GREEN.

### 9.3 IO-0 classification

Approved as proposed for the 15 files whose uses are all lifts or
supporting labels: migrate each to `primitives/pure`, keep every behaviour
assertion. For the others:

| File | Decision |
|---|---|
| `tests/spec_10_io.rs` | Approved: migrate the lifts; keep the opaque-constructor refusal spellings and patterns, and the forbidden-envelope and `Bind` output assertions |
| `tests/ownership_fences.rs` | Approved: replace the synthetic `primitives/IO.Pure` CLIF-name sample with an unrelated whitespace-bearing name; keep both extractor assertions |
| `tests/spec_12_runtime.rs` | Approved: retire the IO-destructuring leg of `panic_sources_report_exact_messages_run` and `matched_io_value_has_no_match_panic_control` at W5, when their `Pure` arm is refused at compile time; keep the other panic sources. No accepted program then reaches spec §12.7.2.1's "Non-exhaustive match" row; `qa` re-bands it at W5 and `spec` says whether the row stands |
| **`tests/s99_fixtures.rs`** (not in the ledger) | **Added.** Line 177 matches `(Pure value)` on an IO value to extract the solve's result. W4 restructures the driver so the workload's value is read without matching `IO`, keeping the marginal pair's subject and control symmetric; `qa` approves the rewrite before it lands |

The ledger read the 17 identity-naming files only. Outside them, `qa`'s
search finds no other `IO` pattern or constructor identity in `tests/*.rs`
or the `.cl` fixtures, except comments.

### 9.4 Verdict

- **W1 is accepted**, with two amendments for `test`: T-NC2's allow-list
  and stale-entry leg (§6 row 16), and the `s99_fixtures.rs` row (§9.3).
- **Go for `dev`: W2** (display: 1062, 1109, and D-3's bare-name `Vec`)
  and **W3** (`pure` step 1; `qa` measures IO-9 inside it). Neither waits on
  the amendments.
- **The W1 record** is a dispatch record, not a fixture or a standing
  document. Its findings are folded here. `test` removes `REPORT.md` and its
  `tests/AGENTS.md` link; the TSV ledgers stay as W4's working input and go
  with W4's close.

## 10. W2 adequacy (display: 1062, 1109, D-3)

**Adequate.** `dev`(`src/`) changed `src/display.rs` and `src/styled.rs`;
`review` (Codex `e02a756a`) reports no findings.

### 10.1 The full run

`cargo nextest run --no-fail-fast` by `qa` on the W2 tree: **8,279 run,
8,055 passed, 224 failed, 1 skipped, 262 s.** Against `qa`'s W1 run
(§9.1, 234 failed):

- **Nothing newly fails.**
- **Ten cells pass that failed:** the W2 cells
  `match_field_parameter_order::s124_1062_e_subject_repl` and
  `s125_d1_unused_parameter_display`; `repl_introspection::s124_markers_closure_display`,
  `s124_markers_nested_io_display`, `s125_d2_option_closure_marker`,
  `s125_d3_user_vec_displays_own_constructor` and the migrated
  `closure_value_display_shows_closure_token`; `opaque_io::s125_io5_vector_display`;
  `concrete_boundary_census::s125_nc2_production_concrete_boundary_census`
  (the §9.2 allow-list amendment); and
  `generated_definition_persistence::s125_ps3_inline_module_no_ghost_restore`
  (§10.2).
- The `launch_grid_corrupt`, `launch_vec_send_corrupt` and 1090 changes
  `dev` reported are relative to the sandboxed W1 record: the first two
  passed in `qa`'s W1 run, and the run-dependent 1090 cell fails in this
  one, as at the opening.

### 10.2 Classifications

- **`s125_ps3_inline_module_no_ghost_restore` is run-dependent, not
  fixed.** RED in `qa`'s W1 full run; 20 of 20 GREEN alone on the W2 tree;
  W2 touched no persistence code. Its restart does not check that it was a
  cache hit, so a restart that recompiles from source passes vacuously.
  **Amendment for `test`:** assert the cache-hit precondition before the
  ghost clause, as T-1036's cached cell does. Its sibling
  `s125_ps3_inline_no_ghost_restore` stays RED, 10 of 10 alone (ACT-1102,
  W7).
- **`<invalid:N>` → `<invalid-string:N>`:** not a defect. An internal
  marker for an unreadable string; no specification names its text. One
  classifier now produces it.
- **Bare-name `Vec` recognition outside `src/`:** not defect intake.
  `crates/cranelisp-typecheck/src/resolve.rs:383` compares the module too.
  `compiler/vec_codegen.rs:265`, `control_flow/fn_as_value.rs:42`,
  `heap.rs:546`, `compiler/trace_codegen.rs:427` (backend) and
  `crates/cranelisp-types/src/heap.rs:208` compare the bare spelling, the
  `spelling-keyed-decision` shape. Probe, `--run`, plain and under
  `CRANELISP_RC_DEC_CHECK` and `CRANELISP_RC_STATS`: a user nullary type
  `Vec` built, bound and matched in a loop, and a user `(Vec a)` built and
  matched 1,000 times, behave as a renamed control does and balance. No
  wrong outcome is observed; the trace site's misrender is in the deferred
  trace work. Recorded as a lead for the sprint whose focus holds the
  backend and types: compare `primitives/Vec` by identity at each site.
- **D-1's falsifier** (a `<field types unavailable: …>` print) is witnessed
  at the module tier by `dev`'s unit row. `qa` held here that no legitimate
  program executes a value of residual type, so no e2e cell was owed. That
  was wrong: the falsifier fires on an ordinary REPL value (§30.2).
- **Red-first evidence** for the seven unit rows is `dev`'s record; `qa`
  did not replant.

### 10.3 Go

**Go for W3:** `dev`(backend) the `pure` lowering, then `dev`(`src/`) the
`insert_primitive` seed. `qa` measures IO-9 (the CLIF of `(Pure x)` and
`(primitives/pure x)` for an `Int`, a `String` and a nullary-ADT payload)
once both are in and before W4 starts, then re-reads IO-2 and IO-5's box
and double-`pure` cells.

## 11. W3 adequacy (opaque `IO` step 1: `pure`)

**Adequate.** `dev`(backend) adds `IoCombinator::Pure` and its emitter;
`dev`(`src/`) seeds `primitives/pure` with `insert_primitive`.

### 11.1 The full run

`cargo nextest run --no-fail-fast` by `qa` on the W3 tree: **8,282 run,
8,095 passed, 187 failed, 1 skipped, 232 s.** Against the W2 reading (224
failed): **nothing newly fails; 37 cells pass** — 224 − 37 = 187:

- the 30 IO-2 value cells (applied, passed, bound, captured and stored;
  scalar and heap; `--run`, linked and the REPL), the twice-forced heap
  marginal (`s125_io2_twice_forced_heap_balances`, balanced under
  `CRANELISP_RC_DEC_CHECK`) and `s125_io5_box_display`;
- `spec_10_io::s124_io_opaque_pure_info` and four S124 cells whose
  controls name `primitives/pure` (`s124_effect_field_pure_control_*`,
  `s124_bind_spelling_builtin_control_run`).

Still RED, as planned: IO-1's 21 spelling cells and the S124 1105–1108
subjects (W5); `s125_io5_double_display` (§11.3).

### 11.2 IO-9: the step 1 equivalence

Measured once with `CRANELISP_CODEGEN_DUMP='*'`, `--run --no-cache`, for
`(defn mk [] (primitives/Pure v))` against `(defn mk [] (primitives/pure v))`
with `v` an `Int`, a `String` (`str-concat` result) and a nullary-ADT
constructor.

- **The node is identical.** `pure`'s inline sequence in `mk` is
  instruction for instruction the body of today's
  `primitives/IO.Pure [T]` instance: a 24-byte allocation, tag 0 at +16,
  the payload at +24, and the glue word at +32 — `iconst 0` for the `Int`
  and the nullary payload, `func_addr` of the `String` release glue for the
  `String`.
- **The call site is not.** `(Pure v)` in a user function calls that
  instance through its GOT slot; `(primitives/pure v)` emits the node
  inline. The design's claim that the CLIF "in the same body is identical"
  (backend opaque-IO §1.2, §6.2) is therefore true of the node, not of the
  body. The difference removes one indirect call and changes no layout,
  glue word or ownership. It is a wording correction for `design`(backend),
  not a defect.
- **IO-2's first-class faces** (passed, bound, captured, stored) deliver
  the payload in all three modes. Their glue word is `dev`'s module row
  (direct and wrapper lowering emit identical CLIF); the e2e marginal
  covers the direct face only. Accepted on that pair.

### 11.3 `s125_io5_double_display`: attributed to `src/result_owner.rs`

- **Observed.** `(primitives/pure (primitives/pure 1))` at the REPL prints
  `Executing IO…`, then `Error: codegen error at 0..0: program result
  reached the result owner still wrapped in (primitives/IO Int) …`. The
  same with the constructor spelling `(primitives/Pure (primitives/Pure 1))`:
  it predates the seed.
- **Control, one difference.** `(primitives/pure [(primitives/pure 1)])`
  displays `:(primitives/Vec (primitives/IO primitives/Int)) [#io]`: an
  `IO` nested inside the payload is displayed and released. Only a payload
  whose own type is `IO` is refused.
- **Mechanism, observed at its seam:** the message is
  `OwnedProgramResult::new`'s (`src/result_owner.rs`, the `ty.is_io()`
  refusal). It is the design as written: the
  [result-owner design](../../design/int/result-owner.md) §4.2 makes "an
  `IO a` type" unconstructable at the owner so that a second unwrap cannot
  happen, and so refuses the legitimate one-hop payload of type `IO Int`.
  Spec (REPL §1.2.1, §1.5; appendix D's S125 leads) requires
  `:(primitives/IO primitives/Int) #io`.
- **Class:** `check-domain-overreach`. **Locus:** `src/result_owner.rs`;
  the cell's `// defect:` line names `src/display.rs` and is a `test`
  notation repair. The diagnostic's category (`codegen error`, `0..0`) is
  a second face of the same refusal.
- **Focus band.** It needs `design`(int) first: the fix reverses a stated
  invariant of the result-owner design, so the design must say how a
  second unwrap stays unconstructable (for example, by taking the payload
  type only from the one-hop `ConcreteType::result_root()` of the static
  result) and which glue releases an `IO` payload. `dev` then builds it
  with a unit row RED first; this cell is the e2e.

## 12. W4 decisions (consumer migration)

`test`'s W4 record (Codex `1c0f9527`) is outside the repository, under
`/tmp/s125-test-w4/`. `qa` did not take a full run: `dev`(`src/`) holds the
test runs for the result-owner fix.

### 12.1 The failing set

`test`'s final unsandboxed run, 193 failed, against `qa`'s W3 set (§11.1,
187), compared by name:

- **Added: exactly the seven golden-CLIF checks** —
  `clif_golden_lane::clif_golden_lane_no_drift`,
  `ownership_fences::clif_golden_single_module_smoke` and five
  `golden_clif_w0b_*` (`ctor_def`, `expr_disposition3`, `macro_clause`,
  `multisig_variant`, `synth_accessor`).
- **Removed: only `trace::s124_1090_mixed_restore_subject`,** the
  run-dependent cell, which passed in that run. It stays a carried defect.
- **No other difference.** No migrated cell regressed.
- **No assertion was deleted.** In the dispatch's own diff the two removed
  lines with an assertion are rewritten in place: one reformatted, and one
  is the PS-3 restart gaining its cache-hit precondition (§10.2).

### 12.2 `tests/s99_fixtures.rs` rewrite: approved

The proposal replaces `repeat-work`'s match on `(Pure value)` with a
`bind` chain: bind `(solve-once)`, recurse inside the continuation, and
`pure` the sum. `main` returns `(repeat-work COUNT)` directly.

- **The pair stays symmetric.** Both children share the driver; only
  `solve-once` differs (`(primitives/pure 154)` against the fixture's
  `main` body, which is a `match` whose arms each end in
  `primitives/pure`).
- **The assertions keep their power.** Each child must exit `COUNT`, which
  requires 154 from every solve. The control's twice-minus-once residual
  must be 0, which proves the `bind` driver itself retains nothing per
  execution; the subject's must also be 0.
- **What it changes:** the driver now consumes an IO value through the
  runtime rather than reading its constructor, which is the only spelling
  W5 leaves. It no longer silently counts 0 for a non-`Pure` node, as the
  old `_ 0` arm did.

### 12.3 Golden-CLIF drift: scoped re-baseline approved

Both corpora's manifests (`tests/fixtures/clif_baseline/MANIFEST.md`,
`tests/fixtures/clif_w0b/MANIFEST.md`, owned by `test`) require an
emission-affecting change-set to re-capture only the drifted entries and
attribute every changed frame. W4's migration is that change.

- **Approved:** re-capture the 19 migrated entries (14 L-B1, 5 W0.b).
- **The attribution each entry must satisfy,** read from IO-9 (§11.2):
  the `primitives/IO.Pure [T]` instance frame disappears; each GOT-indirect
  call to it becomes the inline allocation and the tag, payload and glue
  stores; value and function numbering shift accordingly. A hunk outside
  those three kinds stops the re-baseline and returns to `qa`.
- **Determinism:** each re-captured entry is captured twice and the two
  captures are byte-identical.
- **The W0.b manifest's** claim that every golden carries the `IO.Pure`
  instance frame is corrected by `test` in the same change-set.
- **Class:** maintenance check. The goldens guard emission drift; they
  carry no acceptance authority over `pure`, which IO-2 and IO-9 hold.
- W5 deletes the constructor path's `IO` case and should not change these
  captures again; a drift there is attributed afresh.

## 13. W4: the tests part, and the remaining consumers

### 13.1 The full run

`cargo nextest run --no-fail-fast` by `qa` after `test`'s s99 rewrite and
golden re-baseline (Codex `8fb3d11a`) and `dev`(`src/`)'s result-owner
change: **8,284 run, 8,098 passed, 186 failed, 1 skipped, 237 s.**

- **The failing set is §11.1's W3 set less exactly one cell:**
  `opaque_io::s125_io5_double_display`, the result-owner fix (§11.3).
  Nothing else differs by name.
- **The seven golden-CLIF checks pass** under the approved re-baseline
  (§12.3). `test` reports both captures byte-identical and every hunk within
  the three allowed kinds.
- `trace::s124_1090_mixed_restore_subject` fails again: run-dependent, as
  at the opening.

**The tests part of W4 is adequate.**

### 13.2 Remaining constructor uses outside `tests/` (at this tree)

Counted over committed files (`git ls-files`); generated demo transcripts
under `repl/demos/runs/` and the platform schemas are excluded. A use is a
code occurrence: an application `(Pure …)`, `(Effect …)` or `(Bind …)`, a
qualified or dotted spelling, or the name in an import or export list.

| Owner | Area | Files | Uses | Mechanical? |
|---|---|---|---|---|
| `dev`(`stdlib/`) | `stdlib/` | 3 | 11 | **No, in part.** `io/monad.cl` defines its own `pure` as `(Pure x)`, and `stdlib/prelude.cl` exports `io.monad [pure …]`. It must re-export `primitives/pure` rather than define a second one (backend opaque-IO design, *The standard library re-exports*), or a program importing both sees two `pure`s. `core/io.cl`'s lifts (`map-io`, `when-io`, `unless-io`, `sequence-io`) are mechanical; its header comment describing the constructors is stale prose |
| `dev`(`exemplar/`) | `exemplar/` | 3 | 4 | Yes: imports of `Pure` in `tests.cl`, `solver.cl` and `user.cl` (unused there), and one lift. Corrected: the first count missed `user.cl` |
| `training` | `examples/` | 40 | 127 | **No.** The lifts and `examples/lib/prelude.cl`'s `(export [primitives [Pure]])` are mechanical, but the lessons teach `Pure` as a constructor: example 21 (`hello-io`) Part 1 and Part 4 ("Pure and bind are the only primitives you need"), and the repeated "Wrap the sum … in `Pure`" comment in examples 01–19. The lessons need re-teaching, not a rename |
| `docs` | `user/` | 4 | 29 | **No, in part.** The concurrency guide's six imports and its lifts are mechanical. Every sample is executed by `user_samples.rs`, so a sample left on `Pure` turns RED at W5; prose that describes `Pure` as a constructor needs rewording |
| `test` | `repl/demos/` | 6 | 27 | Yes: `07-io-and-effects.demo` and the `archive/` ring demos (`ring4a`, `ring4b`, `ring4e`, `ring4s`, and `ring4j`, which the first count missed) import and apply `Pure` |
| `test` | `platforms/poll-pool/` | 1 | 1 | Yes: a doc comment |
| `qa` | `platforms/stdio/`, `platforms/test-capture/` | 0 | 0 | — |

Not part of W4's consumer migration, and listed for the cascade:

- **Platform schemas**, the [shapes schema](../../platforms/shapes/src/shapes.platform-schema)
  and the [web schema](../../exemplar/platforms/web/src/web.platform-schema), list `Pure`, `Effect`
  and `Bind` as `IO`'s constructors; W5 regenerates them (IO-6).
- **Compiler source and its designs:** 22 uses in 9 `src/` files, 53 in 15
  `crates/` files and 10 in 5 `design/arch/` files. The bootstrap, the
  backend's constructor path and the fixtures go in W5; design prose
  follows its owners.
- `spec/`: no code occurrence.

Serial order that keeps the suite green: `dev`(`stdlib/`) first (the
re-export, so `pure` has one identity), then `dev`(`exemplar/`), `training`,
`docs`, and `test`'s demos. Each owner's change-set is checked by its own
lane: stdlib conformance, `exemplar*`, `examples.rs`, `user_samples.rs` and
the demo replay.

## 14. W4 close

### 14.1 The full run

`cargo nextest run --no-fail-fast` by `qa` after every consumer migrated:
**8,284 run, 8,098 passed, 186 failed, 1 skipped, 249 s.** The failing set
is §13.1's, name for name: the migrations of `stdlib/`, `exemplar/`,
`examples/`, `user/`, the demos and the poll-pool platform added and removed
no failure.

### 14.2 Constructor uses that remain

Over every committed and untracked file outside `repl/demos/runs/` and
`sprints/archive/`, counting code occurrences as in §13.2:

- **W5's own targets:** `src/` (10 files), `crates/` (15), `design/arch/`
  (7), and the two platform schemas (shapes, 6; web, 15).
- **Test cells kept on purpose:** `tests/opaque_io.rs` (IO-1's refusal
  subjects), `tests/spec_10_io.rs` (the opaque-constructor refusal
  subjects and patterns, and the forbidden-envelope check),
  `tests/spec_12_runtime.rs` (the two legs W5 retires, §9.3).
- **Records and prose, not programs:** the W1 ledgers (since deleted);
  `qa`'s plans; `audits/cranelisp-typecheck-s124.md`
  (a dated assessment); the sprint packets; and design prose in
  `design/backend/` (4 files), `design/int/` (3) and `design/typecheck/` (2),
  which their owners align with W5's change-set.
- **Nothing in `stdlib/`, `exemplar/` (outside its schema), `examples/`,
  `user/`, `repl/demos/` or `platforms/`** other than the two schemas.

The W1 record goes now that W4 closes (§9.4); `test` deleted it.

### 14.3 The single `pure` identity: one cell allocated

- **Risk.** A standard library that again defines its own `pure` beside
  `primitives/pure` gives a program two `pure`s: a bare use is then
  ambiguous where both are visible, or silently takes the library's.
  `stdlib/` held exactly that until this wave.
- **Existing evidence does not see it.** `stdlib_conformance`'s
  all-modules cell glob-imports every public module beside
  `(import [primitives [pure]])` but calls `primitives/pure` qualified, so
  an ambiguous bare `pure` is never resolved. `qa`'s probe shows the
  current state is right: under the workspace prelude, `/info pure` names
  `primitives/pure`, and a bare `(pure 1)` after importing
  `primitives [pure]` evaluates to 1.
- **Allocated, T-PURE-ID** (`test`, under the stdlib-conformance exception):
  with the workspace prelude, REPL and `--run`, `/info pure` names
  `primitives/pure`, and a program that imports `primitives [pure]` and
  calls bare `(pure 1)` resolves with no ambiguity. Wrong implementation
  rejected: a library `pure` with a second identity. Class: maintenance
  check (it guards the library's design, not the language). Expected GREEN.
  It does not block W5.
- **Not allocated now:** `stdlib/plan-stdlib.md` §6.2's `core.io`
  self-tests. Their gate is open and they are `dev`(`stdlib/`)'s plan
  item; they test the combinators, not the identity.

### 14.4 Verdict

**W4 is closed.** **Go for W5**, the cascade, as one change-set in the order
types → typecheck → backend → `src/`, with the bootstrap assertion (IO-8)
and the schema rows (IO-6) observed RED first. At W5, `qa` re-bands spec
§12.7.2.1's "Non-exhaustive match" row and re-reads IO-1 and the 1105–1108
subjects.

## 15. W5 adequacy (opaque `IO` step 3, the cascade)

**Adequate**, subject to `review`'s report on the change-set (running
read-only).

### 15.1 The full run

`cargo nextest run --no-fail-fast` by `qa` after `test`'s W5 follow-ups
(Codex `4e3a52b8`): **8,281 run, 8,124 passed, 157 failed, 1 skipped,
248 s.** Against §14.1's set (186), by name:

- **30 cells pass that failed:** the 21 IO-1 spelling cells in
  `opaque_io`, and the nine S124 opaque-`IO` subjects in `spec_10_io` —
  `s124_effect_field_forced_not_signaled_{run,link,repl}`,
  `s124_effect_field_unforced_not_signaled_run`,
  `s124_effect_field_match_not_signaled_repl` (1106),
  `s124_bind_spelling_outcomes_agree_run` (1105),
  `s124_io_match_not_runtime_match_failed_run`,
  `s124_io_match_wildcard_control_run` (1107) and
  `s124_io_opaque_pure_constructor_refused_run` (1108).
- **One cell fails that passed:**
  `public_api_relocations::public_api_check_runs_against_every_baselined_crate`,
  the expected baseline drift of rows IO-T and D-1. The baselines are
  regenerated at the phase checkpoint, where `arch` compares the diff with
  the approved rows.
- 186 − 30 + 1 = 157. Nothing else differs.
- **The Sudoku exemplar cell is the ACT-1018 guard:**
  `exemplar_ownership_residue_s116::sudoku_warm_serial_solve_retains_nothing`
  has failed in every `qa` run since the opening (§1, ACT-1018's five
  cells) and is not new.

### 15.2 Re-reads

- **IO-1:** each of the 21 cells asserts that the diagnostic names the
  constructor and is a refusal (undefined, unknown, private or not found)
  in its mode; the nine user-constructor controls pass in every spelling.
- **1105–1108:** their subjects pass on refusal; 1107's wildcard cell is now
  refused at its `Pure` arm.
- **IO-6:** the regenerated shapes and web schemas name `primitives/IO`
  only in comments; `spec_platforms_adt` (round trip in three modes and
  the cache restore; the layout-hash gate refusing under `--run` and
  `--link` and warning at the REPL) and the three `exemplar_web` cells
  pass; the backend's `io_result_root_yields_its_payload_and_no_io_entry`
  passes.
- **IO-8:** `bootstrap::tests::io_is_seeded_with_no_constructor` passes;
  its red-first run is `dev`'s record.
- **IO-7:** the cache schema rows pass
  (`cache_schema_version_mismatch_falls_through`,
  `cache_schema_version_bumped_for_r5_representation_change`).

### 15.3 Bands

- `spec/03-types.md` §3.2.3, `spec/10-io.md` §10.1, §10.2 and §10.2.3:
  re-banded to the passing cells.
- `spec/12-runtime.md` §12.7.2.1, the "Non-exhaustive match" row: no
  accepted program reaches it once `IO` has no constructors, and its former
  cells are retired. Banded unreachable; whether the row stands is a
  question for `spec`.

## 16. W6 adequacy (`/type`: 1089, 1099)

**Adequate for 1089 and 1099; one review finding is open and fixed in this
wave before it closes (§16.3).**

### 16.1 The full run

`cargo nextest run --no-fail-fast` by `qa` on the W6 tree: **8,286 run,
8,145 passed, 141 failed, 1 skipped, 275 s.** Against §15.1's set (157),
by name:

- **17 cells pass that failed:** the 14 1089 cells (`s124_1089_*_subject`,
  `s124_type_err_{defn,deftype,deftrait,impl,defmacro}`,
  `s124_type_expr_fresh_{box,some}_remains_evaluable`,
  `s124_type_pure_{deftrait,deftype}_not_defined`,
  `s124_type_pure_impl_not_installed`), 1099's
  `s124_type_macro_expression`, and TY-2 and TY-4
  (`s125_ty2_type_leaves_no_expr`, `s125_ty4_cached_macro_type`). TY-3 and
  TY-5 were already GREEN and stay so.
- **One cell fails that passed:**
  `generated_definition_persistence::s125_ps3_inline_module_no_ghost_restore`.
  Its new precondition held (the trace reports `cache hit (.meta valid)`
  for `m` and `m.nested`), and the restart evaluated `(m/unsaved)` to 42:
  ACT-1102's face, which appears when the cache is written ahead of the
  file and not otherwise. It is W7's, not W6's.
- 157 − 17 + 1 = 141.

### 16.2 The workspace `cargo fmt`

`dev` reformatted 29 files under `tests/` and `src/result_owner.rs`.
`rustfmt` rewrites layout only and does not alter string literals, so the
Cranelisp programs the cells hold are unchanged; across all of `tests/` a
whitespace-insensitive diff differs from the plain diff by five lines, and
the run above shows no cell outside W6's scope changing outcome except the
run-dependent 1102 face. No semantic change in `tests/` is found.

### 16.3 Review finding: `/type` errors lose the expansion's anchoring

`review` (Codex `b9b7d7b3`): `src/process_form/type_query.rs` returns
build and typecheck errors without the re-anchoring an evaluated turn
applies, so `/type (bad)` reports `parse error at 1000024..1000024` where
evaluating `(bad)` reports `0..5` with its expansion context (REPL spec
§5.1, §5.3; one path for two modes).

Evidence, both in the correcting change-set:

- **`dev`, a unit row at the `/type` seam,** RED first: a build error and a
  type error raised inside a macro's expansion come back re-anchored to the
  written call, as the evaluated path's re-anchoring produces.
- **`test`, T-TY-LOC, an e2e pair (REPL):**
  - *parse face:* `(defmacro bad [] \`(if true))`, then `/type (bad)` and
    `(bad)` in the same session;
  - *type face:* a macro expanding to `(primitives/add-i64 true 1)`, the
    same two inputs;
  - each asserts that `/type`'s diagnostic carries the location the
    evaluation reports for the same input and no offset of 1000000 or
    more. Expected RED now on `/type`'s line.
  - Wrong implementation rejected: a `/type` path that formats errors on
    its own (Principle 11), or re-anchors only one of the two error kinds.
  - Class: acceptance (REPL §5.1). `// defect:` class `error-swallow` is
    not right; use `display-envelope-mirror` (two paths presenting one
    diagnostic diverge), locus `src/process_form/type_query.rs`.

### 16.4 Go

**W6 closes when T-TY-LOC and `dev`'s row pass with the correction and
`review`'s re-check of it is clean.** That needs no further `qa` run beyond
the focused cells. **Go for W7** (persistence: 1068, 1101, 1005, 1102 and
the §9.6.1 refusal) after it.

## 17. W7 adequacy (persistence: 1068, 1101, 1005, 1102; §9.6.1)

**Not yet adequate.** The four band defects' cells pass, but `review`
(Codex `0ba03b4b`) found two blocking and two required defects in the
delivered behaviour (§17.4). W7 closes when §17.5's evidence passes.

### 17.1 The full run

`cargo nextest run --no-fail-fast` by `qa` on the W7 tree: **8,306 run,
8,187 passed, 119 failed, 1 skipped, 230 s.** Against §16.1's set (141),
by name:

- **24 cells pass that failed:** the six 1005 cells (`s124_1005_a_begin`,
  `a_macro` as re-baselined, `b_kinds`, `b_names`, `b_redefine`,
  `c_structural_order`); the four 1068 cells; the three 1101
  `s124_save_after_*` cells; 1102's `s124_refused_save_cached_restart_survives_call_and_next_turn`
  and both PS-3 cells; and the eight §9.6.1 refusals (`s125_q51_*_neg`,
  `s125_q52_arguments_neg`, `s125_q52_other_macro_neg`).
- **Two cells fail that passed** (§17.2, §17.3).
- 141 − 24 + 2 = 119.

### 17.2 `s124_refused_save_cold_restart_refuses_unsaved_function_control`

Its seed refuses a save through 1101's construction, which W7 corrected,
so the control's premise is the old defect. **`test` re-seeds it** through
a refusal that still exists, the inline-`mod` guard of the PS-3 cells,
keeping its clauses: a cold restart reports `undefined variable: f` and
not its value.

### 17.3 `constrained_clause_nonoverlapping_arity_dispatches_two_instantiations` (`repl_cached` leg): a pre-existing typecheck defect, newly exposed

- **Reproduced, single signature.** With the test-standard prelude, a
  session that enters `(defn g [:a x] (+ x x))` and
  `(defn main [] (primitives/pure (g 3)))` writes them to `user.cl`; the
  cached restart refuses `cannot redefine user/g; old language type: (Fn
  [:prelude/Num a] a); proposed language type: (Fn [primitives/Int]
  primitives/Int)` and locks the session. `--no-cache` restarts cleanly.
- **Pre-existing.** The opening tree's binary (`4c844f62`, built in a
  scratch copy) refuses the same restart in the same words. The cell's
  multi-signature leg passed before only because 1068 dropped the family
  from the saved file.
- **Mechanism, observed: a file cluster narrows a constrained written
  variable.** Loaded fresh from that file (`--no-cache`), `g` displays
  `(Fn [primitives/Int] primitives/Int)` and `(g 1.5)` is a type error.
  Control: the same file without `main`'s use displays
  `(Fn [:prelude/Num a] a)`. Entered turn by turn, `g` keeps its constrained
  scheme. The restart's redefinition gate compares two genuinely different
  schemes: the restored (turn-checked) one and the file-checked one; its
  comparand is right.
- **Attribution:** typecheck's checking of one cluster, which generalises
  `g` only after `main`'s use has fixed `a`, contrary to spec §3.3.2 (a
  constrained written variable at a quantified position stays abstract)
  and §5.13.1. Class `wrong-reject`; provisional locus
  `crates/cranelisp-typecheck` cluster generalisation. *Refuted if* the
  file check yields the constrained scheme and the restart still refuses.
- **Disposition:** not a W7 regression and not `src/`. **`test` adds
  T-NARROW**, the narrow repro: a file holding `g` and an `Int` use, where
  `(g 1.5)` must evaluate to `3.0` at the REPL and under `--run`; the
  control is the file without the use. It is carried to the typecheck
  focus sprint on its cells, with the constrained-clause cell's cached leg.
  This is the record of a defect newly reached, not decay of `src/`.

### 17.4 The cache-restored-records gap

A cache-restored module has no authored records until its first
regeneration, so a redefinition there would append rather than keep its
position, and a generated definition there would not be refused (repl
§15.4 rule 2; spec §9.6.1). **Not reachable through user commands:** the
entry module recompiles from source at startup, and `/mod` rebuilds a
module before a definition can be entered into it (`review`'s probe; the
design's §4.5). Named residual, asserted with a falsifier: a REPL turn that
defines into a cache-restored module with no rebuild in between.

### 17.5 Review findings and the evidence for them

*Superseded by §18 under the authored-entry rulings of 2026-11-27.*

All four are fixed in S125. One `test` dispatch, then `design`(int) for
R2 and R4, then one `dev`(`src/`) dispatch with a unit row each, RED first.

| Id | Finding | `test` cell (REPL unless stated) | `dev` unit row | Design first? |
|---|---|---|---|---|
| R1 | **Data loss.** `(defmacro make [n] \`(defn ~n [] 10))`, `(begin (make f) (defn a [] 1))`, `(defn a [] 20)`: the saved file holds `(defn a [] 20)` and the whole original `begin`; the restart refuses the duplicate `a` and locks | The three turns, then the saved file holds `(make f)` once and `(defn a [] 20)` once; cold and cached restarts give `(a)` 20 and `(f)` 10 with no lock. Class `partial-record-update`, locus `src/save.rs` | `member_entry_keys` ties a macro-call member of a `begin` to the keys its expansion generated | No: binary clean §4.2 already says each surviving member is emitted alone at the shared position |
| R2 | **§9.6.1 bypass.** `(defmacro maker [] (quote (defmacro g [] (quote 10))))`, `(maker)`, `(defmacro g [] (quote 20))` is accepted, `(g)` is 20 and regeneration drops `(maker)`: macro checkpoints publish before the refusal runs | The three turns: the third is refused, located at it; `(g)` stays 10; the saved file keeps `(maker)` and holds no written `g`. Also a `defmacro` generated by the file's macro call, redefined at the REPL. Class `release-path-bypass` is wrong; use `partial-record-update` (the refusal's record and the checkpoint's publication disagree), locus `src/process_form.rs` | The refusal reads a checkpoint-published macro's origin | **Yes:** the design's refusal site (`finalize_cluster`) runs after checkpoints publish; `design`(int) states where a checkpoint applies the refusal |
| R3 | **Order.** `(begin (defn z [] 1) (defn a [] 2) (defn m [] 3))`, then redefining `a`, saves `a, m, z`: members share one position and tie-break by name (repl §15.4 rule 2) | The saved file lists `z`, `a`, `m`. Class `authored-order-loss`, locus `src/save.rs` | Members of one shared form order by member index | No |
| R4 | **Import order** (pre-existing, retained). Imports entered as `aa/a`, `bb/b`, `aa/c` save as `(import [aa [a c] bb [b]])`; platforms save alphabetically (repl §15.4 rule 4: within each section, authorship order) | The three import turns: the saved file holds three import forms in entered order. Two platforms entered `test-capture` then `stdio` (workspace platforms): saved in that order. Class `authored-order-loss`, locus `src/save.rs` | The import and platform sections read the authored forms in order | **Yes:** the authored form is not on `cranelisp-types`'s `ImportSpec`. `design`(int) prefers the binary's own authored-form record (§4.2), which needs no public change; if it needs `ImportSpec`, it goes to `arch` first, and if that is not bounded this sprint the RED carries with the user's decision |

**Also in the `test` dispatch:** §17.2's re-seed and §17.3's T-NARROW.

**Completion:** R1–R4 RED on their clauses before `dev`; GREEN after it,
with each unit row seen RED first; a `qa` full run whose only differences
from §17.1 are those cells, §17.2's re-seed and T-NARROW (RED, carried);
and `review`'s focused re-check of the correction.

## 18. W7 correction: the settled delta for `test` (authored-entry model)

Supersedes §17.5's table. **Authority:** S125-Q7, Q8 and Q9 (user,
2026-11-27; appendix D); spec §9.6 and §9.6.1; repl §15.4, §15.6 and §18;
[binary clean](../../design/int/s125-binary-clean.md) §4.2 (the entry
model), §4.4 (*A re-entry that drops a definition*) and §4.6 (R2, R4).

- **The model.** A written form or a macro call owns each definition. A
  REPL `begin` dissolves into its members. A multi-module `import`
  contributes one entry per module spec. Regeneration writes each entry
  once, in authored order, and never writes a top-level `begin`.
- R1 and R3 now hold by construction (the split path is deleted); their
  cells stand. R4's one-form-per-spec output is the rule, not a residual.

One `test` dispatch, then one `dev`(`src/`) dispatch; no `design` step is
left.

### 18.1 Cells: as written, extended, re-baselined, new

Every cell is REPL unless stated; a defect cell carries its `// defect:`
line.

| Row | Cell | Action | Assertions | Expected now |
|---|---|---|---|---|
| R1 | `repl_persist::s125_w7_r1_begin_macro_member_survives_redefinition_and_restarts` | Extend | As written, plus: the saved file holds no `(begin` | RED |
| R2 | `repl_persist::s125_w7_r2_generated_macro_turn_redefinition_refused`, `…_file_redefinition_refused` | Extend | As written (refused and located; `(g)` stays 10; `(maker)` kept, no written `g`), plus two legs: a re-entered `(maker)` is accepted; `(begin (defmacro h [] (quote 1)) (defmacro g [] (quote 20)))` after `(maker)` refuses `g` and leaves `h` live | RED |
| R3 | `repl_persist::s125_w7_r3_begin_member_redefinition_keeps_order` | Extend | As written (`z`, `a`, `m`), plus no `(begin` | RED |
| R4 | `repl_persist::s125_w7_r4_import_turns_keep_order_and_forms`, `…_platform_turns_keep_order` | Extend | As written, plus three legs: one turn `(import [aa [a] bb [b]])` saves as `(import [aa [a]])` then `(import [bb [b]])`; an import kept by a later save is written once; save, restart and save again give a byte-identical file | RED |
| Q7 | `repl_persist::persist_repl_begin_spanning_sections_written_once` | Re-baseline | The `deftype` and the `impl` are each written once, no `(begin`; the cold restart holds | RED |
| Q8 | `repl_persist::persist_file_loaded_begin_spanning_sections_written_once` | Re-baseline as the §9.6 leniency cell | A legacy backing file holding the spanning `begin` loads; the next save writes the `deftype` and the `impl` once each, no `(begin`; the cold restart holds. `// spec: spec/09-macros.md §9.6` (the SHOULD leniency) and repl §15.4. If the file refusal is ever built, this becomes its cell | RED |
| Q7 | `repl_persist::s124_1005_a_begin` | Extend | As written (restart gives `f` 1 and `g` 20, no errors), plus: the saved file holds `(defn f [] 1)` before `(defn g [] 20)` and no `(begin` | RED |
| Q9 | **T-Q9**, new, in `tests/generated_definition_persistence.rs` | New | `(defmacro two [] '(begin (defn p [] 1) (defn q [] 2)))`, `(two)`, then `two` redefined to emit only `p`, then `(two)`: refused, naming `q`; `(q)` still 2; `(p)` 1; the saved file unchanged by the refused turn (byte-identical before and after). Controls: re-entry after a redefinition that emits `p`, `q` and a new `r` is accepted and `(r)` works; re-entry with `two` unchanged is accepted. `// spec: spec/09-macros.md §9.6.1`; class `silent-accept`, locus `src/process_form.rs` | RED |

**Wrong implementations rejected.** R1, R3, Q7: a writer that re-emits the
typed `begin`, or emits a member twice. R2: a refusal applied at the
cluster only, which a checkpoint passes. R4: a writer that merges by
module, sorts, or loses the fixed point. Q8: a load that refuses the
legacy file, or a save that writes the `begin` back. Q9: a re-entry that
leaves `q` live with no recorded owner, or replaces silently.

**Not changed by the model** (`qa` confirmed the design's sweep): no cell
in `tests/cache.rs`, `tests/repl_lifecycle_matrix.rs`,
`tests/repl_redefinition.rs`, `tests/spec_09_macros.rs` or the rest of
`tests/repl_persist.rs` asserts a saved `(begin` text. `s124_1005_a_macro`,
§17.2's re-seeded control and T-NARROW stand as delivered.

### 18.2 `dev`(`src/`) unit rows

The design's list (§4.2 rows 1–6, §4.6 R2's three rows, R4's three rows),
each observed RED first, and the `src/` tests the design names
(`regen_literal_begin_multi_defn_emits_once`,
`regen_repl_begin_spanning_sections_emits_once`,
`rehydrate_fills_private_heads_and_begin_members_with_outer_form`,
`regen_macro_expansion_artifact_emits_authored_origin_once`,
`an_unsplit_begin_is_written_once_as_authored`,
`a_begin_split_by_redefinition_writes_each_survivor_alone`) rewritten to the
entry model.

### 18.3 Annotations

Set now: the session-persistence chapter's §15.4 (rules 1, 2 and 4 to
their passing cells; the entry model RED on the R cells) and §15.6, and the
redefinition chapter's §18, both pointing at the language §9.6.1 band;
and that band itself (the passing refusals; R2 and T-Q9 RED).

### 18.4 Completion

- `test`: every row above observed RED on its clause (T-Q9's controls
  GREEN), with the clause map, before `dev` starts.
- `dev`: the rows GREEN, each unit row seen RED first.
- `qa`: a full run whose only differences from §17.1 are these cells,
  §17.2's re-seed and T-NARROW (RED, carried); then `review`'s focused
  re-check.

## 19. W7 correction adequacy

**Not yet adequate: one blocking re-review finding, R5 (§19.4), is fixed
this sprint.** Everything §18 allocated passes.

### 19.1 The full run

`cargo nextest run --no-fail-fast` by `qa` on the corrected tree: **8,330
run, 8,210 passed, 120 failed, 1 skipped, 232 s.** Against §17.1's set
(119), by name:

- **Added:** the two T-NARROW subjects,
  `constrained_file_cluster_narrowing::s125_t_narrow_file_int_use_preserves_float_{repl,run}`
  — the carried typecheck defect of §17.3. Their controls pass.
- **Removed:** `repl_persist::s124_refused_save_cold_restart_refuses_unsaved_function_control`,
  re-seeded per §17.2.
- 119 + 2 − 1 = 120. Nothing else differs.

### 19.2 Re-reads

All pass in the run: R1, both R2 cells, R3, both R4 cells, both
re-baselined spanning-`begin` cells (the REPL one and the §9.6-leniency
file one), `s124_1005_a_begin`, T-Q9's subject
(`s125_q9_shrinking_reentry_refused_without_changing_live_definitions_or_file`)
and its two controls. `test` observed each R and re-baseline cell RED on
its clause before `dev`.

- **`s124_1005_a_begin` was predicted RED and was GREEN before `dev`.**
  The prediction was wrong: W7's first build already wrote the survivors
  of a split `begin` alone, so its saved file had no `(begin` and `f` came
  before `g`. Its added clauses therefore carry no red-first evidence of
  their own. The discriminating cell for dissolution of an unsplit REPL
  `begin` is the re-baselined `persist_repl_begin_spanning_sections_written_once`,
  which was RED first.

### 19.3 The resumed-expansion residual (binary clean §4.5)

A continuation resumed after a dependency gap inside a macro call's
expansion is said to record its products as `Written`.

- **Probe, one shape, not reproduced:** `m` defines
  `(mk)` → `(begin (defn a [] 1) (n/gen))`, with `n` unloaded; the
  scheduler trace shows `n` registered during the `(mk)` turn. A later
  `(defn f [] 20)` is refused as macro-generated, `(f)` stays 10, and the
  saved file holds `(mk)` once.
- **Disposition:** asserted with the design's falsifier, no cell: a
  generated definition that, after a mid-expansion gap, is accepted for
  redefinition by a written form. It predates the change.

### 19.4 R5: a macro call over a written definition is saved twice

`review` (Codex `d951e6ca`): `(defn p [] 0)`, `(defmacro two [] '(begin
(defn p [] 1) (defn q [] 2)))`, `(two)`. Live, both work; the saved file
holds `(two)` twice, and a cold restart refuses the duplicate `p` and locks
the session. Control: without the first `(defn p [] 0)`, the call is saved
once and both survive the restart.

- **Classification:** data loss at restart; class `partial-record-update`
  (one call's entry is split across two positions: `p` keeps its earlier
  written position, `q` takes the call's, and the writer writes one call
  per position); locus `src/session_v4/types.rs::install_authored`.
- **Expected semantics:** the macro call becomes the single owning entry of
  every key it generates, at the call's own position, and the written `p`
  entry it replaced is retired (repl §15.4: each definition has one owning
  entry, written once). This is the only placement that is always safe:
  placing the call at `p`'s earlier position would put it before
  `(defmacro two …)` in this transcript, which a restart could not expand.
  No `spec` question is needed: §15.4's in-place replacement applies to
  an entry replaced by the same entry, and here a different entry takes
  the key over.
- **`test`, one cell** in `tests/repl_persist.rs`, RED now: the three
  turns, then the saved file holds `(two)` exactly once, no
  `(defn p [] 0)`, and `(defmacro two` before `(two)`; cold and cached
  restarts give `(p)` 1 and `(q)` 2 with no lock. Control (GREEN): the
  same without the first `(defn p [] 0)`. A second leg: `(defmacro two …)`
  first, then `(defn p [] 0)`, then `(two)`, with the same assertions, so
  the call's position cannot be passed by placing it at `p`'s.
- **`dev`, a unit row** RED first: when a macro-call entry generates a key
  that a written entry owns, every key of the call takes the call's
  position and the written entry is retired; the writer then writes the
  call once.

### 19.5 Go

W7 closes on R5's cell and row passing, a `qa` full run whose only
difference from §19.1 is that cell, and `review`'s re-check of R5. **Go
for W8 then.**

## 20. W7 close

`cargo nextest run --no-fail-fast` by `qa` after R5's fix: **8,334 run,
8,214 passed, 120 failed, 1 skipped, 237 s.** The failing set is §19.1's,
name for name. The four added cells are R5's: both subjects
(`s125_w7_r5_macro_call_replaces_written_definition_once_and_restarts`,
`s125_w7_r5_macro_before_written_definition_saved_once_and_restarts`), the
control and `dev`'s unit row; all pass. R5's subjects were RED on their
clauses before the fix (`test`'s record) and were added after §19.1's run,
so they appear in neither set. `review`'s scoped re-check (Codex
`0dd26387`) is clean.

**W7 is adequate and closed.** 1068, 1101, 1005 and 1102 are corrected
with the §9.6.1 refusal, the authored-entry model of S125-Q7–Q9, and R1–R5.
Carried from it: T-NARROW (§17.3, typecheck); the cache-restored-records
gap (§17.4) and the resumed-expansion residual (§19.3), both named
residuals. **Go for W8** (module loading and search: 1079, 1092, 1096,
1100; ACT-0994, ACT-1085), against §5.5–§5.6 and §6's rows.

## 21. W8 adequacy (module loading and search: 1079, 1092, 1096, 1100; ACT-0994, ACT-1085)

**Not yet adequate: two required review findings in 1092's private
indexing are fixed this sprint (§21.4).** Everything else W8 owes passes.

### 21.1 The full run

`cargo nextest run --no-fail-fast` by `qa` on the W8 tree: **8,360 run,
8,268 passed, 92 failed, 1 skipped, 239 s.** Against §20's set (120), by
name:

- **29 cells pass that failed:** 12 in `spec_08_modules` (the six
  `s124_1079_{a,b}_subject_*` cells, REPRO-1079-c's pair and the four
  `s124_declared_child_*` cells), 8 in `search` (the five
  `s124_child_index_*` subjects, both `s124_search_reach_*` cells and
  `s125_1092_unloaded_macro_import_keeps_ordinary_definitions`), 8 in
  `spec_09_macros` (the six `s124_macro_sibling_outer*` cells,
  `s125_1100_expand_parity_preserves_user_argument` and
  `s125_1100_selective_derive_stdlib_conformance`), and T-OWNER.
- **One cell fails that passed:** `spec_08_modules::stdlib_module_compiles_and_runs`
  (§21.2 (a)).
- 120 − 29 + 1 = 92.

### 21.2 Classifications

- **(a) `stdlib_module_compiles_and_runs`: the cell asserts the superseded
  rule.** A project-root `main.cl` declares `(mod helper)`; the child
  exists only under the library directory, beside no declaring file. Spec §8.2.5 (S124-Q14) resolves
  a declared child only beside its declaring file, so the refusal is
  correct and binary clean §5.1 predicted it. **`test` re-baselines it** to
  the refusal (located, naming the expected `main/helper.cl`), and adds
  the positive §8.11.2 twin the cell was meant to show: a root module
  `helper` present only in the library, imported as
  `(import [helper [compute]])`, resolves and exits 55.
- **(b) T-OWNER's one failure: a fixture race, provisional.** The owner
  session loads `user.cl` (`(defn sentinel [] 0)`) at startup, and its
  object pass writes `user.o`, `user.meta.json` and the manifest
  asynchronously after the prompt. The contender's before and after
  snapshots cover the whole cache directory, so a late owner write between
  them reads as the contender mutating the cache. *Refuted if* a failing
  run's changed-file list names `app` or `lib` artefacts. **`test`
  repairs the clause:** take the before snapshot only after the owner's
  own cache entries have settled (its `user` object and manifest entry
  present and stable), and report the changed names on failure. The
  product's exclusion is not implicated.
- **(c) 1092's `.meta` branch not built:** a departure, not a defect.
  repl §17.19 R10 is met by indexing an unloaded dependency from source; a
  dependency needing expansion leaves its dependents unindexable, which is
  ACT-0952's carried completion.
- **(d) A contender's private cache directory left on an exit that skips
  `shutdown`:** a named residual of low harm (a stale directory under the
  system temporary directory; no project file is touched). No cell.
- **(e) ACT-0994's row (1) reaches its window only in the shape `dev`
  built** (the fresh registration terminal before the stale completion).
  That row is the designed module evidence (int §7.1) and was RED first;
  the window cannot be held from a process, as recorded in the S124 delta.
  Accepted.
- **(f) Stale loci of the deleted `enumerate_cl_modules_excluding`:** in
  `qa`'s S124 delta, repaired. In `tests/search.rs`'s two `// defect:`
  lines the locus stays (the notation keeps the historical seam);
  `test` adds the prose after the token naming
  `pipeline::module_file_target` as what to read today.

### 21.3 Filings

- **ACT-0994: closed and deleted.** Its two rules are built and its module
  rows pass, red first; no live document links it.
- **ACT-1085: kept until (b)'s repair lands and T-OWNER passes on it.**
  The owner lock and its rows are built; the mixed-generation falsifier
  stays a named residual.

### 21.4 Review findings (Codex `f6d26472`) and their evidence

| Id | Finding | Evidence |
|---|---|---|
| F1 | **A dependency publishing between the index's table snapshot and its scheduler check** is read as `Ready` with an empty or partial private table; import installation fails, the dependent is marked indexed with no rows, and no deferral exists for the publication hook to recover it (repl §17.19 R10). Source-confirmed, not reproduced | **`dev`, a unit row with an injected publication** between the snapshot and the check (a test hook at that seam), RED first: the dependent stays pending and is indexed once the dependency's publication hook runs. No e2e cell: no process can hold the window. Class `lost-wakeup`, locus `src/session_v4/index_worker.rs`. The cure is the read order of §6.1's 1090 design (read publication before the tables), which `design`(int) need not restate |
| F2 | **The index loads the target of an empty import:** `(import [does-not-exist []])` and `(defn null-marker [x] x)`; `/search marker` omits the module and logs `module 'does-not-exist' not found`. Spec §8.3.7: an empty import loads and resolves nothing | **`test`, one e2e cell, RED now:** that module, then `/search marker` lists `null-marker` and the output names no missing module. Control: the same module with an import of an existing module also lists it. Class `enumeration-miss`, locus `src/session_v4/index_worker.rs`. **`dev`, a unit row:** the private provider skips a spec that `imports::names_load` says does not load |

### 21.5 Go

W8 closes on F1's row and F2's cell and row passing, §21.2's
`test` repairs ((a), (b), (f)), a `qa` full run whose differences from
§21.1 are those cells, and `review`'s re-check of F1 and F2. **Go for W9**
(`src/` remainder: 1003, T-0979, ACT-0965 item 3, the `src/platform.rs`
citation, the misnamed agent test) then.

## 22. W8 close

`cargo nextest run --no-fail-fast` by `qa` after W8's corrections (`dev`;
`test`, Codex `f01c7677`): **8,366 run, 8,275 passed, 91 failed, 1
skipped, 227 s.** The failing set is §21.1's less exactly one cell,
`spec_08_modules::stdlib_module_compiles_and_runs`, now the §8.2.5 refusal
with its root-module positive twin. Nothing else differs by name.

- **F2:** `search::s125_empty_import_search_missing_module_keeps_definition`
  and its control pass, with `dev`'s row
  `index_worker::tests::an_empty_import_of_a_missing_module_is_not_provided`.
- **F1:** `dev`'s injected-publication row passes; publication is read
  under one lock before the snapshot. `review`'s re-check (Codex
  `d3da89e6`) is clean for both.
- **T-OWNER** and its uncontended control pass on the settled fixture, with
  the owner row `a_second_session_on_an_owned_project_uses_a_private_cache`.
- **ACT-1085: closed.** The lock and its evidence are in; the two-process
  mixed-generation falsifier and §21.2 (d)'s left-behind private directory
  stay named residuals. `qa`'s own links are removed; the file is deleted
  once `design/int/int.md` (line 4323) drops its link.

**W8 is adequate and closed. Go for W9** (`src/` remainder: 1003 (T-1003),
T-0979, ACT-0965 item 3, the `src/platform.rs` citation, the misnamed agent
test).

## 23. W9 adequacy (`src/` remainder)

**Adequate once `dev`'s unit-evidence repair (§23.2 (3)) lands.** `review`
(Codex `4e9cbc53`) found no correctness defect in T-1003, T-0979, the
citation, the rename or ACT-1060's deletion.

### 23.1 The full run

`cargo nextest run --no-fail-fast` by `qa` on the W9 tree: **8,377 run,
8,294 passed, 83 failed, 1 skipped, 271 s.** Against §22's set (91), by
name: **eight cells pass, none newly fails** — the six T-0979 subjects
(`platform_function_types::s125_0979_{fnparam,fnresult,fnfield}_neg_{run,repl}`;
their two ordinary-signature controls were already GREEN) and both T-1003
cells (`repl_introspection::s125_1003_{forward,reverse}_lists_constructors`;
the `Qother` control was already GREEN). 91 − 8 = 83.

Read against the settling target, the 83 hold **no cell attributed to
`src/` other than the two named exceptions**, `trace::s124_1087_subject_run_first_launch`
and `trace::s124_1090_mixed_restore_subject`. The rest are typecheck's
(1071, 1073–1076, 1080, 1082, 1097, 1103, 1104, T-0985, T-NARROW), intrinsics' (0977), the backend cache schema's (T-1036),
unattributed (1018, 1067), and two maintenance checks (the document gate's
ignored-path findings and the public-API baselines, regenerated at the
checkpoint). WG confirms this on a fresh build.

### 23.2 Leads and review items

- **(1) ACT-0965 item 3's remainder: an accepted residual, no action.**
  The item's subject was two routes wiring host externs with no parity
  guard. One `host_extern_addresses` map now feeds the JIT and the linker,
  so the routes cannot diverge: that is structural, and closes the item.
  What was not built is a named error on a miss. Today a host-promised
  extern absent from the map is skipped on both routes alike; distinguishing
  a true miss from a backend-inlined combinator needs the backend's private
  `HostPromisedLowering::of_symbol`. A miss arises only when the compiler
  binary fails to export a symbol (a build configuration fault: the
  repository's `--export-dynamic` link flag), not from any user program.
  *Falsifier:* a host-promised extern missing from the map reaches
  execution, observable as a call through an unfilled slot (`null-got-slot`)
  in any mode. `design`(int) records the residual in its design; exposing
  the classification goes to `arch` only if the named error is scheduled.
- **(2) `tests/plan/s124-evidence-delta.md:838`'s link to ACT-1060:**
  repaired by `qa`.
- **(3) The address-parity unit row can pass vacuously.**
  `src/worker/tests.rs` compares the map's `sconcat` address with
  `dlsym_host_symbol("sconcat")`; if the export disappears both are `None`
  and the row passes. `dev` requires a non-null expected address, so the
  row fails when the export is missing. This is the item-3 structure's
  one module witness, so it is required before W9 closes.
- **(4) `load_cached_module_via_linker` at 199 lines:** `design`(int)'s,
  under int §12.1 item 21 (decompose or record an exception when opened).
  Not an evidence matter.

### 23.3 Go

W9 closes on (3)'s repair and its focused re-check. That ends the focus
band's language work. **Go for WG**, the integrated gate: a fresh build of
the final tree, `qa`'s full run, `src/` clean and green less 1087 and 1090,
no `src/` build warning, and `arch`'s comparison of the regenerated
public-API baselines with rows IO-T and D-1.

## 24. WG: the integrated gate (2026-11-27)

**Verdict: the suite and build clauses of the settling target hold.** Three
filing dispositions are not yet recorded (§24.5); they are the checkpoint's
open items.

### 24.1 Build and run

- **Tree:** `main` at `4c844f62` with the sprint's uncommitted work, after
  `arch`'s baseline regeneration.
- **Fresh build:** every workspace package cleaned (`cargo clean -p` for all
  eighteen, 83.8 GiB) and the `function-types` dylibs removed, then
  `cargo build`, `tests/scripts/build-link-prereqs.sh` and
  `cargo nextest run --no-run`. **No workspace crate raises a warning**,
  `src/` and its test targets included. The only warning is the
  future-incompatibility note for the external `nix` 0.28.
- **Run:** `cargo nextest run --no-fail-fast`, once: **8,381 run, 8,299
  passed, 82 failed, 1 skipped, 273 s.**

### 24.2 The failing set

Against the W9 close's set (83, identical by name in §23.1's run and the
8,381-test re-run after the parity repair): **one cell passes that failed,
none newly fails.** The cell is
`public_api_relocations::public_api_check_runs_against_every_baselined_crate`,
green on `arch`'s regenerated types baseline. 83 − 1 = 82.

### 24.3 Attribution

| Module | Failing | Defects (cells) |
|---|---|---|
| `src/` | 2 | 1087 (`trace::s124_1087_subject_run_first_launch`), 1090 (`trace::s124_1090_mixed_restore_subject`): the named exceptions |
| typecheck | 68 | 1076 (15), 1075 (9, three under the closed 1065 name), 1071 (7), 1074 (6), 1103 (6), T-0985 (6), 1080 (4), 1082 (4), 1097 (3), 1104 (3), T-NARROW (3), 1073 (2) |
| intrinsics | 3 | 0977 |
| backend | 1 | T-1036 (cache schema; provisional, §6) |
| Not attributed to a module | 7 | 1018 (5: four `s124_print_balance_*`, the Sudoku residue cell), 1067 (2) |
| Maintenance | 1 | The document gate |
| **Total** | **82** | |

- **Matching.** By the identifier in each name or its `// defect:` line;
  every cell traces to a defect of the
  [S124 register](s124-evidence-delta.md#1415-defects-carried-by-failing-tests)
  or to a cell this delta allocated (T-0985, T-1036, T-NARROW).
- **The document gate** reports 514 findings, all of one class
  (`ignored-path`: retained records citing Git-ignored scratch paths). It
  blocks no product claim.
- **One cell's trace line disagrees with its count.**
  `spec_08_modules::s124_declared_child_alias_graph_repl_orders_agree`
  (1082) carries `locus=src/process_form/dependency.rs`, where the refusal
  is raised. It is counted to typecheck, as at the S124 close and in the
  sprint's exclusions: `design`(int) and `arch` (2026-11-19,
  [resolution gaps](../../design/arch/interfaces.md#resolution-gaps)) place
  the fault in typecheck's `resolve_qualified`, whose member-absent gap
  names the alias as written, and rejected `dev`'s `src/`-side substitution
  although it turned the cells green. **The attribution stays provisional.**
  *Refuted if* a build whose gap carries the substituted module still fails
  this cell. `test` aligns the locus token with its three sibling cells
  (`cranelisp-typecheck::resolve_qualified`).

### 24.4 The settling target, clause by clause

| Clause | Reading |
|---|---|
| No failing test attributed to `src/` but 1087 and 1090 | **Holds** (§24.3), on the provisional 1082 attribution |
| No `src/` build warning | **Holds** (§24.1) |
| No open review finding on `src/` | **Holds.** W2, W3+, W5 (`src/`): none. The W3 nit, W6's anchoring finding, W7's R1–R5, W8's F1 and F2 and W9's budget and parity findings are each resolved and re-reviewed. W9's ACT-0965 finding is disposed as a residual (§23.2 (1)), which the user approves or returns |
| Opaque-`IO` rulings | **Holds:** all 76 `opaque_io` cells and both T-PURE-ID cells pass; trace output is deferred with TR-1 |
| Every focus-band and hygiene-band filing disposed after verification | **Three gaps** (§24.5) |
| No decay | **Holds:** no cell fails that passed at the opening (§1); the typecheck count rose from 61 to 68 by new reproductions of older defects (T-0985 +6, T-NARROW +3) less 1107 (−2) |

Residuals named in `src/` this sprint, for the user's approval at the
checkpoint: the cache-restored-records gap (§17.4), the resumed-expansion
residual (§19.3), a contender's private cache directory left on a skipped
shutdown (§21.2 (d)), the two-process mixed-generation falsifier (§22),
1092's unbuilt `.meta` branch (ACT-0952), and the unnamed host-extern miss
(§23.2 (1)).

### 24.5 Filings

**Disposed, deletion ready** (`qa`'s; their cells pass in §24.1's run and
`qa`'s own links are removed): ACT-1004, ACT-1015, ACT-1085.

**Disposed, deletion waits on another owner's link:**

| Filing | Disposition | Waits on |
|---|---|---|
| ACT-0979 | T-0979 passes (8 cells) | `arch`: `design/arch/symbol-table-lifecycle.md:131` |
| ACT-1081 | T-1081 passes | `design`(int): `design/int/int.md:1682`; `spec`: `spec/appendix-d-open-questions.md:416` |
| ACT-1022 | Closed, stale (§2.1) | `audit`: `audits/cranelisp-backend-s122.md:38` |
| ACT-1036 | Carried by `spec_09_macros::s125_1036_cached_written_location` | Nothing; its `refers_to` names FIXME 0915, which stays |
| ACT-1003 | T-1003 passes | Nothing |
| FIXME 0761 | T-0761 passes | Nothing |
| FIXME 0785 | T-0785 passes | `audit`: `audits/cranelisp-frontend-s123.md:331` |
| FIXME 0929 | T-NC2 (`concrete_boundary_census`, 3 cells) passes with both detection legs; one allow-listed site remains | `arch`: row R18 of `design/arch/safety-invariants.md` still reads `unasserted` and "once landed"; the filing's closure is that row recording the census |

**Kept, with reasons recorded:** ACT-0962 (carried by the user without a
date), ACT-0985 (S126, typecheck), FIXME 0889 (trigger unmet), FIXME 0939
(`arch`, to Phase 7), ACT-1093 (trace deferral).

**Gaps: no disposition recorded.**

- **Hygiene FIXMEs with other targets: 0050 (`dev`), 0463 (`training`),
  0800 (`dev` on `stdlib/`), 0900 (`test`), 0915 (`design`(backend)), 0933
  (`design`).** Each file is unchanged since the opening and no dispatch
  row, design or plan records a verification. The scope sends each to its
  target role.
- **Two stale source citations** of the hygiene band stand:
  `crates/cranelisp-typecheck/src/traits/impl_check/tests.rs:1592`
  (`typecheck.md §12 T7`, a row now described there as in source) and
  `crates/cranelisp-platform/src/tests.rs:1479` (ACT-0955, no such
  filing). The `checker.rs:960` comment went with W5's deletion of the
  gate it described; `src/platform.rs` was repaired in W9.
- **ACT-0995 and ACT-1009** (focus band, with `spec`): both still read
  "deferred" from S122, with no S125 framing or deferral recorded.
- **FIXME 0863 item 1** (focus band, `qa`'s, owed before this exit, §2.2):
  assessed in part. Witnesses located by name and header: a failed macro
  redefinition keeps the earlier macro
  (`spec_09_macros::failed_macro_redefinition_preserves_prior_generation`,
  body read); retry without replay
  (`s76_macro_availability::generated_macro_checkpoint_is_not_replayed_after_later_dependency_gap_neg`);
  several emitted definitions in order
  (`spec_09_macros::macro_emitted_definition_batch_lists_all_definitions_in_order`,
  `spec_11_stdlib::def_definition_echo_lists_every_emitted_definition_in_order`);
  an earlier checkpoint stands when a later one is refused, and a refused
  checkpoint publishes nothing (`src/` module rows
  `the_generating_call_passes_the_checkpoint_and_earlier_checkpoints_stand`,
  `macro_checkpoint_closing_a_qualified_cycle_is_refused_and_publishes_nothing`).
  **No witness located** for: a failure at each preparation and backend
  boundary leaving no partial update; a shrinking redefinition retiring
  exactly the surplus clause rows; private and zero emitted definitions.
  The filing stays open on those three until `qa` completes the read or
  the user carries it.

### 24.6 Recommendation

The product reading supports the Phase 5 checkpoint: the suite, build and
review clauses hold and nothing regressed. The filing clause does not yet
hold. Before the user is asked to accept Phase 5, `sprint` either
dispatches the six hygiene FIXMEs and two citations to their owners and
`spec` for ACT-0995 and ACT-1009, and `qa` to finish FIXME 0863, or puts
each to the user as an explicit carry.

## 25. WG: the final pass (2026-11-27)

**Verdict: the settling target holds.** §24.5's gaps are each disposed by
their owners (the WG+ rows of the sprint's dispatch log) or below.

### 25.1 FIXME 0863 item 1, assessed

Every listed checkpoint property holds on this tree. `qa` probed the
unwitnessed ones at the REPL and under `--run`, with the primitives-only
prelude, in a scratch directory.

| Property | Witness or observation |
|---|---|
| A failed first definition leaves no partial parent | `spec_09_macros::repl_error_recovery_no_partial_macro` |
| A failed redefinition keeps the earlier macro | `spec_09_macros::failed_macro_redefinition_preserves_prior_generation` (one clause) |
| A successful checkpoint survives a later refusal; a refused one publishes nothing | `src/` rows `the_generating_call_passes_the_checkpoint_and_earlier_checkpoints_stand`, `macro_checkpoint_closing_a_qualified_cycle_is_refused_and_publishes_nothing`, `a_shrinking_re_entry_is_refused_and_publishes_nothing` |
| Retry without duplication or reordering | `s76_macro_availability::generated_macro_checkpoint_is_not_replayed_after_later_dependency_gap_neg` |
| Zero, one and several emitted definitions in order; direct `defmacro` controls | `spec_09_macros::macro_emitted_definition_batch_lists_all_definitions_in_order`, `repl_macro_begin_splicing_defn_then_call`; `s76_macro_availability::macro_generates_defmacro_available_to_later_use`; `spec_11_stdlib::def_definition_echo_lists_every_emitted_definition_in_order` |
| **A shrinking redefinition retires exactly the surplus clauses** | **No cell.** Probe: `m` with clauses of one and two arguments, redefined with one clause: `(m 0)` gives the new value, `(m 0 0)` is refused (`no matching clause … clauses accept 1 argument(s)`), `/info m` shows one clause |
| **A failed multi-clause redefinition changes no clause** | **No cell.** Probe: `k` with two clauses, redefined with three of which the second is ill-typed: both old clauses still answer, and three arguments are refused naming `1 or 2` |
| **Private emitted definitions** | **No cell.** Probe: a macro emitting `defn`, `defn-`, `defn` echoes all three in order and the third calls the private one; from another module the private name is refused (`'priv-b' is not public in 'lib'`) and the public one imports |
| A failure at the backend boundary leaves no partial update | **Named residual, no cell.** No program that passes the checkpoint's typecheck fails its code generation, and no seam injects such a failure. *Falsifier:* a macro whose definition reports a code-generation error and is afterwards invocable, or listed by `/info`, in any mode |

**T-0863, allocated to `test`** (acceptance evidence, spec §9.12.1 and
§9.6 with §8.7; GREEN on arrival; REPL, primitives-only prelude):

- **Shrink.** The probe above. Rejects an implementation that replaces the
  clauses it was given and leaves the surplus row live: assert the
  two-argument call is refused and names one accepted arity.
- **Failed multi-clause redefinition.** The probe above. Rejects a
  per-clause publication that commits the clauses before the ill-typed
  one: assert the one-argument call gives the old value, not the new, and
  the three-argument call is refused.
- **Private emitted definition.** The two-module probe under `--run`, with
  the public import as control. Rejects an expansion path that registers
  every emitted definition as public.

FIXME 0863 is narrowed to T-0863 and re-targeted to `qa`; it is deleted
when the cells pass.

### 25.2 Filings

- **Deleted (`qa`'s, no live link):** ACT-0979, ACT-1003, ACT-1004,
  ACT-1015, ACT-1036, ACT-1081, ACT-1085, FIXME 0761. Recoverable as
  `git show 4c844f62:<path>`.
- **Closed, deletion waits on `audit`'s links** (Phase 6a): ACT-1022
  (`audits/cranelisp-backend-s122.md:38`), FIXME 0785
  (`audits/cranelisp-frontend-s123.md:331`).
- **FIXME 0929:** narrowed to its one site,
  `crates/cranelisp-types/src/mono_expr.rs::lenient_from_expr`, and
  re-targeted to `arch` (types) per row R18. The census's allow-list entry
  already cites it (`tests/scripts/concrete_boundary_check.py`), so no
  `test` edit is owed.
- **Kept:** FIXME 0863 (T-0863), ACT-0962, ACT-0985, FIXME 0889, and the
  other owners' dispositions in the dispatch log (0050, 0463, 0800, 0915,
  0939; ACT-0995 and ACT-1009 as S125-Q10 and Q11).

### 25.3 The full run

Fresh build as §24.1, no workspace warning. `cargo nextest run
--no-fail-fast`: **8,383 run, 8,301 passed, 82 failed, 1 skipped, 261 s.**
The failing set is §24.3's, name for name. The two added tests are
FIXME 0933's unit rows, which pass
(`platform::tests::platform_sig_with_type_variable_is_refused_quoting_the_signature`
among them). §24.3's table stands; `test` has aligned the 1082 cell's
locus token with its count.

### 25.4 Recommendation

**Go for the Phase 5 checkpoint.** For the user there:

- **Residuals to approve, all in `src/`:** the cache-restored-records gap
  (§17.4); the resumed-expansion residual (§19.3); a contender's private
  cache directory left on a skipped shutdown (§21.2 (d)); the two-process
  mixed-generation falsifier (§22); 1092's unbuilt `.meta` branch
  (ACT-0952); the unnamed host-extern miss (§23.2 (1)); the checkpoint
  backend-boundary failure (§25.1).
- **A provisional attribution the target rests on:** 1082's REPL-order
  cell is counted to typecheck (§24.3).
- **Carried:** the two stale source citations (§24.5), to the next work
  in each crate; T-0863, a `test` dispatch in Phase 6 or the next sprint.
- **Rulings owed:** S125-Q10 and S125-Q11.

## 26. Phase 5 checkpoint (2026-11-27)

### 26.1 The public-API baseline guard

`test` renamed the guard cell to
`public_api_relocations::public_api_check_runs_against_every_baselined_crate`;
§15.1 and §24.2 cite it by that name. It now compares eight baselines,
`cranelisp-exe-bundle` added, and fails when a `crates/*/public-api.txt`
exists for a crate its list omits.

- **Class: maintenance check**, as the guard already is. The unlisted-baseline
  leg governs one artifact: the guard's crate list against the committed
  baselines.
- **Wrong outcome it rejects:** a committed baseline that no test compares,
  so the phase-checkpoint diff `arch` reads is silent for that crate. This
  held for `cranelisp-exe-bundle` until this checkpoint.
- **What it gates:** a claim that the baselines are current. It is no
  acceptance evidence for any compiler behaviour.
- **Detection:** `public_api_detection_proof_catches_public_item_and_accepts_clean_surface`
  plants a baseline for a disposable crate, observes the refusal naming it
  with an empty list, and observes the pass once it is listed. Read in
  source; `qa` did not run it under this dispatch.
- **Limit:** a library crate with no committed baseline is not detected.
  *Falsifier:* a workspace library crate under `crates/` with no
  `public-api.txt` while the guard passes.

### 26.2 S125-Q10: a later `(mod q)` after an import of `q`

The user ruled that the later declaration is an ambiguous-import error, and
in S125-Q10-R1 that the refused turn changes nothing and keeps no child
declaration, and that no form addresses a root `q` which a child captures.
`spec` recorded both in `spec/08-modules.md` §8.11.2.1. The source is
unchanged, so the refusal is unimplemented and has no cell. The cell is
written in S126 on ACT-0995, after the design on `src/`.

- **Band:** §8.11.2.1's heading reads `[S126 — partial: Tested+Neg …]`. Its
  cells evidence the precedence rule within one compilation unit, and
  S125-Q10-R1 left that rule's text as it was, so they are restored. The
  refusal paragraph and its unchanged-state paragraph each carry
  `[S126 — unimplemented, no cell (ACT-0995)]`. The no-root-addressing
  sentence has no cell by decision (§27.1).
- **Condition owed in S126** (acceptance evidence, REPL, primitives-only
  prelude). Fixture: a root module `q` whose `g` returns 99 and a child
  module `user.q`, in its own file, whose `g` returns 11. After `(import [q [g]])`, `(defn h [] (g))`, the turn
  `(mod q)`:
  1. is refused with a diagnostic that identifies an ambiguous import;
  2. leaves `(g)` and `(h)` answering 99;
  3. keeps no child declaration: `(q/g)` answers 99, not 11, and a second
     `(mod q)` is refused in the same words;
  4. leaves `user.cl` byte-identical to its content before the turn, with
     no `(mod q)`, and a cold restart answers `(h)` 99 with no lock.

  A second leg repeats 1–4 after `(import [q])`, observing `(q/g)`.
- **Wrong implementations to reject:** accepting the declaration and
  keeping the earlier binding (today's design); accepting it and
  retargeting the import; refusing only the selecting form of the import;
  reporting the refusal after the child is registered, so that `(q/g)`
  answers 11 or the next save writes `(mod q)`.
- **Why clause 3 observes through `(q/g)`:** the precedence rule makes a
  registered child capture bare `q`, so a retained registration changes
  that answer. `record_submodule_on_symbol_table` appends to the live table
  before any refusal could run (ACT-0995), which is the path a late refusal
  would leave behind.
- **Control:** the same `(mod q)` with no earlier import of `q` is
  accepted, `(q/g)` answers 11, and the next save writes `(mod q)`.

### 26.3 Residuals accepted

The user accepted the seven `src/` residuals of §25.4 at the checkpoint.
Each stays a named residual with its falsifier where the cited section
states one:

| | Residual | Stated in |
|---|---|---|
| (a) | The cache-restored-records gap | §17.4 |
| (b) | The resumed-expansion residual | §19.3 |
| (c) | A contender's private cache directory left on a skipped shutdown | §21.2 (d) |
| (d) | The two-process mixed-generation falsifier | §22 |
| (e) | 1092's unbuilt `.meta` branch | ACT-0952 |
| (f) | The unnamed host-extern miss | §23.2 (1) |
| (g) | A checkpoint failure at the backend boundary | §25.1 |

§25.4's "rulings owed" line is met for S125-Q10 by §26.2.

## 27. Phase 6b: the settled delta (2026-11-27)

**Authority:** the user's decisions at the 6a → 6b checkpoint
([sprint plan](../../sprints/archive/sprint-125.md), *Phase 6a outcome*); S125-Q10-R1;
the [intrinsics audit](../../audits/cranelisp-intrinsics-s125.md) F1–F3; the
[exemplar plan](../../exemplar/plan-exemplar.md), whose Phase 6b corrections
section `dev` removed on delivery;
the [examples plan](../../examples/plan-examples.md) §4.7.

**How this section was made.** `qa` ran no test. Band judgments rest on
§25.3's run, whose failing set (§24.3) holds none of the cells restored
below, and on reading each cited cell. §27.3's observations are `qa`'s
probes of the debug compiler binary (built 2026-11-27 13:48, SHA-256
`071dbde496631e36…`, aarch64 Linux) under `--run --no-cache` in a scratch
directory, with no library path.

§27.8 is the one handoff for `test`.

### 27.1 Coverage bands refreshed

| Section | Was | Now |
|---|---|---|
| repl §3.1, `/type` row and both paragraphs | Partial and nonconforming (1089, 1099) | Tested+Neg on the 1089 and 1099 cells, TY-2 to TY-5 and T-TY-LOC (§16) |
| repl §15.1 heading | Partial (1101) | Tested on the five `s124_save_after_*` cells |
| repl §15.2 heading | Partial (1102) | Tested+Neg on the three PS-3 cells and the two `s124_refused_save_*` controls |
| repl §15.4 heading, rules 2, 4 and 6, closing note | Entry model RED; rule 2 nonconforming; rule 4 uncovered | Entry model Tested+Neg (R1, R3, R5, both spanning-`begin` cells); rule 2 Tested+Neg; rule 4 partial; rule 6 gains the cache-leg cell for rule 2 |
| repl §15.6 heading | Pointer, T-Q9 allocated | Tested+Neg on the generated-definition refusals; rule banded at language §9.6.1 |
| repl §17.19 R10 and its two cross-references | Nonconforming (1092) | Partial: Tested+Neg on four `search` cells |
| repl §18 heading | Pointer to §9.6.1 | Adds the pointer to language §8.11.2.1 |
| language §9.6.1 heading | R2 and T-Q9 RED | Tested+Neg, R2, T-Q9 and the reload cells included |
| language §8.11.2.1 | Cleared by `spec` | Heading restored; two S126 rows; one row with no cell |

**Limits kept in the bands, not removed with the defects:**

- **`/type`:** piped REPL input only. The refusal of multi-form input is
  `src/` unit evidence.
- **Rule 4:** no cell asserts that platforms precede `mod`, or that
  definitions follow the four sections.
- **Rule 3** (qualification style) still has no cell.
- **Rule 6:** rules 3 and 4 are unobserved on a cache-restored module. The
  cache-restored-records gap and the resumed-expansion residual stay named
  residuals (§26.3 (a), (b)).
- **§17.19:** the still-compiling clause is module evidence only (§21.4 F1).
  A dependent of an unloaded dependency that needs macro expansion is not
  indexed (ACT-0952, §26.3 (e)).

**§8.11.2.1, the sentence that no form addresses a captured root `q`: no
cell.** It states an absence. Its only observable is the precedence rule,
which the heading's cells evidence in four positions. A cell would have to
pick spellings to show refused, and a refusal of the spellings picked says
nothing of the rest. *Falsifier:* a form that, inside a module whose
declared child captures `q`, reaches root `q`.

**A cell that no longer reaches its subject.**
`repl_persist::s124_refused_save_cached_restart_survives_call_and_next_turn`
seeds its refused save through 1101's construction. W7 corrected 1101, so
the seed now saves `f`, and the cell passes whether or not a cached restart
restores an unsaved definition. §17.2 re-seeded its cold control and missed
this cell. 1102 stays evidenced by the PS-3 cells, which reach a refused
save through the inline-`mod` guard and a failed write. `test` re-seeds the
cell (§27.7).

**Verifiers after the edits:** `spec_coverage_reconcile.py` reports no dead
citation and no cleared row awaiting `qa`; `spec_link_check.py` reports no
mis-cited anchor (§27.12).

### 27.2 S125-Q10-R1

§26.2 now states the full condition: the refusal, the unchanged earlier
calls, no retained child declaration, and an unchanged backing file. The
cell stays in S126 on ACT-0995.

### 27.3 Audit intake: F1, F2, F3

**F1** stays on 0977's three guards. Nothing is allocated.

#### F3: a second force of a launched effect ends the process on a signal

**Reproduced.** Risk: a conforming program dies with no diagnostic.
Spec §10.8.1 makes an `IO` value reusable and requires each force to be
interpreted as the first.

| Program (platform `poll-pool`) | Result, 3 runs each |
|---|---|
| **Subject.** `io` is `(bind (poll-log 7 1 20 "L") (fn [r] (primitives/pure 1)))`, bound by `let` and forced twice: `(bind io (fn [a] (bind io (fn [b] (primitives/pure (add-i64 a b))))))` | Killed by SIGSEGV, empty stdout, 3 of 3 |
| **Control A, fresh per force.** `(defn mk [] …)` returns the same expression; `(mk)` is forced twice | `LL`, exit 2 |
| **Control B, one force.** The `let`-bound `io` forced once, result plus 1 | `L`, exit 2 |
| **Control C, awaited.** As the subject, with the continuation using `r` (`(add-i64 1 (sub-i64 r r))`), so the effect is not launched | `LL`, exit 2 |

- **What the controls separate.** A and B differ from the subject only in
  whether one node is forced twice. C differs only in whether the reused
  step is launched. Only the reused launched step fails.
- **That the step is launched** is read from control A's trampoline trace:
  the inner step's continuation pops with no platform-effect event, and the
  run exits after the 20 ms drain.
- **Mechanism, from source, consistent with the controls and not observed
  at its seam:** `launch_continue` in
  `crates/cranelisp-intrinsics/src/io.rs` reads the node's sub-tree and
  stores zero in its place, and a second force hands that zero to the
  supervisor. The crash site was not captured: the trace is buffered and is
  lost with the process. *Refuted if* a build that leaves the field intact
  still dies on the subject.
- **Where it entered:** the move-out contract of
  [IO trampoline §15.5](../../design/backend/io-trampoline.md) (S96), which
  the reuse ruling of 2026-09-21 superseded. Row R20 of the
  [safety register](../../design/arch/safety-invariants.md) names it as a
  residual with the second force unmeasured.
- **Class:** `consuming-force`, added to the vocabulary in
  `tests/AGENTS.md`. Locus
  `crates/cranelisp-intrinsics/src/io.rs::launch_continue`.
- **Why coverage missed it:** the S122 reuse cells cover `Pure` and
  `Effect`, and the band said so. No cell forced a launched or a poll-shape
  step twice.

**T-F3, for `test`** (acceptance evidence, spec §10.8.1; `--run`; no
prelude; in `tests/spec_10_io.rs` beside the reuse cells):

- The subject asserts stdout `LL` and exit 2. **RED now**, on the signal.
- Controls A, B and C, each **GREEN**. C shows that a sequentially reused
  poll-shape leaf completes and prints on each force. It does not show
  that the second force suspends again; it does not (§28.2).
- Wrong implementations rejected: today's move-out; a guard that makes a
  second force of an emptied node yield `Unit` without running the effect
  (stdout `L`); a refusal of the second force.
- One mode suffices: the force path is the runtime library's in every mode.

**Not allocated: concurrent reuse of a launch node.** Its forces run on
the reactor thread, interleaved and never parallel
([ownership §6.3](../../design/intrinsics/ownership-and-disposal.md)), so
the sequential cell reaches the same write. Reuse of a poll-shape leaf,
sequential and in flight together, is measured and allocated in §28.2.

#### F2: overlapping platform calls restore each other's trap handlers

**Reproduced, and carried on its failing cell (§27.10).** Risk: a hardware trap in platform code ends the process on a
signal, where spec §12.7.6 requires one stderr line naming the platform
function and a non-zero exit that is not a signal.

- **Why no fixture reaches it.** The guard's signal half is entered only by
  a hardware trap in foreign code. Every faulting fixture (`boom`,
  `test-capture`'s `fault-now`) raises a Rust panic, which the platform
  catches on its own side. The signal half has unit evidence only, so
  §12.7.6's e2e band has never observed a trap.
- **The interleaving is order-dependent.** Each force saves the disposition
  it finds and writes it back on return. The trap is unguarded only if a
  force that began with no other force in flight returns while the
  trapping force is inside foreign code. Two branches of one inferred
  parallel group start together, so their install order is not fixed and
  that shape cannot carry a deterministic cell.
- **A shape that fixes the order,** probed with existing effects: in
  `(select [x z])`, branch `x` starts a blocking effect at once and branch
  `z` starts its own after a `sleep`. With `x` a `pool-log` of 300 ms and
  `z` a `sleep` of 100 ms followed by a `pool-log` of 100 ms, stdout is
  `ZX` in 3 of 3 runs. The blocking effects overlap, and `x`'s starts
  alone.
- **A shape that does not overlap,** also probed: a blocking effect in
  launch position runs serially with the continuation (900 ms for 600, 100
  and 200).

**Fixture, approved here under `qa`'s control of test-suite platforms:**
one effect added to `platforms/pool-demo`, `pool-trap : (Int token, Int
capacity, Int ms) -> IO Int`. It sleeps `ms` on the token's pool, then
raises a hardware trap signal on the forcing thread. A Rust panic does not
qualify. `test` extended a fixture platform before (`poll-pool`,
`059f8748`).

**T-F2, for `test`** (acceptance evidence, spec §12.7.6; `--run`; no
prelude; in `tests/platform_errors.rs`):

- **Subject.** `(select [x z])`. `x` is `(pool-read 1 1 800)` whose
  continuation **uses its result**, then waits on a `(poll-read 9 1 5000)`
  so that the branch does not complete: `(bind (pool-read 1 1 800) (fn [r]
  (bind (poll-read 9 1 5000) (fn [q] (primitives/pure (add-i64 r q))))))`.
  `z` is `(sleep 300)` followed by `(pool-trap 2 1 900)`. Assert the
  dispatch-fault contract of `assert_dispatch_fault_surfaced`: one stderr
  line naming `platform.pool-demo/pool-trap` with the fault text, a
  non-zero exit that is not a signal, no language-panic prefix. **RED**,
  by a signal death (5 of 5 in `qa`'s probe).
- **Control.** The same program with `x`'s blocking effect at 50 ms, so it
  returns before `z`'s begins. **Expected GREEN.** It is also the first
  e2e observation that a hardware trap is reported at all.
- **Fixture properties.** `x`'s blocking call is **awaited, not launched**:
  a continuation that ignores the result makes the step launch-eligible,
  and a launched blocking call runs on the reactor thread, so the trapping
  call begins only after it returns (§27.10). `x`'s force begins at least
  300 ms before `z`'s and returns at least 300 ms before the trap. No
  branch completes before the trap, so cancellation plays no part.
- **Wrong implementations rejected by a repair's GREEN:** a per-call save
  and restore of process-global dispositions; a restore that leaves the
  handler installed with no jump context.
- **If the subject is GREEN on arrival,** or the control RED, `test`
  reports to `qa` and does not retune the timings: the prediction or the
  fixture is then wrong, and the attribution is reopened.
- **Class:** `shared-state-write-race`. Locus
  `crates/cranelisp-intrinsics/src/io_guard.rs::force_effect_thunk_protected`.
- **Limit:** a subject delayed more than 300 ms in starting `x` passes
  without a repair. It cannot fail a correct build.

**Lead for `design`, no cell:** the binary's macro-clause guard in
`src/expander.rs` installed and restored the same dispositions around a
clause call. §28.1 settles it; the guard is deleted.

**Repairs are carried** (user, 2026-11-27). Each defect is carried on its
failing cell with no action.

### 27.4 Exemplar

**The 404 page: no `exemplar_web` cell.**

- The defect is one pure function, `html/not-found-page`, which both
  route arms of `main.cl` call. The exemplar's own failing
  `html/test-not-found-page-escapes-path` observes it at that function.
- No wrong implementation passes that test and fails over HTTP: escaping
  at one call site fails the function test, and escaping inside the
  function covers both arms whatever the `web` parser passes through.
- The existing 404 leg of `exemplar_web` requests `/no-such-path`, which
  holds no escaped character, and stays valid.
- The exemplar is a showcase. Its cells are maintenance checks and accept
  no language behaviour.

**`test` reconciles one pin:** `tests.cl` now exits **46** in both modes
(16 grid, 8 solver, 13 html, 9 form), and
`tests/exemplar.rs::s124_exemplar_runner` still asserts 43 for both runner
cells. `dev` added three tests: `html/test-not-found-page-escapes-path`,
`solver/test-equiv-puzzle-needs-search` and `test-parse-cell`. `review`
found nothing else on the exemplar.

**The parallel ≡ serial guard did not cover the search path until now.**
`dev` found that `solver/test-solve-parallel-equiv` pinned a puzzle that
propagation alone solves, so the parallel search never ran under it, and
the two runner cells compared the modes on work neither did.

- **Class:** evidence that passed without discriminating; a coverage
  defect in a maintenance check, not a compiler defect. No runner result
  before this change is evidence about parallel search.
- **Now:** the puzzle is one on which propagation stalls, and
  `test-equiv-puzzle-needs-search` asserts that premise, so a later puzzle
  change that removes the search fails a test.
- **Limit that stands:** the runner cells show equal pass counts in the two
  modes, and `test-solve-parallel-equiv` pins the one solution. Linked
  fan-out is not established (exemplar memory).

**`exemplar/smoke.cl` stays byte-identical while ACT-1018 is carried.**
`exemplar_ownership_residue_s116::sudoku_warm_serial_solve_retains_nothing`
runs it as the subject of an exact-balance cell. Changing the entry changes
what that cell measures. Modules it loads may change under the exemplar
plan. `dev` then re-reads the cell: it must still fail on a nonzero
retained count with its zero-work control passing. A count other than 2, or
a pass, goes to `qa` before the change is kept; the four `s124_print_balance_*`
cells carry 1018 independently, so neither outcome alone closes or reopens
it.

**The `user.cl` rewrite** is gated by `exemplar_link_run_parity`, which
compares the two modes' output with each other and pins no text. No
reconciliation is owed unless the entry's name changes.

### 27.5 Training: what `test` reconciles in `tests/examples.rs`

The examples harness is a maintenance check on the learning sequence. It
accepts no compiler behaviour; an example the compiler breaks is intake for
`qa`. T125-5 may merge 23 into 21, retire or repurpose 23, and teach
non-empty input in 24. For each kind of change, in the same change-set as
`training`'s:

| Change by `training` | `test` reconciles |
|---|---|
| A file removed or renamed | Its row in `expected_exits()`. The umbrella cell compares the table with the files on disk and fails on either surplus |
| 21 changes its sub-tests or its printed lines | Row `21-hello-io.cl` (250) and `hello_io_example_prints_its_lines_in_order`, which pins exit and the seven lines. Keep its clause: an effect that ran early, twice or not at all changes the transcript |
| 23 retired | Row `23-io-sequence.cl` (178) and the comment near line 228 that names 21 and 23 |
| 24 reads non-empty input | Row `24-io-echo.cl` (20) and its comment, which describe a closed stdin. `run_example` nulls stdin, so a lesson that needs input takes it from the `test-capture` platform, or `test` adds a per-example stdin to the harness. `training` states which |
| Any later file renumbered | Every affected row. The two directory projects have their own cells |

- **Each new exit is derived, not copied:** `training` states the sub-test
  sum, and `test` confirms the observed exit equals it under `--run` and
  linked, cold and warm.
- **No clause is dropped silently.** If 23 goes, its behaviours either
  appear in 21's pinned transcript or are named as no longer exercised by
  the sequence.
- **Outside `tests/`:** `user/getting-started.md` links 21 and 23 (`docs`).

### 27.6 The sprint demo and the replay

Demos are showcases. They display behaviour that cells in this delta
already accept, and establish none.

- **The demo is not a sprint-named file.** `repl/demos/AGENTS.md` folds a
  capability into its demo. Candidates and the cell each rests on:

  | Capability | Demo | Rests on |
  |---|---|---|
  | Opaque `IO`: `pure`, nested `IO` shown as `#io`, a function value as `#closure` | `07-io-and-effects` | The `opaque_io` cells; `s124_markers_*` |
  | `/type` of a macro expression; a definition refused | `01-tour` or `04-functions` | `s124_type_macro_expression`, `s125_ty3_*` |
  | A generated definition is owned by its call | `10-redefinition` | The `s125_q51_*`, `s125_q52_*`, `s125_q9_*` cells |
  | `/search` reaches an unloaded dependency | `09-library-discovery` | `s124_search_reach_*` |

  `test` chooses among them. A segment shows a refusal the specification
  requires; none triggers a carried defect.
- **Evidence for the replay** (maintenance; `test` reports, `qa` reads):
  1. All 41 demos (12 numbered, 3 un-numbered, 26 archived) replayed with
     `DEMO_FAST=1` against a binary built from the final tree, each
     completing.
  2. Every `Error:` line classified: a narrated refusal, or a carried
     defect named by its failing cell. Any other is intake for `qa`.
  3. `memory-lifecycle` and `optimization` re-read against their output:
     W5 changed the `pure` node and the cache version, and their narration
     cites exact counts and IR.
  4. Each new segment's output read against the cell it rests on.

### 27.7 Carry-ins

- **T-0863** (§25.1): three cells, GREEN on arrival. Delivered; FIXME 0863
  is deleted (§27.10).
- **`repl/demos/AGENTS.md` lines 53–56** say the `def` echoes in
  `08-sudoku.demo` show the singular result FIXME 0800 records. They no
  longer do: `(def n 42)` echoes `user/n-def ; defn` then `user/n ;
  defmacro` (`qa`'s probe, standard prelude), as
  `spec_11_stdlib::def_definition_echo_lists_every_emitted_definition_in_order`
  asserts. `test` removes the example and keeps the rule that known-defect
  output stays visible and attributed. FIXME 0800 is narrowed to its third
  face by `dev` on `stdlib/`.
- **T-1102-SEED** (§27.1): re-seed
  `s124_refused_save_cached_restart_survives_call_and_next_turn` through
  the inline-`mod` guard, as its cold control is seeded, and assert the
  seed's backing file does not hold `f`. Its clauses stand: the restart
  exits 0, `(f)` is refused as undefined, and the next turn prints 10.
  Expected GREEN.

### 27.8 The handoff for `test`

**Delivered and accepted (§27.10):** T-F3, T-F2 with its `pool-trap`
fixture, T-1102-SEED, T-0863.

**The next dispatch, one list.** A defect cell carries its `// spec:` and
`// defect:` lines.

| # | Item | Expected | With |
|---|---|---|---|
| 1 | Exemplar runner pin 43 → **46**, both runner cells (§27.4) | GREEN | `dev`(exemplar)'s delivered change |
| 2 | **T-SELFTEST-IO** (§27.11): the `io` shell cell, and the shell-coverage guard | Guard RED before the `io` cell exists, GREEN after; `io` cell GREEN | — |
| 3 | The stale `// defect:` line on `stdlib_core_io_public_scalar_driver_across_modes` (§27.11) | No behaviour change | — |
| 4 | `tests/examples.rs` (§27.5) | GREEN | `training`'s change-set |
| 5 | The demo segments and the replay of 41 (§27.6); the demo guidance correction (§27.7) | Replays complete | After items 1 and 4, on the final tree (§29.3) |
| 6 | **T-STACK** (§29.2). Delivered and accepted (§30.1) | Subjects RED; control GREEN | — |
| 7 | **T-RESID-DISPLAY**, **T-ARG-SCOPE** and the two demo repairs (§30.2, §30.4) | Subjects RED; controls GREEN | Before the full run |

**Completion.**

- No cell is ignored. No assertion is removed outside the reconciliations
  of §27.4 and §27.5.
- For item 2, the guard is observed RED on the missing `io` shell before
  the `io` cell is added.
- The replay record of §27.6.

**`qa` then:** reads the Phase 6b full run against §24.3's set plus the
cells of this section.

**Other owners, through `sprint`:**

- `arch`: row R20's "second forces unmeasured" becomes the T-F3 result:
  the cells are in (§27.10). `design/arch/macro-availability-model.md` §9
  still lists FIXME 0863 as open.
- `docs`: the links to examples 21 and 23 if T125-5 retires or renames
  either.

### 27.10 Acceptance of `test`'s items 1–4

`qa` ran the ten named cells once, alone: 9 passed, 1 failed.

| Item | Cells | Result | Verdict |
|---|---|---|---|
| T-F3 | `spec_10_io::run_mode_reused_launched_poll_step_performs_each_force`; controls `…fresh_launched_poll_step_per_force_control`, `…launched_poll_step_single_force_control`, `…reused_awaited_poll_step_control` | Subject RED: `status: signal: 11 (SIGSEGV)` against exit 2, empty stdout. Controls GREEN | **Accepted.** The red is on the exit clause, by the signal. The subject binds one `(mk)` by `let` and forces it twice; the controls differ as §27.3 requires |
| T-F2 | `platform_errors::overlapping_platform_trap_reports_fault_without_signal_death`; control `…non_overlapping_platform_trap_reports_fault_control` | Both GREEN | **Control accepted. Subject returned:** it does not overlap (below) |
| T-1102-SEED | `repl_persist::s124_refused_save_cached_restart_survives_call_and_next_turn` | GREEN | **Accepted.** The seed asserts the refused save; `(f)` must now be undefined |
| T-0863 | `spec_09_macros::shrinking_macro_redefinition_retires_surplus_clauses_neg`, `…failed_multi_clause_macro_redefinition_keeps_every_prior_clause_neg`, `…macro_emitted_private_definition_not_importable_neg` | GREEN | **Accepted.** FIXME 0863 deleted |

**T-F2's GREEN subject: the cell is not discriminating, and F2 is not
refuted. The fault was in `qa`'s allocation.**

- **Observed at the seam.** `qa` ran the committed program under a preload
  shim that logs each `signal(SIGSEGV, …)` and the disposition in force at
  `raise`. One thread makes every call: install at 9 ms, restore at 819 ms,
  install again at 819 ms, trap at 1,722 ms with the guard's handler in
  force. The trapping call began after the first returned. Nothing
  overlapped.
- **Why.** The committed `x` is `(bind (pool-read 1 1 800) (fn [r]
  (poll-read 9 1 5000)))`. Its continuation ignores `r`, so the step is
  launch-eligible, and a launched blocking call runs on the reactor thread
  (§27.3's second probed shape). `qa`'s own overlap probe used the result;
  §27.3 did not say that it must. `test` built what was written and
  followed the report rule.
- **The corrected subject fails as predicted.** With `x`'s continuation
  using `r` (§27.3 as amended): thread A installs at 14 ms and saves the
  prior disposition; thread B installs at 315 ms and saves the guard's
  handler; A restores the prior disposition at 823 ms; B traps at 1,215 ms
  with the prior disposition in force, and the process dies on SIGSEGV with
  no report. 5 of 5 without the shim. The corrected control (50 ms)
  reports the dispatch fault, 3 of 3, with its two calls not overlapping.
- **Attribution confirmed** at
  `crates/cranelisp-intrinsics/src/io_guard.rs::force_effect_thunk_protected`:
  a per-call save and restore of a process-global disposition. *Refuted
  if* a build that keeps the handler installed across overlapping calls
  still dies on the corrected subject.
- **The fixture stands.** `pool-trap` raises SIGSEGV on the forcing thread
  after its sleep, as specified.

**For `test`, one change:** in `overlapping_trap_output`, `x` becomes the
expression of §27.3, with `add-i64` imported. The helper serves both
cells. Subject RED on the non-signal-exit clause; control GREEN. No timing
changes.

**Bands set:** spec §10.8.1 (a reused awaited poll-shape step Tested; a
reused launched step RED with its controls); spec §12.7.6 (the trap path
Tested by the control; the overlap case nonconforming, with no
discriminating cell until the correction lands); repl §15.2 (the
re-seeded cell cited).

**The corrected T-F2 subject is accepted.** `test` applied the change:
RED 5 of 5 by SIGSEGV, on the non-signal-exit clause and the report
clause; control GREEN. `qa` read the helper as committed and did not
re-run it; the result matches `qa`'s probe of the same program. Spec
§12.7.6 cites it.

**Still owed by `qa`:** read the Phase 6b full run.

### 27.11 Stdlib: the `io` self-tests, a stale defect line, `core.io`

**`stdlib/io/monad/test.cl` is not run by the suite** (`review`).
`tests/stdlib_conformance.rs` has one self-test cell per shell and names
eight: root, `collections`, `compare`, `core`, `fn`, `num`, `testing`,
`text`. Each cell skips every module outside its shell, so a module in a
shell with no cell is discovered by none. `io.monad` is the first module
in `io` to declare a test child.

- **Class:** a maintenance check that cannot see part of what it claims
  to check, the fault §26.1 closed for unlisted public-API baselines.
- **T-SELFTEST-IO, for `test`** (maintenance; `stdlib/AGENTS.md`
  §Loading and running self-tests):
  1. `s124_stdlib_selftests_io`, as its eight siblings. Expected GREEN,
     with a nonzero tally.
  2. **A shell-coverage guard:** one cell that derives the set of shells
     holding a module with a test child, by the walk the cells already
     use, and fails naming any shell that no self-test cell covers. The
     shell list becomes one constant that the guard and the cells share.
     Observed RED on `io` before step 1 is added.
- **Wrong outcome rejected:** a self-test module added under a new shell
  that passes review and never runs.
- **Not allocated:** a per-module count pin. The nonzero-tally clause
  already fails an empty discovery.

**The `// defect:` line on
`stdlib_core_io_public_scalar_driver_across_modes` is stale, not an open
defect.** It reads `class=rc-miscount`, with a prose locus, no `found=`
or `owner=`, and a present-tense abort. The cell was the public aggregate
of condition Q3 in the [S122 delta](s122-evidence-delta.md): RED at the
S121 close, attributed there to the shared-`Bind` field transfer in
`crates/cranelisp-intrinsics/src/io.rs`, and GREEN since that
correction. It passes in every run of this delta.

- **For `test`:** rewrite the line in the notation's form, with the S122
  seam as `locus=`, `found=S121`, `owner=/dev`, `fixed=S122/<commit>`, and
  the comment in the past tense. No assertion changes.
- **Why it matters:** a green cell that still reads as an open abort
  lets a later regression of it pose as a known guard (`tests/AGENTS.md`,
  defect-repro rules).

**`core.io` has no self-tests, and none is constructible.** Its functions
return `IO` values, and a discovered test has type `(Fn [] (Option
String))`, so it cannot force one. Its evidence is the
`stdlib_core_io_*` conformance cells, which run each public composition
in REPL, `--run` and linked. No allocation. `io.monad`'s withheld cases
(`do` over several actions, `bind!` with bindings) rest on
`tests/spec_11_stdlib.rs` in the same way.

### 27.12 Checks on `qa`'s files
- `tests/plan/spec_coverage_reconcile.py` (at §29): 1,356 live citations, no dead
  citation, no name not found, no cleared row awaiting `qa` (one before the
  edits).
- `tests/plan/spec_link_check.py` (at §29): 4,051 citations, none mis-cited or
  malformed.
- The document checker (root `AGENTS.md` invocation) exits 1 on the
  repository's standing `ignored-path` findings. This section adds none.
  This file's remaining findings are the `ignored-path` citations of the
  compiler binary in the header and of the demo run directory in §13,
  which predate it.
- `git diff --check` is clean for the edited files.

## 28. F2 and F3 repair readiness (2026-11-28)

**Authority:** the user's decision of 2026-11-28, "fix F2 and F3 this
sprint"; [process lifecycle §1.8](../../design/intrinsics/process-lifecycle.md)
(F2); [ownership §6.3, §6.4 and §8](../../design/intrinsics/ownership-and-disposal.md)
(F3). `qa` ran no test. Every observation is a probe of the debug compiler
binary of §27 in a scratch directory; signal writes were logged by a
preload shim.

**Verdict.** Both designs' evidence is adequate with the amendments of
§28.3. The binary's macro guard changes with F2 this sprint (§28.1). Reuse
of a poll-shape leaf is a third, separate nonconformance, now reproduced
(§28.2); its repair is not scheduled.

### 28.1 The lead: the binary's macro-clause guard

**Overlap is not reached; the two guards still do not compose, and that
needs no overlap.**

| Question | Finding | Grade |
|---|---|---|
| Can two macro calls overlap? | Not observed. Eight independent modules of 4,295 macro calls each, under `--run`: at the default one priority worker every call ran on one thread; at `--priority-workers 4` they ran on four threads with 7 thread switches in 71,720 disposition writes and no install while another thread was inside. Three runs each | Measured on one corpus; not shown structural. *Falsifier:* an install of the macro handler logged between another thread's install and restore |
| Can a macro call overlap a platform force? | No path found by reading: expansion precedes execution on the driving thread in the REPL and under `--run`; a turn returns only after its workers and strands finish; a linked executable holds no expander | Asserted, with a named falsifier: a platform force in flight while any thread is inside a macro clause call |
| Does a macro call write the dispositions after a platform force, with no overlap? | **Yes, in an ordinary session.** REPL: `(print "x")`, then `(defmacro m …)`, `(m)`. The macro call installs its handler for `SIGILL` and writes back what it found, through `signal`, after the force's own install and restore. It does the same for `SIGFPE` and `SIGBUS`, and never touches `SIGSEGV` | Measured |

**Consequence for §1.8.** Once intrinsics installs once and never restores,
the first macro call after the first platform force re-installs the
intrinsics handler through `signal` for three of the four signals,
without `SA_SIGINFO` and `SA_ONSTACK`. The handler is then entered with
one argument, and its forward of an unarmed trap passes on arguments it
was never given. §1.8's "nothing writes these dispositions again" holds
inside the crate and is false of the process from that call on. `design`'s
overlap case would remove the guard outright; this case degrades it and is
reached by every REPL session that uses a macro after an effect.

**T-F2 does not depend on it.** The macro guard leaves `SIGSEGV` alone, so
T-F2 turns green on the intrinsics repair.

**No reproduction on the binary's side: not constructible.**

- No program makes a macro clause trap. Division by zero in a clause is a
  language panic that ends the process (`error: runtime panic: division by
  zero`, probed).
- The guard's recovery path has no executing evidence at all: its message
  text, `runtime error during macro expansion`, appears in no test.
- With no trap and no overlap, no e2e cell can fail on today's source.

**Disposition: `design`(int) settles the macro guard this sprint, with the
F2 repair.** `src/` is the focus module, and the F2 rule is a property of
the process. Two shapes satisfy it, and the choice is `design`'s, with
`arch` if one owner for both guards is preferred:

- the same rule as §1.8 (one install, the action it found recorded, an
  unarmed trap forwarded); or
- no guard in the binary. It protects against a trap that no program can
  raise and nothing has ever observed it recover one, so its residual is a
  compiler defect in clause code, which would then end the process on the
  signal.

**Outcome (2026-11-28): the guard is deleted.** `design`(int) chose the
second shape:
[macro-turn ownership, Rule 8](../../design/int/macro-turn-ownership.md).
A clause call is a plain call; the binary installs no handler, holds no
jump target and recovers nothing. Its evidence is that document's D5 (the
workspace census, with planted writers and the `SIGUSR1` negative leg) and
D6 (a clause call leaves all four dispositions unchanged, handler and
flags, against sentinel actions). D5 is item 1 below; D6 replaces items 2
and 3, which applied only to a kept guard. `qa`'s reading is in §29.1.

**Evidence owed with it**, by `dev` on `src/`:


1. **The census of §1.8 at workspace scope**, for the four trap signals:
   no `signal` or `sigaction` call on them outside the guard modules the
   designs name, with its planted-call detection proof. `src/sched_dump.rs`
   installs `SIGUSR1` and is outside it.
2. **If a guard is kept, composition,** in a child process, in both
   orders: after one guarded platform call and one macro call, the
   installed action for each of the four signals is the first installer's,
   flags intact. Observed failing on today's per-call `signal` restore.
3. **If a guard is kept, recovery:** a clause-shaped entry that raises
   `SIGILL` returns the macro error. It is the path's first executing
   evidence.

### 28.2 Reuse of a poll-shape leaf: reproduced, sequential and in flight

Ownership §6.4 asks whether two forces of one leaf in flight together need
a cell. They do, and the sequential case fails too.

**Observed** (platform `poll-pool`, `--run`, 5 of 5 runs each; the leaf is
`(poll-log 7 1 300 "L")`):

| Program | Stdout | Reading |
|---|---|---|
| **Sequential subject.** One `let`-bound leaf forced, then forced again in a `select` beside a marker branch that prints `m` after 100 ms | `LLm` | The second force does not suspend: its `L` precedes the marker |
| Sequential control: a fresh leaf per force | `LmL` | Each force suspends 300 ms |
| **In-flight subject.** One leaf forced on both branches of a `select`; each branch then prints its tag (`x`, `z`) after 100 ms | `LLxz` | Two effects on a capacity-1 token complete together |
| In-flight control A: a fresh leaf per branch, capacity 1 | `LxLz` | Serialised, in source order |
| In-flight control B: one leaf, capacity 2 | `LLxz` | Overlap the token permits |

Wall-clock agrees: one reused 500 ms leaf forced twice in sequence takes
535 ms; two fresh ones take 1,035 ms.

- **Requirement.** Spec §10.8.1: each force is interpreted exactly as the
  first. Spec §10.12.4.1 items 2 and 4: at most one effect on a
  capacity-1 token runs at a time, in source order.
- **Mechanism, from source, consistent with the controls.** The timer
  leaves keep their phase in the state closure's result slot: zero means
  unstarted, and on completion the slot holds the result. The backend
  zeroes the slot when it builds the node, and nothing zeroes it per
  force. A second force finds it non-zero, reads it as an elapsed
  deadline and completes at once. *Refuted if* a build that gives each
  force a zeroed slot still prints `LLm`.
- **It is the leaf's state, not every poll leaf.** A reused `stdio`
  `read-line` forced twice on input `one`, `two` yields `one|two`, as a
  fresh pair does. That leaf keeps no phase in the slot.
- **Harm.** A reused timer, or any leaf written to the same pattern,
  returns its previous result without doing its work, and holds no
  exclusion against a concurrent force. `async-demo`, which example 34
  teaches, documents the same slot convention.
- **Where it entered:** the state-closure contract between the backend,
  intrinsics and platform authors
  ([poll-leaf authoring](../../design/platform/poll-leaf-authoring.md)),
  which predates the reuse ruling and is silent on a second force. Row R20
  names it. Provisional locus
  `crates/cranelisp-intrinsics/src/io.rs::await_poll_node`; the seam is
  `arch`'s. Class `consuming-force`.
- **Why coverage missed it, and why §27 did too.** T-F3's control C
  asserted two prints and an exit code. Both hold when the second force
  skips its wait. `qa` then banded §10.8.1 as "performs its effect each
  time". The band is corrected.

**T-POLL-REUSE, for `test`** (acceptance; `--run`; no prelude; in
`tests/spec_10_io.rs`):

| Cell | Asserts | Expected |
|---|---|---|
| Sequential subject | stdout `LmL` | RED (`LLm`) |
| Sequential control | stdout `LmL` | GREEN |
| In-flight subject | stdout `LxLz` | RED (`LLxz`) |
| In-flight controls A and B | `LxLz`; `LLxz` | GREEN |
| `read-line` reuse, input `one`, `two` | stdout `one|two`, with its fresh twin | GREEN |

- **Fixture properties.** Order is the witness, not elapsed time: the
  marker and tag delays are 100 ms against a 300 ms leaf, and every branch
  ends in a long wait so that no branch completes before all output.
- **Wrong implementations rejected:** today's; a second force that returns
  the first's result. **Limit:** a repair that zeroes the shared slot at
  each force would pass the sequential pair, and the in-flight subject is
  the only cell that can then fail; whether it does depends on the leaf,
  so the repair's design names its own unit rows.
- **Control C of T-F3 stays.** It shows that reuse neither crashes nor
  drops a print.

**Repair: not scheduled.** By default the defect is carried on these
cells. Intrinsics takes a larger change this sprint, so *clean house*
applies: `design`(intrinsics) and `arch` say whether a per-force state
fits beside the F3 repair, and the user decides. It is not part of F3:
§6.3's rule and T-F3 hold without it.

### 28.3 The designs' evidence

**F3 (ownership §6.3, §8): adequate, with one row to add or name.**

- The owed rows cover the three wrong outcomes: a force that still writes
  the node, a strand that is not given its own reference (a double
  discharge), and a node that no longer discharges its field (a leak).
- **Add or name:** a strand dropped before it completes, with the node
  still live and with the node already released, discharges exactly its
  own reference. Cancellation reaches detached strands through the
  supervisor's drop, and the new mint adds a reference on that path. If an
  existing cell covers it, `dev` names it.
- **E2E: T-F3 and its controls suffice.** After the repair the subject
  runs two launched strands over one poll leaf at capacity 1. It turns
  green on §6.3 alone, because the second strand's stale completion still
  prints (§28.2). It therefore says nothing about poll-leaf state.
- No e2e balance cell: the module balance rows observe the counts at the
  seam, and an e2e marginal would repeat them through more machinery.

**F2 (process lifecycle §1.8): adequate, with one amendment.**

- Cell 1 is the module twin of T-F2 with the order fixed by barriers.
  Cells 2 to 5 cover the two wrong implementations §27.3 names and the
  unarmed paths the new handler adds.
- **Amend:** the census is scoped to the crate, and the property it grades
  is the process's. §28.1 item 1 widens it; until the binary's guard is
  settled, the row "a protected call's return never removes another
  thread's protection" is structural for `SIGSEGV` only.
- **E2E: T-F2 and its control suffice.** One mode: a linked executable
  runs the same runtime guard and holds no expander.

### 28.4 Next dispatch

1. **`test`:** T-POLL-REUSE is delivered and accepted (§28.5). The open
   list of §27.8 remains.
2. **`design`(int):** the macro guard (§28.1), in parallel; then `arch`
   only if it proposes one owner.
3. **`dev`(intrinsics):** F3, then F2, each with its unit rows red first
   and the additions of §28.3; then `dev`(`src/`) for the macro guard;
   `review` on each.
4. **`arch`:** row R20 (the launch result, and the poll-leaf result), and
   the seam of §28.2.
5. **`design`(intrinsics):** §6.4 is superseded by §28.2's measurement.
6. **`qa`:** after the repairs, read T-F3 and
   T-F2 green, band §10.8.1 and §12.7.6, and read the full run.

**For the user:** whether the poll-leaf state repair is taken this sprint
or carried.

### 28.5 Acceptance of T-POLL-REUSE

`qa` ran `spec_10_io` alone, once: 263 run, 253 passed, 10 failed.

| Cell (`spec_10_io::`) | Result | Verdict |
|---|---|---|
| `run_mode_reused_poll_leaf_suspends_on_each_sequential_force` | RED: stdout `LLm` against `LmL`, exit 0 | **Accepted** |
| `run_mode_fresh_poll_leaf_per_sequential_force_control` | GREEN | Accepted |
| `run_mode_reused_poll_leaf_in_flight_capacity_one_serialises` | RED: stdout `LLxz` against `LxLz`, exit 0 | **Accepted** |
| `run_mode_fresh_poll_leaf_per_in_flight_force_control` | GREEN | Accepted |
| `run_mode_reused_poll_leaf_in_flight_capacity_two_control` | GREEN | Accepted |
| `run_mode_reused_read_line_reads_each_input_with_fresh_control` | GREEN | Accepted |

- **Each red is on its clause.** Both subjects exit 0 and fail the stdout
  comparison; neither fails on setup, a refusal or a timeout.
- **Each subject differs from its control in one expression:** the second
  force names the `let`-bound leaf where the control builds a fresh one.
- **No step is launched.** Every continuation uses its binder, and the
  hold is a `sleep`, which is never launched alone. `test` replaced the
  probe's long poll wait with that hold; the witness is unchanged.
- **The other eight failures are carried:** 1018 (four
  `s124_print_balance_*`), 1075 (three `s124_1065_prelude_bind_*`) and
  T-F3's subject.

**Bands set:** spec §10.8.1 (both reds with their controls; the
`read-line` cell Tested) and §10.12.4.1 item 4 (the fresh-leaf control
Tested for two poll leaves on `select` branches; the reused leaf
nonconforming).

**`dev`(intrinsics) may start F3 and then F2** against the designs and
§28.3. Neither repair depends on these cells, and T-F3 and T-F2 are
accepted reds (§27.10).

## 29. F2 and F3 repairs: adequacy (2026-11-28)

**Verdict: both repairs are adequate.** T-F3 and T-F2 are green with their
controls, the module evidence the designs and §28.3 named is present, and
the binary's guard is gone with its two cells. One intake follows (§29.2).
Everything is uncommitted; `qa` read the landed source and cells and ran
`spec_10_io` and `platform_errors` alone, once.

### 29.1 The repairs

**The run:** 291 run, 282 passed, 9 failed. `platform_errors` is 28 of 28.
`spec_10_io`'s nine are 1018 (four), 1075 (three) and T-POLL-REUSE's two
subjects.

| | Solution evidence | Module evidence, read in source |
|---|---|---|
| **F3** | `spec_10_io::run_mode_reused_launched_poll_step_performs_each_force` GREEN (`LL`, exit 2), red before the repair on the signal (§27.10); controls A, B, C GREEN | `launch_continue` takes a reference through `rc_inc` and writes nothing; the strand's guard releases it on completion and on drop. `io/tests.rs`: forced twice (two runs of the sub-tree, field 0 unchanged, one discharge after the last owner); forced once; a strand dropped before completion with the node live, and with the node already released; the unforced leg is the existing `drop/tests.rs` cell |
| **F2** | `platform_errors::overlapping_platform_trap_reports_fault_without_signal_death` GREEN, red before the repair by signal death (§27.10); control GREEN | `run_trap_guarded` installs once and records the actions it replaces. `io_guard/tests.rs`: the two-thread overlap; the guard still installed after a return; an unarmed trap under a default action dies on the signal; an unarmed trap is forwarded to a previous `SA_SIGINFO` handler; a trap during installation is forwarded to the replaced action (`review`'s finding); nesting; the crate census with a planted writer |
| **Binary** | None is constructible (§28.1) | The guard is deleted. D5 and D6 of [macro-turn ownership](../../design/int/macro-turn-ownership.md) |

- **Red first.** Both solution cells failed on their stated clause before
  the repair and pass after it with no change to the cells. The module
  rows' reds are as `dev` and `review` record them.
- **§28.3's two additions are met:** the strand-drop pair for F3, and the
  census at workspace scope (D5) for F2.
- **§28.1's composition concern is closed by construction.** With no
  second writer, the order of a macro call and a platform force cannot
  matter; D6 measures that a clause call writes nothing.
- **A probe of the composed process:** a stack exhaustion after a platform
  force ends as it does before one (§29.2), so the guard's forward of an
  unarmed trap reaches the Rust runtime's handler intact.
- **Limits.** One mode (`--run`) for both solution cells. Concurrent
  traps on two armed threads rest on the terminator's claim, with no
  cell. The handler's thread-local read is asserted with the design's
  falsifier. Whether a non-overflow trap in a clause may end the process
  on its signal is S125-Q12, with the user.

**Bands set:** spec §10.8.1 (a reused launched step Tested, with its
controls) and §12.7.6 (the trap path Tested+Neg, overlap included).

### 29.2 Intake: stack exhaustion is not reported as a runtime panic

**Reproduced.** Spec §12.7.2.1 lists stack overflow as a panic source, and
§12.7.5 requires one stderr line beginning `error: runtime panic: `, in
every mode, macro expansion included (§9.12).

Program: `(defn deep [n] (if (eq-i64 n 0) 0 (add-i64 1 (deep (sub-i64 n
1)))))`, called at depth 100,000,000.

| Where | Result |
|---|---|
| `--run`, default and with `CRANELISP_NO_LENIENT=1` | Killed by `SIGABRT`; stderr `thread 'main' … has overflowed its stack` and `fatal runtime error: stack overflow, aborting` |
| REPL turn | The same; no further prompt |
| Macro clause (`(defmacro big [] (macros/SexpInt (deep …)))`, `(big)`) | The same |
| `--run`, after a platform `print` | The same, after `x` |
| Linked executable | Killed by `SIGSEGV`; **no output at all** |
| Control: the same program at depth 1,000 | Exit 0 |

- **Two faces.** In the compiler process the report is the Rust
  runtime's, not the language's, and the exit is a signal. In a linked
  executable there is no report: a second nonconformance and a mode
  divergence.
- **Attribution.** No stack-exhaustion condition enters the runtime's
  terminator (`crates/cranelisp-intrinsics/src/panic.rs`); the outcome is
  whatever action the process has for `SIGSEGV`. The compiler process has
  the Rust runtime's overflow handler; the linked startup has none. The
  control differs only in depth. Class `missing-runtime-check`. Provisional
  locus: the intrinsics terminator and the linked startup; the mechanism
  that would detect exhaustion is `design`'s to choose.
- **Where it entered:** never built. The row has carried a pending tag
  since Sprint 18, and §12.7's band says it is untested. S125 did not
  cause or change it: the deleted macro guard never handled `SIGSEGV`, and
  the outcome is the same before and after a platform force.
- **Why coverage missed it:** no cell was ever allocated to the row.
  Several cells assert that a program does *not* overflow; none exhausts
  the stack.

**T-STACK, for `test`, now** (acceptance; spec §12.7.2.1, §12.7.5; no
prelude; in `tests/spec_12_runtime.rs`). A defect is carried on a failing
cell, and this one has none.

| Cell | Asserts | Expected |
|---|---|---|
| `--run` | Exactly one stderr line, beginning `error: runtime panic: `; a non-zero exit that is not a signal; nothing on stdout | RED |
| REPL turn | The same, and no later prompt or value | RED |
| Macro clause | The same | RED |
| Linked executable | The same | RED |
| `--run` after a platform `print` | The same, with `x` on stdout | RED |
| Control at depth 1,000 | Exit 0, in the same modes | GREEN |

- **The message is implementation-defined;** assert the prefix only.
- **Fixture property:** the recursion is not in tail position, so it
  cannot be compiled to a loop.
- **Wrong implementations rejected:** a report written by the compiler
  process only; a handler installed only after the first platform force;
  a report followed by a signal death.

**Repair: not scheduled.** It is carried on T-STACK. It is not a `src/`
defect, and it touches the trap path F2 just changed, so *clean house*
gives `design`(intrinsics) the question of whether it belongs with that
work. The user decides.

### 29.3 The list for `test`

§27.8 is amended: item 5 runs on the final tree, and T-STACK is item 6.

- **In the tree, read by `qa`:** the exemplar pin at 46; the rewritten
  `// defect:` line (`found=S121`, `fixed=S122/7f834bf6`). **Present, with
  its red-first record owed in `test`'s report:** the `io` shell cell and
  `s125_stdlib_selftest_shell_coverage`.
- **Item 5, the demo replay, on the final tree.** The binary is built
  after the F2 and F3 repairs and the guard's deletion. §27.6's four
  evidence points stand, with two additions:
  1. `07-io-and-effects` and any demo that runs a platform effect and a
     macro in one session replay unchanged; that is every session using
     the standard prelude after a `print`.
  2. No demo, guide or example narrates the deleted
     `runtime error during macro expansion` text (`qa` found none), and
     none shows a stack exhaustion.
- **Order:** T-STACK first; then the replay, last.

**`qa` then:** accepts T-STACK's reds and bands §12.7.2.1's row; reads the
Phase 6b full run.

## 30. T-STACK, the replay intake, and what precedes the full run (2026-11-28)

`test`'s record is its dispatch report and retained transcripts. `qa` ran
the six T-STACK cells and the two `stdlib_conformance` shell cells alone,
read the replay transcripts, and probed the debug binary of the final
build in a scratch directory.

### 30.1 Accepted

| Item | Result | Verdict |
|---|---|---|
| **T-STACK**, five subjects (`spec_12_runtime::s125_stack_exhaustion_*`) | RED: `SIGABRT` under `--run`, in the REPL, in a macro clause and after a `print`; `SIGSEGV` when linked. Each fails the non-signal-exit clause and the one-line report clause | **Accepted.** The helper also requires that the linked executable ran, so a link failure cannot pass as the red |
| `…shallow_control_completes_in_every_mode` | GREEN | Accepted |
| **Shell-coverage guard**, red record | Reconstructed by removing the `io` runner: `stdlib self-test shells without runner cells: ["io"]`. Restored: guard and `s124_stdlib_selftests_io` GREEN, as in `qa`'s run | **Accepted as a reconstruction.** It shows the guard detects. No capture of the guard failing before the `io` cell was first added exists |
| **Demo segments** | `01-tour`: `(twice 2)` gives 4 and `/type (twice 2)` gives `:primitives/Int`, no error. `07-io-and-effects`: `[(pure 7)]` shows `[#io]`; a function value shows `#closure` | **Read against their cells** (`s124_type_macro_expression`; `s124_markers_nested_io_display`, `s124_markers_closure_display`). Each displays behaviour a cell accepts |
| **Replay** | 41 of 41 complete; `optimization` narration matches; 19 narrated refusals | Accepted as a maintenance record. The seven intake lines and the `memory-lifecycle` contradiction are §30.2 |

**Band set:** spec §12.7.2.1, the stack-overflow row.

### 30.2 The replay intake

**All seven `Error:` lines are demo-script faults, with one cause. The
cause exposes one defect, and the `memory-lifecycle` contradiction is a
second, which this sprint introduced.**

| Lines | Classification | Owner |
|---|---|---|
| `08-sudoku`: `undefined variable: not`, and the four that follow from `solve` being undefined | **Demo-script fault.** The demo uses `not` without importing it | `test`: import `not` from `primitives`, as the exemplar does |
| `archive/ring4b`: `undefined variable: mul-i64`, and `run` undefined after it | **Demo-script fault** (a stale expectation, which the archive rule makes a demo fix) | `test`: import `mul-i64`, and `int-to-string`, which the demo also uses unimported |
| `memory-lifecycle`: an unpinned `(Err "boom")` shows `<field types unavailable: residual type argument Var(1)>` | **Defect, caused by S125** (below). The narration is right and the output is wrong; the narration is not corrected | `dev` on `src/`; `test` for the cell |

**Why the two demos passed on 2026-11-16 and fail now.** The curated
prelude exports neither name and never did. Both forms hold a library
macro whose home module imports every primitive (`vec` in `solve`; `str`
in `run`). Until W8's correction of 1100, a foreign macro anywhere in a
form had the whole form's bare names qualified against that macro's
module, so `not` and `mul-i64` resolved through it. The run directories of
2026-11-16 hold both definitions saved, so they compiled then. W8 limits
qualification to the macro's own output. The refusals are the conforming
outcome; the demos recorded the defect.

**Defect A: a bare name inside a macro argument resolves in the macro's
module.** W8 narrowed the leak and did not close it.

- **Reproduced, free-standing.** Module `d` holds `(import [primitives
  [add-i64]])` and `(defmacro pass [x] x)`. In a module that imports only
  `pass`: `(add-i64 1 2)` is refused as undefined, and `(pass (add-i64 1
  2))` evaluates to 3; `/expand` shows `(primitives/add-i64 1 2)`. Under
  `--run` the program exits 3. With the standard prelude, `(str "a"
  (int-to-string 3))` gives `"a3"` while `(int-to-string 3)` is undefined.
- **Requirement.** Spec §8.6.1: a bare name resolves through the current
  module's scope. The argument is the caller's text. §9.3.4 lets the
  *expansion's own* references reach the macro's dependencies; nothing
  gives the caller's arguments that scope.
- **Harm.** A name the user forgot to import binds silently to whatever
  the macro's module happens to import under that spelling.
- **Attribution.** `src/process_form/macro_resolution.rs`: the
  qualification walk runs over the whole output, argument sub-trees
  included, and admits any name the home module's table holds
  ([expansion qualification §2.1](../../design/int/expansion-qualification-scope.md)).
  The control differs only in the wrapping macro call. Class
  `wrong-scope-lookup`. The design states this rule, so the repair starts
  with `design`(int).
- **S125 did not introduce it;** the earlier whole-form pass admitted
  more.

**Defect B: a value whose constructor does not use the residual type
parameter is not displayed.**

- **Reproduced, free-standing.** `(deftype (Two a b) (L [:a x]) (R [:b
  y]))`, then `(L 5)`: `:(user/Two primitives/Int a) (Two.L <field types
  unavailable: residual type argument Var(6)>)`. `(primitives/Err "boom")`
  likewise. Pinned by an annotation, the same value shows `(Result.Err
  "boom")`.
- **Requirement.** REPL §1.5: a value displays its constructor and fields;
  §1.5.1: a polymorphic value is never an opaque error. The field here is
  an `Int`; only the other parameter is unresolved.
- **Attribution.** `src/display.rs`: the display refuses every field when
  any type argument is residual, where only a field *of* a residual type
  cannot be read. The marker is absent from the sprint's opening source;
  W2 (row D-1) added it to close 1062. Class `check-domain-overreach`.
- **Why coverage missed it:** §10.2 took the marker to be unreachable and
  owed no e2e cell. `(Some [])` and `(Pair 1 [])` are refused as ambiguous,
  which is the case that reasoning had in mind; a constructor that does
  not mention the residual parameter is not.
- **Disposition: repaired this sprint.** S125 caused it, in the focus
  module (*no decay*). If the repair changes
  `cranelisp_types`' field-type operation, it goes to `arch` first.

### 30.3 Cells for `test`

**T-RESID-DISPLAY** (acceptance; REPL §1.5, §1.5.1; primitives-only
prelude; in `tests/repl_introspection.rs`):

| Cell | Asserts | Expected |
|---|---|---|
| `(L 5)` and `(R "s")` of `(Two a b)` | The value forms `(Two.L 5)` and `(Two.R "s")` after their polymorphic types; no `unavailable`, no `Var(` | RED |
| `(primitives/Err "boom")`, `(primitives/Ok 1)` | `(Result.Err "boom")`, `(Result.Ok 1)`, likewise | RED |
| Control: each value under a pinning annotation | The same value forms | GREEN |
| Control: `(primitives/Some [])` | Still refused as ambiguous | GREEN |

Wrong implementations rejected: today's; a repair that prints a field of
residual type by guessing its representation (the second control, and
1062's cells, hold that line).

**T-ARG-SCOPE** (acceptance; spec §8.6.1; no prelude; in
`tests/spec_09_macros.rs`):

| Cell | Asserts | Expected |
|---|---|---|
| `(pass (add-i64 1 2))`, caller has not imported `add-i64`; REPL and `--run` | Refused as an undefined variable, located in the caller's form | RED (evaluates to 3) |
| Control: the bare call | Refused the same way | GREEN |
| Control: after the caller imports `add-i64` | 3 | GREEN |
| Control: a macro whose *template* names `add-i64` (`(defmacro inc [x] \`(add-i64 ~x 1))`), caller has not imported it | Evaluates; the expansion's own reference still resolves | GREEN |

The last control is the fixture that separates the defect from the
mechanism it lives in: a repair that stops qualifying altogether fails it.

### 30.4 Before the full run

1. **`test`:** T-RESID-DISPLAY and T-ARG-SCOPE, red; the two demo repairs
   of §30.2, with `08-sudoku` and `ring4b` replayed after them.
2. **`dev` on `src/`:** Defect B, with a unit row red first; then
   `memory-lifecycle` replayed, its narration unchanged.
3. **Then the full run.** With 1 and 2 done its failing set is final.
   Without 2, T-RESID-DISPLAY is a red attributed to `src/` and the
   settling target's first clause does not hold.

**Defect A needs a decision, not a delay.** Its cell is a second red
attributed to `src/`. `design`(int) says what the repair costs, since the
walk cannot today tell an argument's symbol from the template's. It is
then repaired this sprint, or the user names it beside 1087 and 1090 as an
exception to the settling target. The full run does not wait on that.

**For `qa` at the full-run read:** spec §9.3.4's heading band still cites
1100's cells as failing; they pass since W8. Watch the `user_samples`
cells, which last ran before W8's change to qualification.

### 30.5 Acceptance of T-RESID-DISPLAY and T-ARG-SCOPE

`qa` ran the twelve cells alone, once: 8 passed, 4 failed.

| Cells | Result | Verdict |
|---|---|---|
| `repl_introspection::s125_resid_display_unused_user_type_parameter`, `…unused_result_type_parameter` | RED: the four value forms are missing and the marker is printed | **Accepted** |
| `…s125_resid_display_pinned_values_control`, `…ambiguous_field_refused_control` | GREEN | Accepted |
| `spec_09_macros::s125_arg_scope_unimported_argument_refused_repl`, `…_run` | RED: evaluates to 3; exits 3 | **Accepted** |
| The bare-call, caller-import and template-dependency controls, REPL and `--run` | GREEN | Accepted |

- **Each red is on its clause.** The display subjects complete their
  session and fail on the value forms. The scope subjects fail on "must be
  refused", with the session or program having run.
- **Each subject differs from a control in one thing:** the pinning
  annotation; the wrapping macro call.
- **The demo repairs are read:** `08-sudoku` imports `not`, and
  `archive/ring4b` imports `mul-i64` and `int-to-string`. Both replay
  with no `Error:` line.

**`dev` on `src/` may start Defect B** against §30.2 and T-RESID-DISPLAY,
with its unit row red first. Its two controls bound the repair: a pinned
value still displays, and a field of residual type is still refused, not
read. `memory-lifecycle` is replayed after it.

**Bands:** none set. REPL §1.5's rows gain T-RESID-DISPLAY when it is
green. Spec §8.6.1 has no row for a macro argument's scope; T-ARG-SCOPE
is cited when Defect A is disposed.

## 31. The Phase 6b full run (2026-11-28)

**Verdict: the settling target holds.** One maintenance pin is stale and
is repaired before close (§31.2). Two defects found in this phase are
carried on failing cells, outside `src/`, for the user to accept (§31.4).

### 31.1 The run and the set

The coordinator's run, on a fresh build of the uncommitted tree at
`4c844f62`: `cargo nextest run --no-fail-fast`, **8,447 run, 8,357 passed,
90 failed, 1 skipped, 274 s.** `qa` read its output and failing names and
ran nothing further.

Against §25.3's set of 82, by name (derived from the W8 name list less the
ten cells §22 to §24.2 record as fixed):

- **None of the 82 passes that failed.** The carried set is unchanged.
- **Eight are added.** Seven are this phase's accepted reds: T-STACK's
  five subjects (§30.1) and T-POLL-REUSE's two (§28.5). One is unexpected:
  `regression::s60_run_tests_reduction_1_exemplar_batched_failing`
  (§31.2).
- 82 + 8 = 90.
- **Green as accepted:** T-F3 and T-F2 with their controls;
  T-RESID-DISPLAY; T-ARG-SCOPE, all eight cells; T-1102-SEED; T-0863;
  the `io` shell cell and the shell-coverage guard; all 22 `user_samples`
  cells, which W8's change to qualification could have reached.

| Module | Failing | Defects (cells) |
|---|---|---|
| `src/` | 2 | 1087, 1090: the named exceptions |
| typecheck | 68 | As §24.3: 1076 (15), 1075 (9), 1071 (7), 1074 (6), 1103 (6), T-0985 (6), 1080 (4), 1082 (4), 1097 (3), 1104 (3), T-NARROW (3), 1073 (2) |
| intrinsics | 10 | 0977 (3); T-STACK (5; the linked face also reaches the linked startup); T-POLL-REUSE (2; provisional, the seam is `arch`'s) |
| backend | 1 | T-1036 (provisional) |
| Not attributed to a module | 7 | 1018 (5), 1067 (2) |
| Maintenance | 2 | The document gate; the stale exemplar pin of §31.2 |
| **Total** | **90** | |

### 31.2 The one unexpected red: a stale pin, not a regression

`regression::s60_run_tests_reduction_1_exemplar_batched_failing` runs the
exemplar's `/run-tests html` and requires the text `12 passed in`. The
session exits 0 and reports `13 passed`: the thirteenth is
`html/test-not-found-page-escapes-path`, added with the 404 repair.

- **Class:** a maintenance pin on the exemplar's test count, stale by this
  sprint's own exemplar change. No compiler behaviour is involved.
- **Why it was missed:** §27.4 named the runner pin in
  `tests/exemplar.rs` and looked for `--test` pins. `qa` did not look for
  a `/run-tests` count.
- **For `test`:** 12 becomes 13, with its comment. `qa` reads the cell
  green alone; no further full run is needed for it.

**The document gate** (`citation_drift`) is in §24.3's set and fails as
before, on `ignored-path` findings only. This phase's edits add none.

### 31.3 `dev`'s lead: `constrained_clause_nonoverlapping_arity_dispatches_two_instantiations`

It has an owner. Its `repl_cached` leg is one of T-NARROW's three cells
(§17.3, §24.3): the cached restart refuses `cannot redefine user/g`
because a file cluster narrows a constrained written variable, a
typecheck defect carried on
`constrained_file_cluster_narrowing::s125_t_narrow_file_int_use_preserves_float_{repl,run}`.

- It is a coverage cell, not a reproduction, so it takes no `// defect:`
  line.
- **Its comment is stale.** "RED at HEAD (the constrained clause is
  rejected-by-construction)" describes Sprint 112. **For `test`:** replace
  it with the present state: every leg passes but the cached REPL leg,
  which fails on the T-NARROW defect and turns green with those cells.

### 31.4 The settling target

| Clause | Reading |
|---|---|
| No failing test attributed to `src/` but 1087 and 1090 | **Holds.** Defects A and B, found and attributed to `src/` in this phase, are repaired and their cells green. The 1082 attribution stays provisional (§24.3) |
| No `src/` build warning | As §24.1. `qa` did not read this build's output for warnings; the coordinator's fresh build is the evidence |
| No open review finding on `src/` | **Holds** on the coordinator's record: Defect A, Defect B, the re-anchoring repair and the guard's deletion each passed `review`. One advisory is with `design`(int): the re-anchoring fallback when nothing expanded is unspecified |
| Opaque-`IO` rulings | **Holds**, as §24.4; the `opaque_io` cells pass |
| Every focus-band and hygiene-band filing disposed | **Holds**, as §25; FIXME 0863 is since deleted |
| No decay | **Holds, on §31.2's repair.** Nothing fails that passed at the opening except new reproductions of defects the sprint did not cause, and that pin |

**For the user to accept:**

1. **1087 and 1090**, the settling target's named exceptions, unchanged.
2. **Stack exhaustion is not reported as a runtime panic** (§29.2):
   carried on T-STACK's five cells; repair unscheduled.
3. **A reused poll-shape leaf does not repeat its work** (§28.2): carried
   on T-POLL-REUSE's two cells; repair unscheduled.
4. **The residuals of §26.3,** as accepted, and the limits of §29.1.
5. **S125-Q12** is open: whether a non-overflow trap in a macro clause may
   end the process on its signal.

**Not evidenced by this run:** `qa` did not read Defect A's and the
re-anchoring repair's source or module rows; their adequacy rests on
T-ARG-SCOPE's eight cells red then green, `review`'s record and this run.

**Bands set:** REPL §1.5.1 (T-RESID-DISPLAY); spec §8.6.1 (T-ARG-SCOPE);
spec §9.3.4's heading (S125-Q4's twelve cells and 1100's, all passing).

**Before close:** `test` repairs §31.2's pin and §31.3's comment, and
`qa` reads that cell green.

### 31.5 Closed

`test` repaired §31.2's pin to `13 passed in` and replaced §31.3's
comment with the T-NARROW leg's present state. `qa` read both and ran
`regression::s60_run_tests_reduction_1_exemplar_batched_failing` alone:
passed.

**Final verdict: the Phase 6b settling target holds.** The failing set is
89: §31.1's table with the maintenance row at 1, the document gate. No
failing test is attributed to `src/` but 1087 and 1090, and no cell fails
that the sprint caused. The items of §31.4 are the user's to accept at
the Phase 7 checkpoint.
