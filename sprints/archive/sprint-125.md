# Sprint 125: The binary clean and green, and debt paydown

**Status**: CLOSED 2026-11-28 (Phase 7)

**Goal**: Make `src/` clean and green — its crashes, data loss and the opaque
`IO` ruling delivered — and verify and dispose a cross-module batch of open
filings.

**Audit**: `cranelisp-intrinsics` (approved 2026-11-26; longest unassessed,
last S115). Read-only in the Phase 6/7 window; ACT-0969 supplies its
predecessor observation.

## Phase approvals

| Transition | Checkpoint presented | User approval | State |
|---|---|---|---|
| Start → Phase 1 | "frame the next sprint … what is the focus module?" | 2026-11-26 | approved |
| Phase 1 → Phase 2 | scope draft: `src/` focus band, opaque `IO`, hygiene band | 2026-11-26, "advance to phase 2" | approved |
| Phase 2 → Phase 3 | `arch` sign-off: IO-T, TR-1, D-1 approved; B18 and ACT-1087 decisions; scope adjustments; S124-Q19 reframing | 2026-11-26, "agree with the ruling; advance to phase 3 with recommendations. let's deal with trace when builtins and primitives are our focus module" | approved |
| Phase 3 → Phase 4 | designs (int, typecheck, backend), rewritten row IO-T, spec rulings S124-Q19 and S125-Q1–Q6, `qa` readiness with the 1079 condition met; open: S125-Q5-R1 and the reload-drops-the-call case (both since ruled) | 2026-11-26, "approved to move to phase 4" | approved |
| Phase 4 → Phase 5 | wave plan W0–W9 + WG; audit `cranelisp-intrinsics` proposed | 2026-11-26, "yes" (waves, audit and advancement) | approved |
| Phase 5 → Phase 6a | W0–W9 + WG delivered; `src/` clean and green less 1087/1090; seven residuals, S125-Q10/Q11 and close items put to the user | 2026-11-27, "2 approved" | approved |
| Phase 6a → Phase 6b | six assessments; no new compiler defect; exemplar 404 escaping defect; audit F1–F5 with dispositions; deferrals | 2026-11-27, "don't defer the IO lessons now we've changed the developer surface. otherwise agreed" | approved |

**Phase 5 checkpoint rulings (user, 2026-11-27; advancement not yet approved):**

- Residuals (a)–(g): "accept".
- S125-Q10: "(mod q) after (import [q]) should be an error ambiguous import." Recorded by `spec` (§8.11.2.1); implementation carried to S126 on ACT-0995 (re-targeted to `design`). Companion S125-Q10-R1, "1 agreed": no root-addressing form (the user removes the collision); a refused turn keeps no proposed child declaration.
- S125-Q11: "defer as long as there is an action." Deferred to ACT-1009.
- Exe-bundle baseline: "ensure this is consistent and checked." Done: `arch` regenerated the baseline (+1 `runtime_switches`, S123-approved) and updated `design/arch/`; `test` guards all eight baselined crates and rejects an unlisted baseline (4/4 green, +0 drift); `qa` classified it as a maintenance check (delta §26).
| Phase 6b → Phase 7 | 6b outcome; F2/F3, the binary guard, Defects A and B repaired; full run 89 failing, `src/` 1087/1090 only; robust-primitives ruling; timer-leaf carried; close operations 1–3 (records, commits, archive) | 2026-11-28, "yes" | approved |

## Phase 1 decisions (user, 2026-11-26, "proceed with this framing")

- **Focus module: `src/`.** It holds candidate 1 of the
  [roadmap's S125 order](../ROADMAP.md#next-sprint--s125) entirely, 71 of the 143
  failing tests at the S124 close, all three data-loss defects and four of the
  memory-unsafe ones.
- **Opaque `IO` (roadmap candidate 2) is in scope.** It is mostly `src/`;
  defect 1107 (`typecheck/adt.rs`) joins under *clean house*
  ([METHOD §Delivery principles](../METHOD.md)).
- **A cross-module hygiene band is adopted** (below). Whether it becomes a
  standing delivery principle, and its per-sprint size N, is decided at
  Phase 7 from this sprint's measured triage cost.
- **S124-Q19** (§3.2.3 "pure functions MUST NOT return IO" is false of
  `pure`) is ruled by the user in Phase 3; it blocks the opaque-`IO` design.
- **The prior audit is already disposed**: the S124 typecheck audit was
  disposed in-sprint on 2026-11-20 (R1 → defect tests, R2–R5 → ACT-1098,
  R6 → ACT-1097, R7 → `spec`). Phase 1 has nothing to settle there.

## Scope

### Settling target (observable on a fresh build of the final tree)

- `cargo nextest run --no-fail-fast` shows **no failing test attributed to
  `src/`** other than the trace-deferred cells of defects 1087 and 1090,
  `src/` produces no build warning, and no review finding on it is open. Attribution is `qa`'s, against the
  [S124 evidence delta §14.15](../../tests/plan/s124-evidence-delta.md).
- The compiler conforms to the opaque-`IO` rulings of 2026-11-22:
  `primitives/pure` exists, the `IO` constructors are refused in user code and
  in `match`, and the REPL displays nested `IO` and function values as `#io`
  and `#closure` (trace output deferred; see §Architecture review).
- Every filing in the focus band and the hygiene band has a disposition
  recorded after verification against its `refers_to` source.
- No module the sprint touches is left worse (*no decay*).

### Focus band — `src/`, drained

Defects carried by failing tests (identifiers per delta §14.15):

| Group | Defects | Severity |
|---|---|---|
| Persistence (`src/save.rs`, `session_v4/lifecycle.rs`) | 1005, 1068, 1101, 1102 | data loss; 1102 memory-unsafe |
| `/type` (`src/repl/commands.rs`) | 1089, 1099 | 1089 memory-unsafe |
| Display (`src/display.rs`, `styled.rs`) | 1062, 1109 | 1062 memory-unsafe |
| Opaque `IO` (`src/bootstrap.rs`; 1107 typecheck) | 1105, 1106, 1107, 1108 | 1105, 1106 memory-unsafe |
| Module loading and search | 1079, 1092, 1096, 1100 | legal programs refused, wrong values |
| Trace and cache | 1087 (`arch` accepted residual), 1090 | low harm |

Filings attributed to `src/`:

- ACT-0965 (src audit residuals), ACT-1060 (a module test writes `ctx.txt`
  into the checkout), ACT-1093 (strict evaluation in the trace help).
- FIXME 0863 (macro checkpoints and ordered definition results), 0889
  (macro-turn marshal residue). FIXME 0929's remainder is in the hygiene
  band (`qa`).
- `src/`-side REPL filings currently with `spec`: ACT-0995 (later same-named
  child module), ACT-1009 (restore last known good). `spec` frames each for
  the user's ruling or a deferral with rationale.
- Stale citation in `src/platform.rs:555` (S124 close carry).

The band is too large for one wave; Phase 4 decomposes it, it does not carry
on size (METHOD §2.4).

### Hygiene band — verify and dispose, across modules

Each filing is verified against its `refers_to` source first, then: closed
(stale or resolved), converted to a failing test (the test becomes the
record and the action is deleted), re-targeted, or kept with a reason. A
disposition that needs a fix outside `src/` stays carried on its test; it
does not widen the focus band.

- The fifteen `qa` actions no failing test carries, not re-triaged at the
  S124 close: ACT-0962, 0978, 0979, 0982, 0985, 0987, 0994, 1001, 1003,
  1004, 1015, 1022, 1036, 1081, 1085 → `qa`.
- The remaining legacy filings in `design/arch/fixmes/` not in the focus
  band: 0050, 0463, 0694, 0761, 0776, 0783, 0785, 0800, 0811, 0848, 0857,
  0900, 0907, 0915, 0929 (remainder, `qa`), 0933, 0938, 0939, 0942, 0943 → each to its target role
  (`/testing` → `test`, `/stdlib` → `dev` on `stdlib/`, `/examples` →
  `training`).
- Stale source citations from the S124 close outside `src/`:
  `cranelisp-typecheck/src/traits/impl_check/tests.rs:1592`,
  `cranelisp-typecheck/src/checker.rs:960` and neighbours in `builtins.rs`,
  `cranelisp-platform/src/tests.rs:1479`. Comment-only repairs.

The triage is read-only and may fan out in parallel; any edit it leads to
runs serially (root `AGENTS.md` §Testing).

### Exclusions

- Typecheck's other carries (1071, 1073–1076, 1080, 1082, 1097,
  1103, 1104) and ACT-1098 — the natural S126 focus.
- ACT-1112 (`race` to the library), ACT-1054 (checked/unchecked
  arithmetic), the 32 partly covered specification rows (delta §14.14),
  ACT-0962's coverage increment — carried without a date per the roadmap.
- 0977, 1018, 1067 — not attributed to `src/`.
- Trace features — TR-1, ACT-1110, ACT-1111/B18 — until the built-ins and
  primitives are the focus module (user, 2026-11-26).
- LLVM, by user direction.

### External operations

None before Phase 7. Commit, archive and push are proposed there and each
needs its own approval.

## Architecture review (Phase 2)

`arch` signed off 2026-11-26. The working packet is
`sprints/s125-architecture-review.md`; the approved rows are in the batch
table of `design/arch/interfaces.md` (rows IO-T, TR-1, D-1). S124-Q19 changes
no verdict.

User decisions at the Phase 2 checkpoint (2026-11-26):

- **S124-Q19 ruled.** "Pure" in normative text means only that calling a
  function performs no effect — true of every function under §10.8. §3.2.3
  is restated: evaluation never performs an effect; an effect occurs only
  when the runtime executes an `IO` value, so every operation that describes
  an effect has an `IO` result. Where the spec meant "no `IO` in the type"
  (§10.1.2, §10.7 and similar) it says so. `primitives/pure` keeps its name,
  noted in §10.2 as the conventional lift into `IO`. `spec` scribes; `docs`
  aligns `user/` in Phase 6.
- **Trace work is deferred** to the sprint whose focus module is the
  built-ins and primitives: TR-1 (`#io`/`#closure` in trace output),
  ACT-1110 and ACT-1111/B18. Defect 1109 stays in scope for the REPL display
  only; trace output keeps its current markers until then, a known
  divergence from §12.9.1's shared format. `arch`'s approved TR-1 row stays
  in `design/arch/interfaces.md`, unscheduled.
- **ACT-1087 and 1090:** costed by `design`(int), then deferred with trace
  by the user (see the Notes section below); their cells are the settling target's named
  exceptions.
- **Scope adjustments accepted:** FIXME 0929's remainder moves to the hygiene
  band under `qa`; typecheck joins for 1107 (and the 0776 repoints) only; the
  opaque-`IO` migration follows `arch`'s four-step order without step 4
  (trace markers), which is deferred with TR-1.

## Waves (Phase 4)

Source-editing dispatches run one at a time (root `AGENTS.md` §Testing);
read-only and document-only work may overlap. Each implementation wave is
`dev` → independent `review` (Codex) → `qa` adequacy, and closes with its
module tests, evidence and design status together. `dev` dispatches only
against `test` evidence that `qa` has accepted. Build order for opaque `IO`
is `arch`'s (packet §4) without step 4.

| Wave | Content | Roles | Depends on |
|---|---|---|---|
| W0 | Refresh the evidence delta once for everything ruled since `qa`'s plan: strict §9.6.1 (S125-Q5, R1, R2), S125-Q4, REPRO-1079-c, T-0979 now `src/` (focus band), T-MARKERS-TRACE withdrawn with the trace deferral. Plus the mechanical hygiene handoffs (inbound links to closed filings, R8's citation of FIXME 0857, the `stdlib/` `core.io` self-test gate; two stale citations in `arch`'s packet, lines 35 and 156) | `qa`; owners of each handoff | — |
| W1 | All REDs and GREENs of delta §6 as refreshed; IO-0 classification of the 17 identity-naming files | `test` | W0 |
| W2 | Display: 1062 (row D-1), 1109 REPL `#io`/`#closure`. Precondition of W5 | `dev`(`src/`) | W1 |
| W3 | Opaque `IO` step 1: `pure` lowering, then `pure` seeded with `insert_primitive` (additive; `Pure` still public) | `dev`(backend) → `dev`(`src/`) | W1 |
| W4 | Opaque `IO` step 2: every consumer moves from `Pure` to `pure` — tests (2,822 uses, 169 files), stdlib, exemplar, examples, `user/`, platforms. `qa` approves any deletion of a constructor-behaviour assertion | `test`; `dev`(`stdlib/`), `dev`(`exemplar/`); `training`; `docs` — serially | W3 |
| W5 | Opaque `IO` step 3, one change-set: types (`internal` removed), typecheck deletions (1107), backend `ConstrADT` removal and schema walk with cache 36→37, binary constructorless `IO` and bootstrap assertion (RED first), both platform schemas regenerated and rebuilt. 1105–1108 turn green | `dev`(types) → `dev`(typecheck) → `dev`(backend) → `dev`(`src/`) | W2, W4 |
| W6 | `/type`: 1089, 1099 | `dev`(`src/`) | W1 |
| W7 | Persistence: 1068 + 1101 (selector), 1005 (authored order), 1102 (cache agreement), the S125-Q5 refusal (strict identity) | `dev`(`src/`) | W1 |
| W8 | Module loading and search: 1079, 1092, 1096, 1100; ACT-0994, ACT-1085 | `dev`(`src/`) | W1 |
| W9 | `src/` remainder: 1003, T-0979 platform function types, ACT-0965 item 3, the `src/platform.rs:555` citation, the misnamed agent test, the 1092 `{gap:?}` rendering | `dev`(`src/`) | W1 |
| WG | Integrated gate: a fresh build of the final tree, full suite, `src/` clean and green less the two named exceptions; public-API baselines regenerated and compared with rows IO-T and D-1 by `arch` | `qa`, `arch`, `sprint` | all |

W6–W9 have no mutual dependency; they are ordered by harm (memory-unsafe
1089 first) and run one at a time. W2 may run before or after W3.

**Audit (proposed):** `cranelisp-intrinsics` — longest unassessed (S115);
ACT-0969 supplies its predecessor observation. Read-only in the Phase 6/7
window.

## Dispatch log

| Wave | Agent | Surface | Model | Effort | Harness | Outcome |
|---|---|---|---|---|---|---|
| W0 | `qa` | refresh the evidence delta for W1; dispose its gated deletions (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: §6 settled at 21 rows; annotations set for Q19, Q1–Q6 (Q2/Q3/Q6 `[S126]`); FIXME 0857 deleted; deletions of ACT-1004, 1015 (int.md links) and 1022 (backend audit link) held on owners; go for `test` |
| W1 | `test` | delta §6, 21 rows; IO-0 classification | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `932a3a55` | complete: report folded into the S125 evidence delta (W1 acceptance section); sandboxed full run 8,024 / 246 failed / 1 skipped; unexpected: T-NC2 gate RED on two backend fallbacks, PS-3 SIGSEGV; IO-2/IO-5 await W3; spec links clean |
| W1 | `qa` | W1 acceptance, IO-0 approval, W2/W3 go (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: unsandboxed full run 8,271 / 8,037 / 234 failed / 1 skipped = opening 143 + 91 W1 cells, no regression; PS-3 crash is ACT-1102 (W7); T-NC2 sites are the IO special case W5 deletes (allow-listed until then); IO-0 approved with `s99_fixtures.rs` added; go for W2, W3. Note: `qa` ran `rm -rf /tmp/tmp.*` on system `/tmp` while cleaning its probes |
| W1 | `test` | amendments: T-NC2 allow-list + stale-entry leg, `s99_fixtures.rs` ledger row, remove `REPORT.md` | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `464aa776` | complete: targeted 3/3, row 16 GREEN, stale-entry leg proven RED first; report removed |
| W2 | `dev` | `src/`: display — 1062 (D-1), 1109 REPL `#io`/`#closure`, D-3 bare-name `Vec`; delete FIXME 0848 | `claude-opus-5-5` | medium | primary (Claude) | complete: 8 display cells GREEN; 7 unit tests RED→GREEN; full run 8,279 / 225 failed, no product regression; two `test` cells assert the retired `<closure>`; IO-5 box/double wait on W3; FIXME 0848 deleted |
| W2 | `review` | `src/` display change | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `e02a756a` | complete: no findings; 46 display units + 11 targeted REPL cells passed |
| W2 | `qa` | W2 adequacy, leads, W3 go (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: W2 adequate; full run 8,279 / 224 failed, nothing newly failing; bare-name `Vec` sites a lead for a backend/types focus (no wrong outcome observed); `<invalid-string:N>` not a defect; amendment for `test`: PS-3 module cell must assert its cache hit; stale `build_adt_subst` citations for `design`(backend), `arch`, `design`(int); go for W3 |
| W3 | `dev` | backend: `pure` lowering (step 1) | `claude-opus-5-5` | medium | primary (Claude) | complete: `IoCombinator::Pure` + `emit_pure_node` (typed glue); direct and first-class CLIF identical; `emit_bind_node` uses `IO_TAG_BIND`; backend 540/540, no warnings; full run 8,281 / 225 failed (+1 most likely the run-dependent PS-3 module cell) |
| W3 | `dev` | `src/`: seed `primitives/pure` (step 1) | `claude-opus-5-5` | medium | primary (Claude) | complete: `register_pure_primitive` (HostPromised); unit RED first; 31 IO-2 + 2 IO-5 cells GREEN; full run 8,282 / 187 failed, none new; IO-5 double-`pure` display RED in `src/result_owner.rs` (predates the seed) → `qa` |
| W3 | `review` | backend `pure` lowering | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `a5f7e39d` | complete: no findings; 5 targeted tests passed; no inter-crate change |
| W3 | `review` | `src/` `pure` seed | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `19095666` | complete: one nit — `mounts_pure_as_host_promised_lift` lacks `// spec: spec/10-io.md §10.2` (→ `dev`(`src/`) with the next `src/` dispatch); no blocking or required findings |
| W3 | `qa` | IO-9, re-read IO-2/IO-5, attribute double-`pure` display (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: W3 adequate; IO-9 node identical (call site inline vs GOT — wording fix for `design`(backend)); 30 IO-2 + twice-forced + box/vector credited; full run 8,282 / 187 failed = 224 − 37, nothing new; double-`pure` display attributed to `src/result_owner.rs` (`check-domain-overreach`, design first) |
| W3+ | `design` | `src/` (int): result-owner change for `IO`-typed payload; stale citations (resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: `s125-binary-clean.md` §3.3 — `ReleasePlan::new` takes the static type and unwraps once itself; `is_io` refusal deleted; payload released by normal `GlueShape::Io` glue; no gate item; unit row named (RED first); ACT-1004/1015 links removed from `int.md`. Queued for `dev`(`src/`) after W4's `test` dispatch, with the `// spec:` nit |
| W4 | `test` | step 2: migrate tests from `Pure` to `pure`; two amendments | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `1c0f9527` | complete: 166 files, `Pure` 2,737 → 41 (classified); no assertion deleted; amendments done; full run 8,282 / 193 failed = 187 + 7 golden-CLIF checks − 1 run-dependent 1090 cell; s99 rewrite proposed, not applied; evidence in /tmp/s125-test-w4/ |
| W4 | `qa` | s99 proposal, golden-CLIF rebaseline disposition, failing-set reconciliation (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: failing set = W3 + 7 golden checks − run-dependent 1090; no assertion deleted; s99 rewrite approved; scoped golden re-baseline of 19 entries approved (three allowed hunk kinds, double capture, W0.b manifest corrected; maintenance class). Queued for `test` after `dev`(`src/`) releases the runs |
| W3+ | `dev` | `src/`: result-owner `IO` payload (§3.3); `// spec:` nit; stale comment | `claude-opus-5-5` | medium | primary (Claude) | complete: owner takes the static type and unwraps once; `is_io` refusal deleted; 3 unit rows RED→GREEN; e2e double-`pure` GREEN; full run 8,284 / 193 failed — set swap: double-display now passes, run-dependent 1090 cell fails again; `src/AGENTS.md` bullet corrected |
| W3+ | `review` | `src/` result-owner change | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `f86888d2` | complete: no findings; 29 targeted unit tests passed. `design`(int) folds the delivered change into `result-owner.md` (held for its next dispatch) |
| W4 | `test` | s99 rewrite; scoped golden-CLIF re-baseline (19 entries) | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `8fb3d11a` | complete: s99 rewritten as approved; 19 goldens re-captured, double captures identical, hunks within the three allowed kinds; W0.b manifest corrected; 24/24 focused GREEN |
| W4 | `qa` | tests-part adequacy, full run, remaining-consumer list by owner (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: tests part adequate; full run 8,284 / 186 failed = W3 set − double-display; census: stdlib 11 (non-mechanical `pure` definition), exemplar 3, examples 127 (re-teaching), user/ 29 (prose), repl demos 27 + one platform comment (`test`) |
| W4 | `dev` | `stdlib/`: re-export `primitives/pure`, migrate lifts | `claude-opus-5-5` | medium | primary (Claude) | complete: `io.monad/pure` deleted, prelude re-exports `primitives/pure`; `core.io` lifts migrated; one identity shown by probe (ambiguity gone); full run 8,284 / 186 failed, same set verified by revert |
| W4 | `review` | `stdlib/` change | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `dbf9ea51` | complete: no findings; probes confirm one identity, direct and first-class lifts, combinators; missing module self-tests are pre-existing |
| W4 | `dev` | `exemplar/`: migrate 3 uses | `claude-opus-5-5` | medium | primary (Claude) | complete: 4 uses in 3 files (census missed `user.cl`'s unused import); exemplar runs exit as expected; full run 8,284 / 186 failed, identical set. Review not dispatched: mechanical import and lift change, covered by the exemplar cells |
| W4 | `training` | `examples/`: re-teach opaque `IO`, migrate 127 uses | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `50f69cae` | complete: example 21 re-taught (opaque `IO`, `pure`, deferred effects, `bind`), example 01 and the 01–19 comments updated; 42 files; no `Pure`/`Effect`/`Bind` left; `examples` lane 7/7 |
| W4 | `docs` | `user/`: opaque `IO` prose, 29 uses, S124-Q19 terminology | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `57a3fc0d` | complete: 5 files; constructor prose reworded; Q19 passages fixed; no `Pure`/`Bind` left (`Effect` only as table headings); `user_samples` 22/22; checker clean in `user/` |
| W4 | `test` | REPL demos (6 files, 27 uses) and one platform comment | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `2b6ec58a` | complete: 41 replacements in 6 demos (incl. `ring4j`) and the poll-pool comment; all six replay; focused 20/20; transcripts git-ignored |
| W4 | `qa` | close W4: full run, constructor census, single-`pure` test verdict, W5 go (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: W4 closed; full run 8,284 / 186 failed, same set; remaining constructor uses are W5's targets and the deliberate refusal cells; T-PURE-ID allocated (maintenance, GREEN, for `test`); the W1 fixture ledgers deletable; go for W5 |
| W5 | `dev` | types: remove the `internal` flag (surface 1 of 4) | `claude-opus-5-5` | medium | primary (Claude) | complete: delta matches row IO-T (−2, 1 changed); types 303/303; downstream checklist produced; cache bump left to backend as the row places it |
| W5 | `dev` | typecheck: opaque `IO` deletions, 1107 (surface 2 of 4) | `claude-opus-5-5` | medium | primary (Claude) | complete: gates, flag and exhaustiveness exclusion deleted; fixture constructorless; 6 unit rows RED first; typecheck 997/997; four design docs and crate guidance updated; stale gate-function citations in two `qa` deltas and `arch`'s packet |
| W5 | `dev` | backend: `IO` `ConstrADT` removal, schema walk, cache 36→37 (surface 3 of 4) | `claude-opus-5-5` | medium | primary (Claude) | complete: special case and its inputs deleted (both T-NC2 sites gone); `abi_layout_args` treats `IO` like `Vec`; cache 37; IO-6 and IO-7 rows RED first; `Pure` write census with detection proof; backend 543/543; design citations and IO-9 wording fixed |
| W5 | `dev` | `src/`: constructorless `IO`, IO-8, regenerate both platform schemas (surface 4 of 4) | `claude-opus-5-5` | medium | primary (Claude) | complete: `IO` constructorless; IO-8 RED→GREEN; both schemas regenerated (IO entries gone, user entries byte-identical), dylibs rebuilt and load; workspace builds, no warnings; run excluding `platform_schema_roundtrip` 8,277 / 163 failed; all 77 `opaque_io` GREEN; new REDs are test-side follow-ups and expected API drift; `result-owner.md` updated |
| W5 | `qa` | disposition of three `spec_10_io` `Pure`-pattern cells (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: retire `pure_pattern_accepted` and the exhaustiveness-exclusion cell (duplicated by IO-1 and 1107); rewrite `match_arms_all_io_pure` on a non-IO scrutinee, keeping §10.7.2 |
| W5 | `test` | compile fix, census entries, retire legs, three `spec_10_io` cells, T-PURE-ID, delete W1 fixtures | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `4e3a52b8` | complete: all six items; targeted 395 / 7 failed, all carried (1075 ×3, 1018 ×4); no other assertion removed; W1 fixtures deleted |
| W5 | `qa` | full run, set comparison, IO re-reads, W5 adequacy (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: W5 adequate subject to review; full run 8,281 / 157 failed = 186 − 30 (21 IO-1 + 9 opaque-`IO` subjects for 1105–1108) + 1 expected public-API drift; Sudoku cell is the ACT-1018 guard; IO-1, IO-6, IO-7, IO-8 re-read; §3.2.3, §10.1–§10.2.3 re-banded; §12.7.2.1 non-exhaustive-match row now unreachable (→ `spec` question) |
| W5 | `dev` | backend: census truncation fix + detection leg; repoint 8 test comments | `claude-opus-5-5` | medium | primary (Claude) | complete: stripping keeps production code after a test module; new leg RED on the old census, GREEN now; backend 543/543; no backend file cites the retired record |
| W5 | `review` | finding-scoped re-review of the census correction | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `a53de07c` | complete: resolved, no new finding; residual — a column-0 `}` inside a test raw string ends stripping early (fails loud by over-counting; not carried). **W5 closed** |
| W6 | `dev` | `src/`: `/type` — 1089, 1099 | `claude-opus-5-5` | medium | primary (Claude) | complete: `/type` expands, refuses definitions and multi-form input, checks without commit (`type_query.rs`); 6 unit rows RED first; 1089 ×14, 1099, TY-2..5 GREEN; full run 8,286 / 140 failed; ran a workspace `cargo fmt` that reformatted 29 `tests/` files and `result_owner.rs` (whitespace) |
| W6 | `review` | `src/` `/type` change | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `b9b7d7b3` | complete: one required finding — `/type` propagates build and typecheck errors without the expansion-diagnostic re-anchoring (`parse error at 1000024..1000024` vs `0..5` on evaluation); first review round, so fixed this sprint (→ `dev`(src) after `qa`'s run) |
| W6 | `qa` | W6 adequacy, set comparison, fmt check, W7 go (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: full run 8,286 / 141 failed = 157 − 17 + 1 (run-dependent 1102 ghost-restore cell, W7's); `cargo fmt` changed no semantics; correction evidence: `dev` unit row RED first + T-TY-LOC e2e pair (RED now); W6 closes on those and a clean re-check; then go for W7 |
| W6 | `test` | T-TY-LOC (RED first) | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `c929755d` | complete: two cells RED on the intended clause (`/type` 1000024 / 1000030 vs evaluation 0..5) |
| W6 | `dev` | `src/`: re-anchor `/type` expansion diagnostics (review correction, resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: both paths reuse the evaluated turn's re-anchoring; unit test RED first (parse and type cases shown separately); T-TY-LOC GREEN; W6 cells 29/29 |
| W6 | `review` | finding-scoped re-review of the anchoring correction | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `abf2c96e` | complete: resolved, no new finding. **W6 closed** |
| W7 | `dev` | `src/`: persistence — 1068, 1101, 1005, 1102; §9.6.1 refusal | `claude-opus-5-5` | medium | primary (Claude) | complete: §4.1–§4.4 built (departures in §4.5); 23 cells GREEN; full run 8,306 / 119 failed; 2 new REDs — a control whose premise was 1101, and a cached-restart narrowing refusal now reached via 1068; gap: cache-restored modules lack authored records until first regeneration |
| W7 | `review` | `src/` persistence change | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `0ba03b4b` | complete: four findings — (1) blocking data loss: a `begin` holding a macro call and a redefined sibling is written twice, restart locks; (2) blocking: macro checkpoints publish before `finalize_cluster`, bypassing the §9.6.1 refusal; (3) split `begin` members lose authored order; (4) pre-existing: imports merged and platforms alphabetical (rule 4). First review round: 1–3 fixed this sprint; 4 needs disposition → `qa` |
| W7 | `qa` | W7 adequacy, classify two REDs and the cached-module gap (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: not yet adequate — R1–R4 owed; full run 8,306 / 119 = 141 − 24 + 2; control re-seed for `test`; the cached-restart refusal is a pre-existing typecheck narrowing defect (T-NARROW, carried to the typecheck sprint); cached-records gap a named residual (unreachable by user command); evidence allocated |
| W7 | `spec` | record the authored-entry ruling (repl §15.4) | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `5f1e1742` | complete: S125-Q7 closed; §15.4, §15.6, §18 changed; S125-Q8 opened (file `begin` vs §9.6) |
| W7 | `spec` | S125-Q8 and the shrinking re-entry refusal | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `41af23e8` | complete: Q8 and Q9 closed; §9.6.1 refusal added; §15.4/§15.6/§18 limit dissolution to REPL input; checker clean on edited files |
| W7 | `design` | `src/` (int): redesign §4.2 on authored entries (resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: entry model in §4.2; split path deleted (R1, R3 by construction); six unit rows; ~8 tests to re-baseline; raised the shrinking-set residual |
| W7 | `design` | `src/` (int): fold Q8 and the shrink refusal (resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: REPL-only dissolution; legacy file `begin` kept as §9.6 SHOULD leniency (refusal flagged as a separate change); shrink refusal once per entry before any publication; unit rows and re-baselines listed |
| W7 | `qa` | refresh §17 allocation for the entry model (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: §18 — R1–R4 cells extended, three re-baselines, new T-Q9 (subject RED, two controls GREEN); §15.4/§15.6/§18/§9.6.1 bands set; go for `test` then `dev` |
| W7 | `test` | §18: extend R1–R4, re-baselines, T-Q9 | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `8313adf0` | complete: 9 RED on their clauses, 3 GREEN (`s124_1005_a_begin` and both T-Q9 controls) |
| W7 | `dev` | `src/`: entry model, R4, R2 checkpoint refusal, Q9 shrink refusal | `claude-opus-5-5` | medium | primary (Claude) | complete: split path deleted; R1–R4 and T-Q9 GREEN (22/22 targeted); 15 unit rows RED first; full run 8,330 / 120 failed (+2 T-NARROW carried, +1 re-seeded control passing); residual: an expansion interrupted by a dependency gap records resumed products as `Written` (predates) |
| W7 | `review` | finding-scoped re-review of R1–R4 and Q9 | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `d951e6ca` | complete: R1–R4 and Q9 resolved (37 targeted pass); new blocking R5 — a macro call that regenerates a previously written name keeps two positions, is saved twice, restart locks. Data loss, so fixed now under the stop rule (→ `qa` evidence, `test` RED, `dev`) |
| W7 | `qa` | W7 adequacy after the correction (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: §18 all GREEN; full run 8,330 / 120 = 119 + 2 T-NARROW − 1 control; resumed-expansion residual did not reproduce, named with falsifier; R5 classified `partial-record-update`, semantics confirmed (the call owns every key at its own position); evidence allocated; W7 closes on R5 |
| W7 | `test` | R5 RED (subject, second leg, control) | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `2ae76b6b` | complete: subject and second leg RED on "`(two)` exactly once"; control GREEN |
| W7 | `dev` | `src/`: R5 — the macro call owns its keys at one position (resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: `install_authored` gives a key joining from another entry the call's position; unit row RED→GREEN; R5 cells GREEN; targeted 48/48; design citations repointed |
| W7 | `review` | finding-scoped re-review of R5 | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `0dd26387` | complete: R5 resolved, no new finding; 46 targeted pass |
| W7 | `qa` | close W7: full run after R5 (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: full run 8,334 / 120 failed, identical to §19.1; R5 cells GREEN; carried: T-NARROW (typecheck), two named residuals. **W7 closed** |
| W8 | `dev` | `src/`: module loading and search — 1096, 1079, 1092, 1100; ACT-0994, ACT-1085 | `claude-opus-5-5` | medium | primary (Claude) | complete: all six built, unit rows RED first; full run 8,360 / 92 failed (29 fixed incl. T-OWNER); one regression found and fixed in-pass (owner = referrer cycle); newly failing `stdlib_module_compiles_and_runs` asserts what §8.2.5 now refuses; residuals: no dependency `.meta` path in the index, contender private dir left on skipped shutdown |
| W8 | `review` | `src/` module loading and search | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `f6d26472` | complete: two required findings in 1092's private indexing — a publication between snapshot and check marks a module indexed without rows (concurrency); an empty import triggers dependency resolution (§8.3.7). No data-loss or memory-safety finding. First round: fixed this sprint |
| W8 | `qa` | W8 adequacy, classify leads, dispose ACT-0994/1085 (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: not yet adequate (F1, F2); full run 8,360 / 92 = 120 − 29 + 1; leads classified — (a) re-baseline, (b) T-OWNER fixture race (provisional), (c)–(e) departures/residuals, (f) stale locus prose; ACT-0994 closed and deleted; ACT-1085 kept until T-OWNER's fixture repair |
| W8 | `test` | F2 RED, (a) refusal + positive, (b) T-OWNER fixture, (f) locus prose | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `f01c7677` | complete: F2 RED, control GREEN; library-only root positive GREEN (exit 55); refusal cell RED — diagnostic omits the expected `main/helper.cl`; T-OWNER fixture settles before snapshot, 3/3 passes; locus prose added |
| W8 | `dev` | `src/`: F1 read order, F2 `names_load`, refusal names expected file (resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: three unit rows RED first; F2 and refusal cells GREEN; full run 8,366 / 91 failed — exactly §21.1 less `stdlib_module_compiles_and_runs` |
| W8 | `review` | finding-scoped re-review of F1, F2 and the refusal message | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `d3da89e6` | complete: F1, F2 resolved, refusal verified; no lock-ordering, release-hook or lost-deferral defect |
| W8 | `qa` | close W8, dispose ACT-1085 (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: full run 8,366 / 91 = §21.1 − 1; ACT-1085 closed (deletion waits on `int.md` ~4323 link, `design`(int)); residuals carried. **W8 closed** |
| W9 | `dev` | `src/`: 1003, T-0979, ACT-0965 item 3, `platform.rs` citation, misnamed agent test, delete ACT-1060 | `claude-opus-5-5` | medium | primary (Claude) | complete: all six; unit rows RED first; T-1003 and T-0979 cells GREEN; full run 8,377 / 83 failed; ACT-0965 item 3 partial (no named-error-on-miss without a backend API change) but the action was deleted — remainder disposition with `qa`/`arch`; `load_cached_module_via_linker` 199 lines → `design`(int) |
| W9 | `review` | `src/` W9 change | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `4e9cbc53` | complete: three required — ACT-0965 remainder closed without disposition (→ `qa`/`arch`); `load_cached_module_via_linker` budget unmet (→ `design`(int)); `sconcat` export test passes when the export is missing (→ `dev`) |
| W9 | `design` | `src/` (int): linker-loader budget decision; ACT-1085 link (resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: decompose into five steps (new §7.1); behaviour unchanged, pinning unit rows; ACT-1085 links removed and stale §7.7 status corrected |
| W9 | `qa` | W9 adequacy, ACT-0965 remainder (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: full run 8,377 / 83 = §22 − 8 (T-0979 ×6, T-1003 ×2); only `src/` REDs are 1087, 1090; ACT-0965 remainder an accepted residual (one map makes divergence structural; miss only from a build-config fault; falsifier named); W9 closes on the parity-test repair; go for WG |
| W9 | `dev` | `src/`: parity test non-vacuous; decompose `load_cached_module_via_linker` (§7.1) (resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: parity helper requires a real address, detection leg added; loader split into five steps (one symbol walk; no slot written on a failed restore); three pinning rows, one proven by reverting; full run 8,381 / 83 failed, same set |
| W9 | `review` | finding-scoped re-review of the parity test and the decomposition | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `a76d9b2b` | complete: both resolved, no new finding. **W9 closed — focus-band language work complete** |
| WG | `arch` | regenerate public-API baselines, compare with IO-T and D-1 | `claude-fable-5-2` (allocated) | medium | primary (Claude) | complete: clean — types −2/1 changed (IO-T), all other guarded crates +0, withdrawn and deferred items absent; `public_api_relocations` 4/4; noted a stale unguarded `cranelisp-exe-bundle/public-api.txt` (S123, not S125) for a close-time item |
| WG | `qa` | fresh build, full run, settling-target verdict | `claude-fable-5-2` (allocated; Opus substitution ended) | medium | primary (Claude) | complete: fresh build, no warnings; full run 8,381 / 82 failed = W9 set − public-API check; `src/` REDs only 1087, 1090 (1082 counted to typecheck, provisional); suite/build/review clauses hold; filing clause does not — six hygiene FIXMEs undisposed, two stale citations, ACT-0995/1009 unframed, FIXME 0863 item 1 partial |
| WG+ | `design` | int: verify FIXME 0933 (focus band, missed at Phase 1); drop ACT-1081 link (resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: the refusal already holds (`install_platform`'s `SlotMint(NotConcrete)`); only the message is wrong — designed an actionable message (§7); ACT-1081 link dropped |
| WG+ | `dev` | `src/`: FIXME 0933 platform type-variable message (resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: `platform_install_error` quotes the written signature; unit row shown RED by disabling the branch; 45 platform units + 39 e2e pass; FIXME 0933 deleted |
| WG+ | `review` | `src/` FIXME 0933 change | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `ceb8bf43` | complete: no findings; extraction preserves install order and other error paths |
| WG+ | `qa` | final pass: 0863, deletions, 0929, link, full run, verdict (resumed) | `claude-fable-5-2` | medium | primary (Claude) | complete: settling target holds; fresh build no warnings; full run 8,383 / 82 failed, identical set; 8 filings deleted; 0863 narrowed to T-0863 (`test`); 0929 narrowed to `lenient_from_expr`, retargeted `arch`; go for the Phase 5 checkpoint |
| WG+ | `arch` | close two FIXME 0933 lines in arch docs (resumed) | Claude Opus | inherited | primary (Claude) | complete: open point removed from `platform-interface.md`; `total-concreteness.md` §3.5 states the mint-time rule and why there is no parse-side check |
| WG+ | `design` | backend: verify and dispose FIXME 0915 (resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: backend half resolved (prefix, subject, `0..0`); internal-subject presentation needs an inter-crate carrier → retargeted to `arch`, trigger when the binary's half is scheduled; two stale backend design passages corrected |
| WG+ | `arch` | regrade R18; drop ACT-0979 link (resumed; spawned on Opus) | Claude Opus | inherited | primary (Claude) | complete: R18 now asserted-with-a-named-falsifier (census measured, one allowed site); FIXME 0929 stays open narrowed to `lenient_from_expr` (→ `qa`; allow-list entry should cite it); ACT-0979 link dropped and the sentence now states the enforced rule (`refuse_function_types`, spec §10.10.1) |
| WG+ | `dev` | `stdlib/`: verify FIXME 0800 | `claude-opus-5-5` | medium | primary (Claude) | complete: keep, narrowed to face 3 (calling a stored function value directly; user-deferred API choice, plan-stdlib §6.1); faces 1–2 hold. Follow-ups for Phase 6b: narrow the filing and fix `stdlib/defs.cl:43` (`dev` stdlib), correct `repl/demos/AGENTS.md:53-56` (`test`) |
| WG+ | `dev` | verify FIXME 0050 (display) | `claude-opus-5-5` | medium | primary (Claude) | complete: kept deferred — protocol still unbuilt; trigger: a sprint takes the display protocol, starting with `arch`'s review of `TypeDefInfo.render` and `DescriptorKind::Collection` |
| WG+ | `training` | verify FIXME 0463 | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `a7ebcca5` | complete: keep — no shared socket/client platform or harness client driver exists; trigger recorded in `examples/plan-examples.md` |
| WG+ | `test` | FIXME 0900; 1082 locus alignment | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `7040962e` | complete: cell #15 locus now a seam form; 1082 locus aligned to `resolve_qualified`; FIXME 0900 deleted (numeric mentions only remain) |
| WG+ | `spec` | frame or dispose ACT-0995, ACT-1009; drop ACT-1081 link | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `d678a331` | complete: framed S125-Q10 (later child declaration vs an earlier import) and S125-Q11 (restore last known good); both actions open awaiting user rulings; ACT-1081 link dropped |
| W7 | `test` | REDs for R1–R4, control re-seed, T-NARROW | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `0419f429` | complete: 6 `s125_w7_*` cells RED on their clauses; T-NARROW RED ×2 with GREEN controls; re-seeded control GREEN |
| W7 | `design` | `src/` (int): R2 checkpoint refusal, R4 authored import/platform order (resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: §4.6 — R2: one per-key check before both publication points (`compile_macro_if_needed`, `finalize_cluster`), rebuild fact moved to `AttemptFacts`; R4: one import form per spec in table order, no sort, ~40 lines removed, no public change; residual: a multi-spec import form saves as one form per spec (grouping not kept) |
| W6 | `design` | backend: delete the retired `s125-opaque-io.md` | `claude-opus-5-5` | medium | primary (Claude), resumed | complete: no inbound link; file and index row deleted; `sprint` dropped the declaration |
| W5 | `review` ×4 | types, typecheck, backend, `src/` (one per surface, read-only, parallel) | Codex `gpt-6.1-sol` | medium | `codex_role.py` | types (f9c37d76) complete: delta matches IO-T, one nit — `check.rs:211` still mentions the removed internal flag (→ `arch`: fixed, with the `interfaces.md` and packet citations; checker clean on its files); typecheck (2363090e) complete: no implementation defect, one required doc finding — `io-types.md` still frames Q6 as open (→ `design`(typecheck): fixed in `io-types.md`, `adt.md` §6 and a new `typecheck.md` §12 S126 entry; checker clean); backend (51ee3f47): no runtime finding, two required — the `Pure` write census truncates production code after an inline test module (→ `dev`(backend) after `qa`'s run, with a detection leg), and standing backend designs describe the deleted mechanism (→ `design`(backend): fixed — `io-trampoline.md`, `non-concrete-release-contract.md` §5.3, `compile-to-module.md` §12.1, `lenient-eval.md` §2.4, `backend.md`; `s125-opaque-io.md` retired to anchors-only until 8 test comments and one delta link are repointed); `src/` (2320482d): no findings, schema hashes independently recomputed |
| W2 | `test` | migrate two `<closure>` assertions | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `abb06705` | complete: both verified against §12.9.1 / repl §1.5, migrated to `#closure`, 2/2 GREEN |
| W0 | `arch` | R8 citation of 0857, packet citations (resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: R8 cites the eight detection triplets and records three limits (release build unmeasured); packet lines 35 and 156 repaired; checker clean on its files; FIXME 0848 resolvable → `dev` deletes it with its first `src/` dispatch |
| P2 | `arch` | architecture review, `arch` hygiene FIXMEs | `claude-fable-5-2` | medium | primary (Claude) | stopped 2026-11-26: Fable usage limit (HTTP 429) before any edit; resume the same agent after the reset |
| P2 | `arch` | architecture review, `arch` hygiene FIXMEs | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: signed off for Phase 3; IO-T, TR-1, D-1 approved; two decisions escalated; FIXMEs 0783, 0938, 0942, 0943 resolved and deleted, 0776 resolved pending two design(typecheck) repoints, 0939 kept to Phase 7. Edits verified in the tree |
| P3 | `spec` | S124-Q19 ruling, "pure" terminology | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `69a2dd99` | complete: Q19 closed in appendix D; 8 spec files reconciled, annotations untouched; `user/` list (getting-started 195, 312; concurrency 61, 71, 381) → `docs` Phase 6; checker shows no findings in edited files. Verified in the tree |
| P3 | `design` | `src/` (int) focus band | `claude-opus-5-5` | medium | primary (Claude) | complete: `design/int/s125-binary-clean.md` (declared in `int-current-designs` by `sprint`); every item designed; IO-T step 3 held on falsifier 2 (platform schema walk) → `arch`; `pure` seeding shape matches typecheck's; 1087 costed (~150–250 lines, no API change; recommends named exception); ACT-1060 already fixed at `8667a868`; 0863 item 1 and 0889 → retarget to `qa`; four non-blocking `spec` questions |
| P3 | `design` | `cranelisp-typecheck`: IO-T side, 0776 repoints | `claude-opus-5-5` | medium | primary (Claude) | complete: `Pure`-by-identity assumption confirmed (with a required `pure` seeding shape, relayed to `design`(int)); IO-T "every spelling" claim refuted for the dotted and scrutinee-picked paths → `arch`; wildcard match on `IO` → user ruling; 0776 repointed. Verified in the tree |
| P3 | `arch` | IO-T visibility operation (correction to row IO-T) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: both leads verified; corrected IO-T approved, no user escalation — `ResolutionScope::resolve_member` added (types +4/−2/2 changed); platform schema walk treats `IO` like `Vec`, shapes and web schemas regenerate in step 3; new staging falsifier; FIXME 0776 deleted |
| P3 | `design` | typecheck: fold `resolve_member`, staging falsifier | `claude-opus-5-5` | medium | primary (Claude), same agent resumed | stopped: staging falsifier fires as written (three `current_module` switch sites); consequence argued to hold by acyclicity → `arch` ruling; fold pending |
| P3 | `arch` | rule on the staging falsifier (same agent resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: option (a) — `resolve_member` reads only the scope's own views; falsifier restated on acyclicity, graded asserted-with-a-named-falsifier (residual carried into Phase 4); baseline unchanged (types +4/−2/2) |
| P3 | `design` | typecheck: fold `resolve_member`, check REPL redefinition paths (same agent resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: `resolve_member` folded into `io-types.md` and `typecheck.md` §12; REPL paths checked (staged entries, redefinition replay, `/type`, inline children) — none refutes the falsifier; wildcard-match question still with the user; checker clean |
| P3 | `design` | `src/` (int): fold corrected IO-T | `claude-opus-5-5` | medium | primary (Claude), same agent resumed | complete: schema walk, both schema regenerations, `pure` shape and `ctor_shape` folded into `s125-binary-clean.md` §1.1–§1.4; step 3 is one change-set (types, `src/`, typecheck, `dev`(backend) schema walk + cache bump, both platforms); checker clean under `design/int/` |
| P3 | `arch` | assess zero-constructor `IO` against row IO-T | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: recommended and approved — `IO` has no constructors; `pure` a host-promised built-in like `bind`; `ConstructorAccess`, `resolve_member` and the staging residual withdrawn (user-type private constructors verified refused by probe); refusal now structural; types baseline −2/1 changed; cache +1 |
| P3 | `design` | `src/` (int): revise for zero-constructor `IO`; mark trace deferrals | `claude-opus-5-5` | medium | primary (Claude), resumed | complete: §1 rewritten (constructorless `IO`, `pure` via `insert_primitive`, bootstrap assertion to be shown RED first); 1087, 1090, ACT-1093 marked out of S125; checker clean |
| P3 | `design` | typecheck: revise for zero-constructor `IO` | `claude-opus-5-5` | medium | primary (Claude), resumed | complete: `io-types.md` rewritten, `typecheck.md` §12 updated; `IO` constructor set empty, `pure` a `BuiltinFn`, no resolution path changes; ownership treats `pure` as ⊤ (unchanged behaviour); checker clean |
| P3 | `design` | `cranelisp-backend`: `pure` lowering, `IO` `ConstrADT` removal, schema walk | `claude-opus-5-5` | medium | primary (Claude) | complete: the backend W5 working design (delivered, then retired; its rules now in `io-trampoline.md` §1.5/§2.1 and `non-concrete-release-contract.md` §5.3); `pure` a fifth inline IO combinator, byte-identical to today's `(Pure e)`; schema walk treats `IO` like `Vec`, cache 36→37; `pure` not sparked; no gate item; traced `IO` text changes at step 3 (both forms nonconforming, TR-1 deferred); §10.2.3 "partially applied" is vacuous for a one-argument `pure` → `spec` |
| P3 | `qa` | evidence plan, readiness, constructor-less `match` count (same agent resumed) | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: ready for Phase 4 on one condition (1079 scope — settled above); plan IO-0…IO-9 and per-area conditions with evidence classes; 18-row settled delta for `test` (§6); IO-0 migration (2,822 `Pure` uses in 169 test files) to be its own wave; 0694 deleted; T-1036 RED (backend cache schema, not `src/`); T-1081 all GREEN; `match` census 92 test forms, 0 in examples/stdlib/exemplar, none on `IO`; ACT-1060 verified fixed |
| P3 | `design` | `src/` (int): fold Q5-R1 and reload rulings into §4.4 (resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: same-call identity = same canonical macro + structurally equal authored form (spans ignored); reload replaces origins; two residuals raised — edited-argument re-entry is refused under this identity, and names only an earlier expansion produced stay live |
| P3 | `spec` | scribe Q5-R1 and reload rulings | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `f91e922b` | complete: S125-Q5-R1 and R2 closed; §9.6.1 and repl §15.4/§15.6/§18 aligned; checker clean on edited files. §9.6.1 now refuses "a different call to the same macro" while advising users to "edit" the call — the conflict put to the user |
| P3 | `spec` | scribe S125-Q1–Q6 rulings | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `31857786` | complete: Q1–Q6 closed in appendix D; normative text in 12 spec/repl files (§8.3.8/§8.10.1, §5.4.5, §7.2, §3.5.3/§3.7.6, §9.3.4/§9.6.1, ch. 6, §10.1, repl §15.4/§15.6/§18); follow-up S125-Q5-R1 opened; annotations preserved; checker clean on the edited files |
| P3 | `design` | `src/` (int): re-check 1005, 1100 against Q4 A, Q5 C (resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: §4.2 revised, new §4.4 Q5 refusal (`Written`/`Generated` origin on the authored-form record; refused in `validate_guarded_staging`; `src/`-only, no gate item; single-cluster case already refused by typecheck); 1100 consistent with Q4 A; two follow-up questions for `spec` (re-entering a macro call; reload that drops the call) |
| P3 | `design` | `src/` (int): defect 1079 (same agent resumed) | `claude-opus-5-5` | medium | primary (Claude) | complete: mechanism confirmed in `src/` (loader never loads a mount's owner); designed in `s125-binary-clean.md` §5.4 from `int.md` §6.13's unscheduled S124 design; no gate item; `qa` leads include REPRO-1079-c |
| P3 | `spec` | frame open questions: ACT-1081, ACT-0985 ×4, int ×4, `spec/10-io.md` §10.2.3, wildcard match | Codex `gpt-6.1-sol` | medium | `codex_role.py` session `d6fab22e` | complete: S125-Q1–Q6 opened in appendix D; five leads answered by existing text (ACT-0985 forward reference and constraint rigidity, `(pure (pure 1))` display, §17.19 index, unary partial application). Q1 was framed before the user's ACT-1081 ruling and needs closing |
| P3 | `qa` | opening suite reading, hygiene triage | Claude Opus (user-directed substitute) | inherited | primary (Claude) | complete: opening suite 8,109 / 7,966 / 143 failed / 1 skipped, identical to S124 close, no regression; 22 hygiene filings — 7 deleted, 3 closed pending inbound links, 4 converted to `test` reductions, rest kept with reasons; `tests/plan/s125-evidence-delta.md` (declared by `sprint`) |

## Notes

- 2026-11-26: no commit since the S124 close touches `src/` or `crates/`; the
  §14.15 register describes the opening tree. The opening suite reading is
  taken by `qa` at Phase 3 readiness, not assumed from the close.
- 2026-11-26, focus-band additions by METHOD §2.4.4 (the focus module's
  backlog is drained): ACT-0994 and ACT-1085 (`src/` designs ready to build)
  and ACT-1003 (`qa` converted it to a `src/`-attributed RED, T-1003) join the
  focus band.
- 2026-11-26, trace held until the fixes are done (user: "is there any
  reason to dig into trace again until we do all the fixes?"): defects 1087
  and 1090 and ACT-1093 leave the focus band and join the trace deferral.
  The settling target names 1087's and 1090's cells as its exceptions.
- 2026-11-26, opaque `IO` (user): the veil is not lifted for `Pure`. `arch`
  assesses an `IO` with no constructors at all against row IO-T.
- 2026-11-26, scope correction (`sprint` error at Phase 1): defect 1079
  (qualified reference through an export mount, 8 cells) is attributed to
  `src/process_form/dependency.rs`, not typecheck; it joins the focus band
  under METHOD §2.4.4. Raised by `qa`'s readiness check.
- 2026-11-26, user rulings on `qa`'s decisions:
  - FIXME 0694: "yes close" — its members close as residuals, each reopened
    by a recurrence of its recorded signature.
  - ACT-1036: "repro and carry as defect" — `test` reproduces the cached
    macro-produced refusal at `0..0`; the failing test carries it.
  - ACT-1081: "I don't [think a] child mod is necessarily a cycle until
    something is imported from it." A `mod` declaration alone is not a
    dependency edge; importing from the child is. The ACT-1081 tree is
    acyclic and is accepted on every route. `spec` scribes; REPRO-1081
    requires agreement on acceptance.
- 2026-11-26, user rulings on S125-Q2–Q6: Q2 "A" (duplicate impl pair in
  one cluster refused); Q3 "A, maybe B later" (result-only HKT constructor
  refused; result-directed dispatch a future direction); Q4 "A" (caller's
  visibility governs a macro-introduced reference); Q5 "C - redefinition of
  a macro-generated name is blocked"; Q6 "refuse" (a `match` with no
  constructor arm is refused, every type). Q2, Q3 and Q6 are implemented in
  a later sprint (typecheck); Q4 and Q5 bear on 1100 and 1005 and are
  re-checked by `design`(int). `spec` scribes all six and Q1.
- 2026-11-26, user rulings on the Q5 follow-ups: S125-Q5-R1 "yes" —
  re-entering the same macro call may replace its own generated definitions;
  a reload whose file drops the call and defines the name by hand: "accept".
  `spec` scribes; `design`(int) folds into §4.4.
- 2026-11-26, §9.6.1 conflict ruled (user: "we should strictly limit redefs
  for now. later we'll loosen it by recompiling dependent modules."): the
  strict reading stands. At the REPL only an identical re-entry of a macro
  call replaces its generated definitions; a call of the same macro with other
  arguments is refused. §9.6.1's "edits … the macro call" advice is corrected
  to mean editing the call in its file and reloading. Carried with the later
  loosening: names only an earlier expansion produced stay live after an
  identical re-entry under a redefined macro.
- 2026-11-26, carried leads from W0, none blocking: §10.1 still calls the `IO`
  constructor "conceptually module-private" (→ `spec`, next dispatch); appendix
  D reads `(primitives/pure)` as a zero-argument partial application, against
  the backend design's premise (→ `design`(backend, typecheck), with the user).
- 2026-11-26, held for each owner's next dispatch: stale `build_adt_subst`
  citations (W2 deleted it) in `design/backend/backend.md`,
  `design/backend/trace-codegen.md`, `design/arch/interfaces.md` and
  `design/int/s125-binary-clean.md` (also its `driver_result_type` citation,
  and the deleted gate functions cited at `tests/plan/s122-evidence-delta.md`,
  `tests/plan/s124-evidence-delta.md` and `arch`'s packet line 35,
  which the result-owner change removed); `result-owner.md` to absorb the
  delivered change; `test` amendment that
  `s125_ps3_inline_module_no_ghost_restore` asserts its cache hit (W4 dispatch).
- 2026-11-27, persistence-unit ruling (user: "yes" to the authored-entry
  model): every live definition has one owning entry — a written form, or a
  macro call owning its expansion; a top-level `begin` dissolves into its
  members at entry, file and REPL alike; a multi-module `import` is one entry
  per spec; regeneration writes entries once in authored order. R1 and R3
  resolve by construction (the `begin`-split path is deleted); R4's grouping
  residual becomes the rule. `spec` scribes repl §15.4; `design`(int)
  redesigns §4.2; `qa` re-baselines the begin-written-once tests.
- 2026-11-27, user rulings: S125-Q8 "agree to keep the prohibition - that is
  consistent" (no hand-written top-level `begin` in file source; dissolution is
  REPL-only); shrinking re-entry "agree to refuse" (an identical re-entry whose
  expansion would drop a previously defined name is refused, naming the
  dropped definitions).
- 2026-11-27, `sprint` miss recorded: the hygiene band's non-`qa`/`arch`
  filings were never dispatched after Phase 3 ("a later wave"), and FIXME
  0933 (`src/platform.rs`) belonged to the focus band from Phase 1. Both
  dispatched at WG. Stale source citations at
  `crates/cranelisp-typecheck/src/traits/impl_check/tests.rs:1592` and
  `crates/cranelisp-platform/src/tests.rs:1479` are carried to the next time
  each surface is worked (the S124 close convention), not dispatched alone.
- 2026-11-26, allocation deviation (user: "move to opus until we get a fable
  reset"): Fable-allocated roles (`arch`, `qa`) run on Opus until the Fable
  limit resets. Phase 7 checks the dispatch log against the shared allocation
  and records this deviation. Ended at WG (2026-11-27): `arch` and `qa` back
  on `claude-fable-5-2`.

### Phase 6a outcome (2026-11-27)

Assessments, all read-only outside each owner's plan: `spec`
(S125-Q10-R1 recorded in §8.11.2.1; its band handoffs delivered by `qa` in delta §27), `docs`
(dispatch report), `training` (`examples/plan-examples.md` §4.7, 152/152
replays), `dev`(stdlib) (`stdlib/plan-stdlib.md`, 318/318 self-tests; its 6b section delivered and removed),
`dev`(exemplar) (`exemplar/plan-exemplar.md`, 44/44 `--test`), `audit`
(`audits/cranelisp-intrinsics-s125.md`, F1–F5; two inbound links repointed).
No new compiler defect. One exemplar-owned defect: the 404 page reflects the
request path unescaped. ACT-0995 updated with S125-Q10-R1.

**User decisions at the 6a → 6b checkpoint (2026-11-27).** Audit: F1 carried
on 0977's guards; F2 and F3 to `qa` intake with `test` reproductions in 6b,
repairs carried; F4 carried as an action to `design`(intrinsics); F5 fixed in
6b by its owners. Deferred: stdlib FIXME 0800 face 3 and `Ord String`. Not
deferred: training's IO-arc reorganization (T125-5) — "don't defer the IO
lessons now we've changed the developer surface"; any entry removal or exit
change is co-planned with `test`.

**F2 and F3 repairs brought into 6b (user, 2026-11-28):** "fix F2 and F3 this
sprint". Route: `design`(intrinsics), `arch` if an interface changes, `dev`,
`review`, `qa`; back to the user if `design` finds either repair large. The
§27.8 item 5 replay runs after the repairs.

**Phase 6b outcome (2026-11-28).**
- **Repaired:**
  - F3 and F2 in intrinsics;
  - the binary's trap guard deleted (`design/int/s125-binary-clean.md` §8);
  - Defect A, macro-argument caller scope, with its reanchoring (`design/int/expansion-qualification-scope.md` §2.7, `macro-diagnostic-reanchoring.md` §2.2);
  - Defect B, the residual-type display regression.
- **Reviewed:** each repair passed `review`, and each finding was corrected and re-checked.
- **Replay:** 41 of 41 demos; two demo imports repaired.
- **Full run:** a fresh build of the final tree gave 8,447 run, 90 failed. After `test`'s stale-pin repair the set is 89. No failure was caused by the sprint, and the only failures in `src/` are 1087 and 1090 (delta §31).

**User decisions at the 6b → 7 checkpoint (2026-11-28).**
- **Robust primitives:** recorded by `spec` as appendix D S125-Q12, which it closes as option A.
  - Every offered primitive is robust: it reports failure through its type.
  - `unchecked-` primitives, and the compiler warning for code that can reach one, are a future requirement.
  - Panics are removed as a category, which replaces the 2026-11-15 ruling.
  - Stack exhaustion and failed allocation get a zero-cost diagnostic where the platform permits.
  - Graceful failure is the platform designer's responsibility: "the pure language should assume it, not guard against it".
  - The rewrite is carried to S126. T-STACK stays until the spec text changes.
- **Timer-leaf reuse:** carried on T-POLL-REUSE: "carry the timer-leaf if we have defects and it's not in our focus module".

## Close (Phase 7, 2026-11-28)

**Outcome against the settling target.** It holds on a fresh build of the final tree. There are 89 failing tests, each the reproduction of a carried defect. The only ones attributed to `src/` are 1087 and 1090, the named exceptions. No `src/` review finding is open. The failing set and its attribution are in the [S125 evidence delta §31](../../tests/plan/s125-evidence-delta.md).

**Accepted by the user:**
- 1087 and 1090;
- the residuals of delta §26.3 and the limits of §29.1;
- stack exhaustion, carried on T-STACK's five cells until the S126 rewrite of the specification;
- timer-leaf reuse, carried on T-POLL-REUSE's two cells.

**Carries:**
- [ACT-1054](../actions/ACT-1054-primitive-arithmetic-checked-unchecked-pairs-and-ub.md): the robust-primitives ruling (appendix D S125-Q12), scheduled for S126;
- [ACT-0995](../actions/ACT-0995-repl-later-submodule-declaration-resolution.md): S125-Q10;
- [ACT-1009](../actions/ACT-1009-repl-restore-last-known-good.md): S125-Q11;
- [ACT-1113](../actions/ACT-1113-intrinsics-trampoline-duplication-and-dormant-recording.md): F4;
- [ACT-1114](../actions/ACT-1114-primitives-marshal-derives-adt-layout-locally.md): primitives ADT layout;
- [ACT-1115](../actions/ACT-1115-reanchoring-fallback-when-nothing-expanded.md): the reanchoring fallback;
- [ACT-1116](../actions/ACT-1116-s125-close-maintenance-residue.md): the close maintenance residue.
