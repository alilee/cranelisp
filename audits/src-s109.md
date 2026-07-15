# `src/` (int) Whole-Context Assessment — Sprint 109

> **Rotation**: `src/` — the binary / integration layer (pipeline orchestration,
> REPL session, CLI, `--link`, `src/agent/`), per `sprints/SPRINT.md` §Audit
> (arch P2 ruling: observability lead landed in `src/agent/`, the
> heaviest-touched context this sprint).
>
> **Predecessors**: `audits/src-s87.md` (S87 Stage-B delta audit, findings
> F-A…F-L — reconciled in §2.8 below; it predates the artefacts.md acceptance
> gate, so there is no disposition trail to start from) and
> `audits/src-20260423.md` (historical baseline).
>
> **Method**: acid test per `.claude/commands/audit.md` — "if we lost this
> context's code and docs but retained the insight, would the second-time
> solution look like this?" Read-only; this file is the only artefact written.
> Includes the S109 audit-calibration lens (FIXME 0583): bounded-context
> responsibility boundaries, swept in both directions (§2.4).
>
> **Scale at audit**: 62,188 raw LOC under `src/` (~48k production after
> excluding `tests.rs`/`*_tests.rs`/`#[cfg(test)]`), 36 top-level modules plus
> 8 submodule directories. `src/agent/` is 8,624 LOC (prod + its unit tests).

---

## 1. Verdict

| Attribute | Grade | One-line basis |
|---|---|---|
| Design quality (fitness) | **strong** | The seams are the ones a second-time solution would design again: one cluster core, one gap→scheduler crossing, one styled-display authority, the `AgentModel` membrane. |
| Design realisation | **adequate** | Code faithfully realises the design — but the master design doc (`design/int/int.md`) and `agent.md §2.2` assert states the code left behind one-to-three sprints ago (§2.2). Drift is docs-behind-code, not code-off-design. |
| Simplicity & volume — code | **adequate** | The S87 god-file decomposition landed and held everywhere except `repl.rs`, which regrew into the workspace's largest production file (5,103 lines, ≥6 mixed responsibilities). 26 functions exceed the context's own ~100-line budget. |
| Simplicity & volume — docs | **weak** | 44 design docs in `design/int/` with no staleness triage; `int.md` presents S81-era layout/LOC as current; `agent.md` is a 3,124-line chronological accretion. Over-documentation is the context's largest excess. |
| Simplicity & volume — tests | **strong** | Unit tiers are per-submodule and scenario-shaped (`worker/tests.rs`, `scheduler/tests.rs`, `imports/tests.rs`, …); agent lane is stub-driven, zero-network, request-content-asserting. Nothing here the rewrite would drop. |
| Duplication | **strong** (one exception) | The S87 duplication findings converged: prelude-hop → one canonical helper, macro-clause → one core, type rendering → one `render_type` walk, sink gate → one `sink.rs`. The one genuine remaining mirror is `bootstrap.rs::register_synth_adt` ↔ typecheck's `register_type_def_with_ctor_infos` (§2.4). |
| Risk-weighted coverage | **strong** | Top risks are pinned on production paths: the S109-1 scheduler race has a ≥25-iteration e2e sweep + four deterministic unit arms; mode parity (REPL/`--run`/`--link`) is actively tested; DEF-1 and the 0571 cluster each closed with failing-first guards. |
| Maintainability | **adequate** | Seam clarity and naming are high; comment honesty is high but narrative density is extreme (26 production comment blocks ≥30 lines, some pure sprint history) — flagged at 04-23 and S87, still regressed. ~30 `#[allow(dead_code)]` sites persist. |
| Memory freshness | **adequate** | `src/CLAUDE.md` (28 KB, down from 39 KB at S87) is current on every claim spot-checked. `lib.rs`'s module-comment layer is not: it cites the retired `facades/int.md`, calls the live `cluster` path "not yet reachable" (FIXME 0176, long resolved), and describes `agent` as a Wave-2 placeholder (§2.7). |

**Overall.** Would the second-time solution look like this? **Architecturally,
yes — this is one of the strongest contexts in the workspace.** The things
that make int hard — three cadences, a work-stealing scheduler, gap-driven
retry, cache restore, session transactions, an embedded LLM advisor — are each
behind a single, named, tested seam, and the S109 work (0571 gap-arm, unified
display envelope, observability log) landed *on* those seams rather than
beside them. The rewrite would keep the v4 cluster orchestration, the
scheduler, the styled-display authority, and the agent membrane essentially
as-is. What it would **not** reproduce: `repl.rs` as a 5,103-line flat module
containing a whole search subsystem; a second hand-maintained copy of ADT
registration in `bootstrap.rs`; ~30 dead-code allows and a vestigial raw-pointer
parameter; a master design doc describing a tree two restructures old; and a
3,124-line agent design doc whose classifier section the code explicitly
contradicts. The gap between as-built and second-time is almost entirely
**volume hygiene and doc currency**, not design.

---

## 2. Current state

### 2.1 Design quality — the seams held under this sprint's load

The heaviest-touched seams this sprint were exercised exactly as designed:

- **0571 gap-arm decision logic** — the "member-absent → unconditional gap →
  int decides" reshape landed cleanly at the single crossing:
  `src/process_form.rs:453-491` implements the three-arm decision (terminal ⇒
  honest diagnostic; absent/non-terminal ⇒ `drive_module_dep` + park), with the
  monotone `ever_terminal` set (`src/scheduler.rs:328,1489`) closing the 0571.3
  "scheduler later forgot" residual, and the §8.5.4 "module X has no member Y"
  diagnostic having exactly **one authoring site**
  (`module_has_no_member_error`, `src/process_form.rs:577` — shared by the gap
  arm and `phantom_member_diagnostic`). Typecheck stays scheduler-free; int
  owns liveness decisions. This is the bounded-context split working.
- **0572/0569 display unification** — `/search` rows, macro rows, and eval
  results all build `StyledDoc`s and emit through the single `styled::render`
  seam; the macro row renders the `; defmacro` envelope through the same
  producers as bare lookup (`render_search_row_doc`, `src/repl.rs:1349-1405`,
  unit-pinned at `:3414`). `style::styled` has exactly the two sanctioned call
  sites (`src/styled.rs:175`; the agent frame in `src/agent/render.rs`).
- **Eval-thread vs pool-worker convergence** — the REPL retry loop
  (`process_form_cluster`, `src/eval.rs:243`) wraps the same
  `process_cluster_once` core the pool workers run, with `eval_driven: true` as
  a mode parameter (`src/eval.rs:307`), not a second pipeline. Invariant SW
  holds structurally.
- **Agent architecture** (§2.5) — the membrane/allowlist/harvest-ladder design
  survived three feature waves (Advise → Build/Document → observability)
  without `agent_turn` growing a second dispatch shape.

**Fitness caveat**: `src/bootstrap.rs::register_synth_adt` — see §2.4. It is
user-arbitrated (FIXMEs 0241/0242/0319) but is design the second-time solution
would not repeat now that 0583 has named the class.

### 2.2 Design realisation — code ahead of docs, in three places

Drift is one-directional (implementation moved on; docs did not), but the
master doc's staleness is material:

1. **`design/int/int.md` §3.2/§3.3** presents the S81-era tree as current:
   "`session_v4.rs` 6,452 LOC god-file … split into `eval.rs` + `repl.rs` per
   §3.3 … **Wave D (carried)**", "Total today: 28,592 LOC", `observability.rs`
   "renames to `src/scheduler_trace/`" (never happened), `expander.rs` "517
   LOC" (now 1,683), `save.rs` "493" (now 2,306). Wave D landed at S87; the
   submodule directories (`session_v4/`, `process_form/`, `worker/tests.rs`)
   post-date every row. A reader planning int work from the master doc gets a
   two-restructures-old map. (`design/int/int.md` §3.2 table, §3.3.)
2. **`design/int/agent.md` §2.2** documents the *retired* symbol-resolution
   classifier ("a bare `Symbol` is known iff `symbol_is_known(name)`…", lines
   ~113-165, with a bolded "future reader MUST NOT" warning about a premise
   that is no longer the rule). The code implements the **form-count rule**
   (user ruling 2026-07-12): `forms.len() == 1 → Repl`, else `Agent`,
   `symbol_is_known` explicitly NOT consulted (`src/agent/mod.rs:70-148`;
   `symbol_is_known` no longer exists outside comments). The doc's normative
   warning now protects the wrong invariant.
3. **`src/lib.rs` module comments** (§2.7): retired-facade citations, a
   "not yet reachable … FIXME 0176" note on the live `cluster` hot path
   (`src/lib.rs:22-27`), and an `agent` comment frozen at the Wave-2
   placeholder state (`src/lib.rs:108-114`).

One tracked-work gap found: `phantom_member_diagnostic`'s comment
(`src/process_form.rs:438-449`) defers "the deeper ordering cure — typecheck
preferring the loaded absolute module over the phantom child" to "a
`/typecheck` FIXME" — **no such FIXME exists** in `design/arch/fixmes/`. Post-
0571 (member-absent now gaps unconditionally) it is also unverified whether the
phantom-child shape can still arise, i.e. whether this shim is live or dead
(R-5).

### 2.3 Simplicity & volume

**Code.** The S87 decomposition programme succeeded and held — `session_v4`
lifecycle/nice-worker/test-runner extractions brought `CompilerSession::new`
216→83 lines, `compile_module_object` 174→53, `discover_tests_extern` 190→42
(`src/session_v4/lifecycle.rs:57`, `nice_worker.rs:148`, `test_runner.rs:387`);
`try_cache_hit_load` went 254→43 lines with six named helpers
(`src/process_form/cache_restore.rs:41-469`). The exceptions:

- **`repl.rs` is the new god-file**: 5,103 lines, ~185 production functions,
  one flat module mixing (a) slash dispatch (`dispatch_command`, :512, 155
  lines), (b) ~25 `handle_*` command handlers, (c) an entire **search
  subsystem** (`handle_search` :1158, `collect_name_and_docstring_hits`,
  `render_search_row*`, `wait_for_index_settled`, `try_search_by_scheme`,
  `scan_referers` — the UI half of the `session_v4/index_worker.rs` feature,
  embedded inline), (d) the introspection-display formatter family
  (`format_def_entry_doc` :2738, `format_eval_result*` :2579-2611,
  `format_type_display`, `format_trait_display`), (e) prompt/banner/line-editor,
  (f) typecheck-only + macro-expansion entry points (`typecheck_only`,
  `compile_pending_macros`). It absorbed S108's search UI and S109's display
  unification without ever being re-cut. The `design/int/int.md` §3.3 Wave-D
  allocation for this file was "slash-command dispatch, prompt formatting,
  banner, line-editor wrapper" — roughly a fifth of what it now holds.
- **26 production functions > 120 lines** (budget is ~100). Top:
  `main.rs::run` (:241, **394 lines, 9 params**), `exe.rs::generate_startup_object`
  (:50, 340), `worker.rs::commit_staging_to_live` (:423, 237),
  `process_form.rs::process_cluster_once` (:150, ~224 — *grown* from ~150 at
  S87), `main.rs::parse_args` (:641, 225), `redefine.rs::run_transaction`
  (:852, 185). Three functions exceed the 8-param cap, worst
  `compile_macro_with_state` (11 params, `src/process_form/macro_resolution.rs:314`).
- **Narrative density** (04-23 F7, S87 "regressed/unchanged" — third
  consecutive flag): 26 production comment blocks ≥30 consecutive lines,
  concentrated in the orchestration core (`scheduler.rs:865,1661`,
  `session_v4.rs:258` — literally "Sprint 57 Wave 2 G6", `bootstrap.rs:1`
  55 lines) and `src/agent/*`. Comment honesty is high; placement is the
  problem — sprint history belongs in `design/int/`, not hot paths.

**Docs.** `design/int/` holds **44 design docs** with no currency triage; at
least the `step*.md` / `s7*.md` / `wave-*.md` slice docs are superseded
narrative, and the two load-bearing docs (`int.md`, `agent.md`) are the stale
ones (§2.2). S109 built exactly the tool for this in typecheck (FIXME 0578:
as-built rewrite + doc-sprawl banners + CLAUDE.md doc-index); int is the next
context that needs it. `agent.md` at 3,124 lines is a chronological accretion
of eight sprint-phases (§0 MVP tiers … §28 sink notes) rather than an as-built
design — over-documentation as decay-in-waiting, already misleading in §2.2.

**Tests.** Right-sized and well-shaped. Per-submodule unit tiers sit next to
their code (`worker/tests.rs` 2,043, `scheduler/tests.rs` 1,654,
`imports/tests.rs` 846, `observability/tests.rs` 736, plus scenario-class files
like `session_v4/bare_primitive_value_path_tests.rs`); the agent lane runs the
whole loop against a scripted stub with request-content assertions
(`src/agent/mod.rs:648-1184`) — e.g. `tool_result_re_enters_next_request`
asserts fed-back tool-result *content*, strengthened after it once passed
vacuously (:837-912). No test volume the rewrite would delete.

### 2.4 Duplication + the bounded-context responsibility lens (FIXME 0583 calibration)

Applying the new lens — "does src/ do work that belongs to another context, or
vice versa?" — across all four facets:

**The one genuine instance: `bootstrap.rs::register_synth_adt` is a
hand-maintained mirror of typecheck's ADT registration.**
`src/bootstrap.rs:131-285` reconstructs, near line-for-line,
`cranelisp_typecheck::register_type_def_with_ctor_infos`
(`crates/cranelisp-typecheck/src/adt.rs:123-211`): the product/sum predicate
(`bootstrap.rs:159` ≡ `adt.rs:158`), ctor-scheme building (`:165-181` ≡
`build_constructor_scheme`, `adt.rs:316`), GOT-slot allocation (`:223` ≡
`adt.rs:357`), the synthetic `ConstrADT` body (`:194-216` ≡ `adt.rs:325-342`),
the product dual-facet vs separate-`TypeDef` split, and — new since S87 — the
S109 **canonical `member_key` + bare-alias keying** (`bootstrap.rs:256-267`),
meaning the dotted-ctor change had to be applied to *both* copies this sprint.
This is S87 F-J, but its status changed: it is the exact class 0583 names
(sanctioned by FIXMEs 0241/0242/0319 as "content construction is not
type-checking," yet two copies of one registration algorithm that must move in
lockstep — and S109 proved they do have to move together). The S110 0583
initiative is the natural vehicle: one ADT-entry builder in `cranelisp-types`
consumed by typecheck's resolver-driven path and bootstrap's FQ-direct path
(R-2).

**Everything else swept is clean** — evidence, briefly:

- `bind_chain_analysis.rs` (854 prod lines): pre-typecheck AST→AST transform;
  reads only `scheduling_class` off entries via keyed lookup + import-chain
  follow (`bind_chain_analysis.rs:24-38`); no Scheme/Type inspection. Correctly
  int-owned (its finer ownership question is already tracked, FIXME 0486).
- `display.rs`/`pretty.rs`: **no** parallel type renderer — five
  `cranelisp_types::render_type` call sites, zero local structural walks; the
  one local recursion (`format_type_with_inline_constraints`, `display.rs:263`)
  is display-decoration that delegates every variant back to `render_type`.
  The FIXME 0420 convergence held.
- `expander.rs`: recognition fully delegated to
  `cranelisp_types::ResolutionScope::resolve_macro_head`
  (`expander.rs:319-368`); remaining table access is direct keyed lookup on the
  already-resolved FQ (`:228,241`). No hand-rolled precedence walk.
- **`symbol_tables.iter()` scans**: nine production sites, ALL exhaustive
  enumerations (linker registration `worker.rs:1421-1557`, `--link` gate
  `exe.rs:478`, watcher reverse-dep `session_v4/lifecycle.rs:919`, `/uses`
  `repl.rs:1501`, index snapshot `index_worker.rs:1027`, agent existence probe
  `harvest.rs:397` — feature-gated boolean). **Zero** first-hit-wins name
  resolution of the backend `resolve_driven` shape. src/ has no 0583-class
  resolver.
- `session_v4/index_worker.rs` (1,966 lines): consumes typecheck outputs and
  *calls* typecheck's own predicates (`signature_matches_exact/partial`,
  `index_worker.rs:418-421`, rustdoc: "int CALLS them; does not own them");
  meta-stale re-index runs the real `check_forms` against a private snapshot
  (`:1079-1148`). No re-derivation. The S109 `mod-` privacy fix landed here as
  a declared-attribute read, not a name probe (Principle 19).
- Production `Scheme`/`Type` construction is confined to the two sanctioned
  seeders (bootstrap; the platform-manifest installer, `platform.rs:381`).
- **Reverse direction**: zero hits for `CompilerSession`/`SharedState`/
  scheduler/REPL-display knowledge in any `crates/*` source; typecheck's only
  session contact is the borrowed read-only `&ModuleAliases`/`&PreludeFallback`
  params. No crate reaches into int's concerns.

**Divergent-copy status**: the S87 §3 finding (prelude-fallback consulted at
~10 uncoordinated sites) has **converged**: actual bit-decision reads are down
to four sites, one per concern (`imports.rs:287`, `expander.rs:357`,
`process_form/form_dispatch.rs:237`, `repl.rs:716` inside the canonical
`lookup_with_prelude_fallback_opt`); the two S87 off-canonical re-inlines in
`describe_symbol`/`format_eval_result_body` are gone (routed through the
canonical helper, `repl.rs:404`, `:2633`). The S108 `_or_prelude` convergence
exemplar worked on the int side too.

**Spec-surface facet**: nothing surfaced from the int vantage this rotation.

### 2.5 `src/agent/` — accumulated design health (the S109 focus area)

**Verdict: the strongest-designed subsystem in src/.** Three feature waves and
an observability increment accreted onto one architecture without deforming it:

- **The membrane held.** `agent_turn` (`src/agent/mod.rs:200-372`) still
  dispatches through the one-method object-safe `AgentModel`; rig coupling is
  still confined to `provider.rs`/`request.rs`; the stub drives the whole loop
  zero-network. Streaming (S9x) was added as `complete_streaming` with a
  default degrade — no second loop.
- **The consent boundary is structural.** The read-only allowlist +
  the single `submit`/`set-preamble`/`set-doc` write tools are enforced at
  synthesis (`pull.rs:62-186`), confirm-gated through one `ConsentReader`
  seam, with negatives (`write_tool_call_is_refused`,
  `document_tools_refused_by_read_only_allowlist_neg`).
- **The observability lead (0577-A) is exemplary in shape**: `log.rs` (431
  lines) is a flat, fluently-built `LogEvent` with every F1–F6 field
  documented against the metric it feeds in
  `tests/plan/agent-context-tuning.md §4` (`log.rs:76-105`); the scenario tag
  is stamped at the single `record` chokepoint (`:213-232`) so no call site
  can forget it; the shared env-gate/append/swallow mechanism was extracted
  ONCE into `sink.rs` for both log and trace (Principle 7 done properly,
  `sink.rs:1-49`); the silent/graceful contract is unit-pinned including the
  unwritable-path negative. The Thread-B probe channel runs read-probes
  against a throwaway sink rather than echoing into the user session.
- **Volume**: 8,624 LOC total is defensible — roughly 5.3k production across
  11 files, each under 1,000 prod lines except `pull.rs` (~995 prod + ~740
  test), which now holds pull + submit + repair + document-edit and is the
  file to watch (next write-mode wave should split submit/repair out).
- **Debt is documentary, not structural**: the `agent.md` §2.2 classifier
  contradiction (§2.2 above), the doc's 3,124-line accretion, and the
  `MAX_TURN_ITERATIONS`/`MAX_REPAIR_ITERATIONS` budget knobs being
  code-constants while the harvest budget got an env knob — minor asymmetry.
- **Repo hygiene nit**: `agent_trace.txt` (1.0 MB dev-session trace) sits
  untracked at the repo root and is NOT gitignored — an NG4 artifact one
  `git add -A` away from history (R-6).

### 2.6 Risk-weighted coverage

Derived top risks, each verdicted against a production-path pin:

| Risk | Pinned? | Evidence |
|---|---|---|
| Scheduler in-flight race (§8.5.4 edge 7, ≥2 workers) | **yes** | S109-1: C1-e2e ≥25-iteration sweep + four deterministic unit arms at both seams (`tests/plan/risks.md:10`); the S93 lost-wakeup fix is the atomic check-and-block (`scheduler.rs:865,1661` narrative + unit pins) |
| REPL/`--run`/`--link` divergence | **yes** | one `process_cluster_once` core (§2.1); 0571/0573 fixes verified mode-parity in-sprint (SPRINT dispatch log); dual-mode e2e discipline in `tests/plan/` |
| Cache restore / schema skew | **yes** | S109-3 warm-cache + stale-invalidation rows; `cache_restore.rs` decomposed with validity check first |
| Persistence data loss (save/regenerate) | **yes** | 0573 closed with the deftype-shape × persistence matrix (sum/product × file-content/reload), the "coverage by definition variants" category made concrete |
| Redefinition UAF (trap stubs, retention pool, GOT slots) | **yes** | `src/CLAUDE.md` §redefine invariants + `redefine.rs` unit tier + S101/S102 e2e |
| Agent-lane regressions leaking into default suite | **yes (by construction)** | full `#[cfg(feature="agent")]` gating; default build never compiles rig; agent e2e lane `tests/agent.rs` |
| TTY prompt width (R13) | **no — documented deferral** | `repl/spec.md §10.8`; `prompt_string` doc comment; accepted risk, unchanged |

The known-defect-guard discipline is working: the suite carries only the two
long-known carries at sprint end per the S109 record, and every S109 defect
closed failing-first.

### 2.7 Maintainability & memory freshness

- **Naming/seams**: coherent throughout; the `_doc`-producer + `render`
  pattern makes display code uniformly testable; newtyped identifiers used
  consistently.
- **`#[allow(dead_code)]`**: ~30 non-test sites, including the two S87 F-H
  accessors still present verbatim (`introduce_module_blank`,
  `session_v4/lifecycle.rs:620-621`; `cached_module_remove`,
  `scheduler.rs:2000-2001`), a module-level allow on `cache_writer.rs:13`, and
  clusters in `redefine.rs` (7) and `platform.rs` (3). The S87 Wave-0
  "prefer deletion" precedent was not applied.
- **Vestigial raw-pointer param**: `extra_jit_symbols: &[(String, *const u8)]`
  still threaded through `inline_jit_codegen_for_module/_for_names` and nulled
  at `worker.rs:1125` (S87 F-I, unchanged — a dead `*const u8` slice is a
  latent foot-gun).
- **House-style violation**: the one production pipeline `.unwrap()` flagged at
  S87 (F-K) is still there — `process_form.rs:906`
  (`ctx.symbol_tables.get(&ctx.current_module).unwrap()` in
  `clear_module_codegen`); `src/CLAUDE.md` §Error Handling forbids it. The
  rest of the sweep stays clean (remaining unwrap/expect are algorithmic
  invariants with text, or thread-spawns; zero production `panic!`).
- **`src/CLAUDE.md`**: current on every claim spot-checked (fallback mechanism,
  form_dispatch path, styled seam, agent map); 28 KB. **`src/lib.rs`** comments
  are the stale layer (§2.2 item 3).

### 2.8 S87 findings reconciliation (the prior-assessment trail)

| S87 | Finding | S109 status |
|---|---|---|
| F-A | codegen batch ignores prelude fallback (DEF-1 seat) | **Resolved at a different seam** — the DEF-1 repro is GREEN-pinned (`tests/plan/PLAN.md:1797`, S108 prelude≡import convergence); `derive_codegen_batch` (`worker.rs:874`) still enumerates only the module's own table, which is now correct by design |
| F-B | JIT vs `--link` host-extern dual wiring | **Open, unchanged** (`worker.rs:1421` dlsym path vs JIT fallback) — remains 0407-family backlog; no parity guard yet |
| F-C | `try_cache_hit_load` god fn | **Resolved** — 43 lines + 6 helpers (`cache_restore.rs:41-469`) |
| F-D | 3 over-budget session_v4 fns | **Resolved** — 83/53/42 lines after extraction |
| F-E | process_form over-budget family | **Mixed** — `classify_form` cured (66); `process_cluster_once` **grew** to ~224 |
| F-F | repl.rs over-budget handlers | **Mixed** — `format_def_entry` cured via `_doc` split; `handle_imports` unchanged (~110) |
| F-G | prelude-hop re-inlines | **Resolved** — both routed through the canonical helper; 4 decision-site reads remain, one per concern |
| F-H | dead-code accessors | **Unchanged** (both still present, still allowed) |
| F-I | `extra_jit_symbols` vestige | **Unchanged** (`worker.rs:1058/1113/1125`) |
| F-J | bootstrap↔typecheck ADT mirror | **Open, escalated in significance** by 0583 (§2.4) — S109's dotted-ctor keying had to be hand-applied to both copies |
| F-K | production `.unwrap()` | **Unchanged** (`process_form.rs:906`) |
| F-L | `register_dep` prologue ×5 | **Resolved** — shared prologue with caller-owned error framing (`dependency.rs:482`) |

Score: 5 resolved, 2 mixed, 4 unchanged (all small residue), 1 escalated.
The big-ticket S87 asks were done; the small-residue batch was not — the same
pattern the typecheck S108 audit found (its accepted R-5 "S87 residue batch"
is the precedent for R-4/R-5 below).

---

## 3. Recommendations

Severity-ranked. Per the audit charter these are proposals for the S110
Phase-1 acceptance gate; none is filed as a FIXME by `/audit`.

### R-1 (Important, cost: medium) — Decompose `repl.rs`; extract the search subsystem first
**Owner**: `/dev` (src/), with `/design` (int) sign-off on the cut (the 0580
`program.rs` split is the S109 template: cut signed off first, mechanical move
last, `public-api.txt` zero-diff).
**Evidence**: §2.3 — 5,103 lines, ~185 production functions, six mixed
responsibilities; the search UI (`handle_search` `repl.rs:1158` +
`render_search_row*` + settle/scheme/referer helpers) is the UI half of
`session_v4/index_worker.rs` living in the wrong file; the display-formatter
family (`format_*_doc`, `:2579-2760`) is a coherent sibling of `display.rs`.
**Shape**: `repl/search.rs` (UI half, beside its index worker), `repl/format.rs`
(the `_doc` producer family), `repl/commands.rs` (the `handle_*` battery),
residual `repl.rs` (dispatch + prompt/banner + line-editor — the §3.3 Wave-D
allocation it was supposed to be). Fold the S87-unchanged `handle_imports`
split into the move.
**Done**: no file in the family exceeds ~1,500 lines; behaviour-invariant
(golden REPL e2e green, zero `public-api.txt` diff); `design/int/int.md`
module map updated in the same change-set.

### R-2 (Important, cost: medium, cross-crate) — Fold the bootstrap↔typecheck ADT-registration mirror into the S110 0583 initiative
**Owner**: `/arch` (it is a `cranelisp-types` interface question), executing
skills `/dev` (typecheck + src/).
**Evidence**: §2.4 — `bootstrap.rs:131-285` ≡ `adt.rs:123-211` near
line-for-line, including the S109 canonical-key logic that had to be edited in
both places this sprint. This is src/'s one instance of the 0583 "two
implementations, one algorithm" class; 0583's S110 charter ("typecheck emits,
backend consumes; one codepath per operation") is the natural umbrella even
though this mirror is int-side.
**Shape**: one ADT-entry builder in `cranelisp-types` (entry construction is
already types-crate vocabulary: `ModuleEntry::def`, `member_key`, GOT-slot
alloc) with two thin callers — typecheck's TypeExpr-resolving path and
bootstrap's FQ-direct path.
**Done**: `register_synth_adt` reduced to field-spec assembly + a call into the
shared builder; the product/sum predicate, ctor-scheme construction, and
canonical keying exist exactly once in the workspace; both callers' unit tiers
green.

### R-3 (Important, cost: medium) — `design/int/` currency pass: rewrite `int.md` to as-built; triage the 44-doc sprawl; fix `agent.md §2.2`
**Owner**: `/design` (int).
**Evidence**: §2.2/§2.3 — `int.md` §3.2/§3.3 asserts the S81 tree ("Wave D
carried", 28,592 LOC, phantom `scheduler_trace/` rename); `agent.md §2.2`
documents the retired resolution classifier with a now-wrong normative warning
(code: `src/agent/mod.rs:70-148`, form-count rule, user ruling 2026-07-12);
44 docs with no staleness banners.
**Shape**: the S109 typecheck 0578 template — as-built rewrite of the master
doc's structural sections, doc-sprawl banners on superseded slice docs
(`step*.md`, `s7*.md`, `wave-*.md`, dated one-shot designs), a doc-index in
`design/int/CLAUDE.md`, and a surgical §2.2 correction in `agent.md` (the full
agent.md restructure can wait; the classifier section actively misleads today).
**Done**: `int.md`'s module map matches the tree (spot-check: `session_v4/`,
`process_form/`, `repl.rs` reality); every superseded doc carries a banner;
`agent.md §2.2` describes the form-count rule and its "MUST NOT" warning
protects the live invariant.

### R-4 (Moderate, cost: medium) — Over-budget function batch, worst-first, with narrative relocation
**Owner**: `/dev` (src/).
**Evidence**: §2.3 — 26 functions >120 lines against the context's own
~100-line budget; worst: `main.rs::run` (394 lines **and** 9 params),
`exe.rs::generate_startup_object` (340), `worker.rs::commit_staging_to_live`
(237), `process_form.rs::process_cluster_once` (~224, grown since S87),
`main.rs::parse_args` (225); `compile_macro_with_state` 11 params
(`macro_resolution.rs:314`).
**Shape**: phase-named helper extraction (each offender already has phase
comments marking the cut points); context structs for the two param-cap
violators; and — the third-time flag — when touching a function, move its
≥30-line sprint-history block into the relevant `design/int/` doc, leaving a
one-line pointer (couples with R-3 so the narrative has a current home).
**Done**: the six named functions ≤ ~120 lines with named helpers; no function
>8 params; behaviour-invariant (suite green, zero public-API diff).

### R-5 (Minor, cost: small) — S87 residue batch + the untracked phantom-shim question
**Owner**: `/dev` (src/) for the residue; `/qa` or `/design` (typecheck) for
the shim verdict.
**Evidence**: §2.7/§2.8 — F-H dead accessors (`lifecycle.rs:620`,
`scheduler.rs:2000`) and the ~30-site `allow(dead_code)` population; F-I
`extra_jit_symbols` raw-pointer vestige (`worker.rs:1058/1113/1125`); F-K
production unwrap (`process_form.rs:906`); and the `phantom_member_diagnostic`
comment (`process_form.rs:448`) deferring to a `/typecheck` FIXME that was
never filed — post-0571 it is unverified whether the shim is still reachable.
**Done**: each `allow(dead_code)` deleted or justified with its consumer named;
the vestigial param dropped; the unwrap converted to
`unreachable!("invariant: …")`; the phantom shape either reproduced (→ tracked
FIXME for the typecheck probe-order cure) or shown unreachable (→ shim + its
`find_named_var_span` helpers deleted). Precedent: S108 typecheck R-5,
accepted as FIXME 0581.

### R-6 (Minor, cost: small) — Repo/comment hygiene: gitignore `agent_trace.txt`; refresh `lib.rs` module comments
**Owner**: `/dev` (src/) (gitignore line via `/sprint`'s next commit is also fine).
**Evidence**: §2.5/§2.2 — `agent_trace.txt` (1.0 MB, NG4 dev artifact)
untracked and not ignored at repo root; `lib.rs:22-27` ("not yet reachable …
FIXME 0176") describes the live hot path as dormant, `:7/:30/:35` cite the
retired `facades/int.md`, `:108-114` describes `agent` as a Wave-2 placeholder.
**Done**: trace/log artifacts ignored; `lib.rs` comments state current facts
(or are deleted where the module rustdoc suffices).

---

## 4. Disposition trail

*(Appended at S110 Phase 1 by `/sprint` + the user — accepted → FIXME number,
or declined + rationale. Not written by `/audit`.)*
