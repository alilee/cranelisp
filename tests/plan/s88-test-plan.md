# Sprint 88 — `/qa` Failing-Test Plan (Step 3.1, gating)

Owned by `/qa`. Authored Phase 3 Step 3.1 (the gating, run-first step). The
DEF-2 minimal repro is the GATING deliverable (R1 — minimal-repro-gates-owner-
assignment); the 0423 repro and the agent-feature test plan accompany it.

Baseline at S88 open: `cargo nextest run --workspace` = **2870 passed / 0 failed
/ 0 skipped**, zero intentional reds (S87 close). A genuine regression is any RED
beyond the named guards this plan adds.

SHA at authoring: `bb585ea` (working tree, pre-commit).

---

## Stage A — Green & clear (the two defect repros)

### 1. DEF-2 — curated `conj` corrupts heap-ADT Vec elements — **RESOLVED** (GATING)

**Headline determination (R1): DEF-2 does NOT reproduce on the current binary.
It was collaterally fixed (S87 FIXME 0417). There is NO live defect and NO owner
to assign — the triage `/sprint` queued is MOOT.**

#### What the brief asked for

Reduce to a minimal failing test the EXACT shape the exemplar reports:
accumulate a `(Vec Box)` (heap-ADT element) via the curated wrapper
`(defn conj [v x] (vec-push v x))` vs via bare `vec-push`, in a ~30-iteration
accumulator loop, and assert the two produce equal element sums. S87's repro
pass claimed "simple conj doesn't reproduce"; the brief insisted the LIVE shape
is the heap-ADT-element-passed-through-the-wrapper-call-frame one.

#### What the isolation found

I drove the EXACT shape the brief and `exemplar/CLAUDE.md §DEF-2` name, and
**every variant produced equal, correct results** — conj and `vec-push` are
behaviourally and RC-identical:

| Shape driven (via `--run`, 30 iter unless noted) | conj result | vec-push result |
|---|---|---|
| `(Vec Box)` value-threaded accumulator, sum all | 465 ✓ | 465 ✓ |
| `(Vec Box)` borrowed-source re-read each iter | 150 ✓ | 150 ✓ |
| copy shared heap-ADT elements src→acc, sum acc | 465 ✓ | 465 ✓ |
| build acc from borrowed src, then re-read SRC | 465 ✓ | 465 ✓ |
| multi-variant `Cell` (Given/Solved/Candidates) built, `vec-set` one, sum all | 535 ✓ | 535 ✓ |
| RC trace (`CRANELISP_RC_TRACE=1`) on a 2-element case | identical | identical |

**The decisive test — the exemplar itself.** I copied `exemplar/` to a tmpdir and
swapped **every** `vec-push`→`conj` (curated `collections.vec/conj`) across
`grid.cl`, `solver.cl`, `html.cl` — the exact change the DEF-2 carve-out forbids:

- `--run solver.cl` → solves the full 9×9 puzzle, valid grid, **exit 0**.
- `--run user.cl` (headline) → full valid solution + HTML page, **exit 0**.
- `--run tests.cl` (in-language runner, exit = pass count) → **exit 39** (39/39).
- A **200×** sustained build-and-sum of an 81-element `(Vec Cell)` via `conj`
  → **exit 0** (no slow corruption / accumulating heap rot).

The exemplar's "spurious No solution found / corrupted `(Vec Cell)`" does not
occur. DEF-2 is resolved.

#### Root cause of the resolution (CLIF / seam evidence)

DEF-2 lived in the same `vec-push`/`vec-set` heap-element consuming-inc seam
(`crates/cranelisp-backend/src/{vec_codegen.rs,vec_runtime.rs}`,
`vec_push_copy`/`vec_set_copy`) that **FIXME 0417** aligned in S87 — see the
existing guards `tests/spec_12_runtime.rs::vec_set_heap_element_borrowed_recursive_source_no_uaf`
(+ `…_run`) which document 0417's up-front-inc convention. The RC trace on the
conj-wrapper path shows balanced alloc/dec/free with no premature element free;
the wrapper's call frame inc's its heap-ADT argument and `vec-push` consumes it
symmetrically. The "wrapper-RC mis-count" hypothesis (the candidate `/backend`
owner) is **not present in the current codegen**. No CLIF anomaly remains to
inspect — the convergence is the absence of the asymmetric dec.

#### Tests authored (GREEN guards, NOT failing-not-ignored)

Per `/qa` §Failing-not-ignored, **a fixed defect earns a regression guard, not a
RED**. Authoring a RED for DEF-2 would be a false regression. The guards pin the
now-correct heap-ADT-through-the-wrapper behaviour so a future regression of the
0417 seam flips them RED. Free-standing (inline `Box`/`Cell` types + inline
`conj` wrapper; zero stdlib dependency per CLAUDE.md §Stdlib separation):

| Test | Tier | Shape | Asserts |
|---|---|---|---|
| `tests/spec_12_runtime.rs::conj_wrapper_heap_adt_element_matches_vec_push_repl` | REPL | `(Vec Box)` conj-built vs push-built, 30 iter | conj-sum − push-sum == 0 (`:primitives/Int 0`) |
| `tests/spec_12_runtime.rs::conj_wrapper_heap_adt_element_sum_run` | `--run` | `(Vec Box)` conj-built, 30 iter, sum | exit 209 (465 mod 256) |
| `tests/spec_12_runtime.rs::conj_wrapper_multivariant_cell_vec_built_correctly_run` | `--run` | multi-variant `Cell` conj-built + `vec-set`, sum all | exit 23 (535 mod 256) |

All three **GREEN on HEAD**. `// spec: spec/12-runtime.md §12.3.3 / §12.1.5`.
→ `/backend` named as the owning seam (vec heap-element consuming-inc; the FIXME
0417 surface) should a regression appear.

#### Handoff to `/sprint`

- **No `/backend` (or `/typecheck`, or RC-fusion) triage to dispatch** — there is
  nothing to fix. The R1 owner-disambiguation resolves to "already fixed."
- **Stage A exit gate (DEF-2 half) is met by the GREEN guards** — not by flipping
  a RED. `/sprint` should record DEF-2 as resolved-collaterally-by-0417.
- **Stage D / Phase 6b G2 swap is UNBLOCKED:** `/port` can swap the exemplar's
  `vec-push`→`conj` at the ~5 heap-ADT accumulator sites and retire the DEF-2
  carve-out in `exemplar/CLAUDE.md` + the `grid.cl`/`solver.cl`/`html.cl` carve-out
  comments. (Verified above: the full swap solves + passes 39/39.)

### 2. 0423 — `(mod test)` extraction writes CWD-relative, not lib-dir-relative

**Reproduces on HEAD. Owner: `/int` (as the FIXME states). RED guard authored.**

| Test | Tier | Asserts |
|---|---|---|
| `tests/spec_08_modules.rs::inline_mod_test_extraction_writes_lib_dir_relative_not_cwd` | `--run` | (+) backing file at `lib/accum/test.cl`; (−) NO stray `accum/test.cl` at the CWD root |

**Repro layout (matches the harness CWD model):** a lib-dir module
(`lib/accum.cl`, on `CRANELISP_LIB` via `.lib_dir("lib")`) declares an inline
`(mod test …)` body; the `--run` driver (`driver.cl`) sits at the tmpdir ROOT,
which is the process CWD. CWD (tmpdir) ≠ lib-dir (tmpdir/lib). After the run the
extractor writes the stray backing file at `<cwd>/accum/test.cl` instead of
`<lib-dir>/accum/test.cl`. The parent rewrite (to bare `(mod test)`) DOES
correctly target the lib-dir copy — only the backing-file write mis-resolves
against the CWD.

**Observed RED (HEAD):** the `lib/accum/test.cl` positive assertion fires —
"the extracted `(mod test)` backing file MUST be written LIB-DIR-relative" — and
a manual reproduction confirms the stray `accum/test.cl` lands at the CWD root.
This is the concrete evidence behind the stray `./collections/ ./num/ …` repo-root
cruft the S87 close band-aided with a `.gitignore` guard.

`// spec: spec/08-modules.md §8.2.2` — extraction step 1 writes
`{parent_dir}/{stem}/{name}.cl`; `{parent_dir}` is the parent module's OWN
directory (the lib-dir for a lib-dir module), never the process CWD. (FIXME 0423
itself cites §8.2.5; §8.2.2 step 1 is the load-bearing requirement — the write
location — so the test cites §8.2.2.)

**Secondary symptom CONFIRMED (separate, noted for the `/int` fix pass):** the
regen pretty-printer emits a SPACE after `:` for a PARENTHESIZED type expression
— a `(mod test)` body with `(defn check [:(Option String) x] …)` regenerated as
`[: (Option String) x]`. Per `memory/annotation-reader-macro-binds-following-form`,
`:Type` binds the immediately-following form with NO space; `: (Option String)`
is a latent formatting divergence. A BARE type name (`:Int`) regenerates
correctly (no space) — only the parenthesized form is affected. Not separately
tested here (the lib-dir-relative write is the primary 0423 defect; the spacing
rides the same regen-path fix), but flagged so the `/int` fix addresses both.

Per `memory/feedback_no_fixme_with_failing_test`, the RED test IS the record +
trigger; no paired FIXME needed (0423 already exists as the cross-skill request
that named the defect; its resolution deletes it when `/int` lands the fix).

---

## Stage B/C — Agent-feature test PLAN (no implementation this step)

> **Track-wide strategy:** the four-lane testing strategy for the entire
> agentic-REPL track (S88→S90 — the deterministic stub `CompletionModel`, Lanes
> A/B/C/D, and the rung→lane mapping) is in
> `tests/plan/agent-testing-strategy.md`. The rows below are the S88-specific
> draft; the strategy doc is the durable record Wave 3 / S89 / S90 build against.

These tests live behind `#[cfg(feature="agent")]` in a SEPARATE lane. The default
`cargo nextest run` stays agent-free (no `agent` in any crate's `default`, no
dev-dep enables it — `repl-embedded-agent.md §7`, /arch Phase-2 verdict). **PLAN
ONLY** — these are Phase-5 / Stage-C deliverables, written when the classifier +
`src/agent/` land. Drafted now so the per-crate triads have acceptance criteria.

### Lane mechanics

- A new test file `tests/agent.rs` gated `#![cfg(feature = "agent")]` at the top
  (the whole file compiles out by default). Subprocess-only (the e2e tier — no
  Rust API), driving the binary built `--features agent`.
- The `--features agent` build is a SEPARATE nextest invocation (a CI lane /
  `--features agent` profile), never the default suite. The binary under test for
  this lane is `target/debug/cranelisp` built with the feature.
- **Dormant-without-key discipline:** most routing/wiring tests must NOT require a
  live LLM key (they assert the deterministic seams — classifier routing, `/ask`
  feature-off message, pull-as-command rendering). Only the end-to-end "Advisor
  answers" acceptance test needs a key; gate it additionally on a runtime
  env-var presence check and `#[ignore = "needs CRANELISP_AGENT_KEY"]` when
  absent (the ONE legitimate ignore — a backend-credential gate, not a spec gap).

### §5.3 classifier routing (`/int` + `/repl`)

The classifier (`classify(line, buffer_state)` — `repl-embedded-agent.md §5.3`)
routes by "parses as a complete form or a slash command → REPL; else → agent."
Zero regression of `repl/spec.md §4` (the bare-atom self-doc surface).

| Planned test | Asserts (feature ON) |
|---|---|
| `agent_routes_complete_form_to_repl` | `(add-i64 1 2)` → REPL eval (`:primitives/Int 3`), NOT the agent |
| `agent_routes_slash_command_to_repl` | `/list` → the existing command, NOT the agent |
| `agent_routes_prose_to_agent` | multi-word prose ("how do I define a function") → `Agent(text)` arm (two bare symbols = parse error → agent) |
| `agent_unclosed_paren_is_continuation_not_agent` | `(add-i64 1` → Continuation (parens-balanced gate), NOT the agent |
| `agent_ask_escape_hatch_forces_agent` | `/ask why` (bare single word that would otherwise self-doc) → agent |
| `agent_bare_atom_self_doc_preserved_neg` | bare `add-i64` (no `/ask`) STILL self-documents per `repl/spec.md §4` — the agent does NOT intercept it (negative: the §4 surface is untouched) |
| `agent_off_ask_prints_not_built_in` | feature OFF: `/ask why` → "agent not built in"; `(foo bar baz` other-parse-error → today's byte-identical parse-error display (the `Err(other)` fallback, /arch's byte-identical-by-construction claim) |

The last row is the load-bearing guard for the four-cut feature graft: with the
feature OFF the binary is byte-identical to today on every non-`/ask` input.
A version of `agent_off_ask_prints_not_built_in` runs in the DEFAULT lane (no
`--features agent`) — it is the one agent-named test that belongs in the agent-free
suite because it pins the feature-OFF contract.

### Pull-as-visible-command wiring (`§4.4`)

A pull (the agent reaching for `/source`/`/info`/`/refs`/…) synthesizes a REPL
command run through the SAME `process_commands` path and rendered as if typed
(`repl-embedded-agent.md §4.4`, §5 `agent_turn`).

| Planned test | Asserts |
|---|---|
| `agent_pull_renders_as_typed_command` | an agent turn that needs a symbol's source emits the `/source <sym>` line in the transcript, echoed as if the user typed it, with the command's normal output following |
| `agent_pull_goes_through_process_commands` | the pulled command inherits cluster-atomic staging + error recovery (a pull of a bad command surfaces the normal command error, not an agent-internal one) |
| `agent_pull_read_only_in_advise_mode_neg` | in read-only Advise mode (the S88 MVP), NO write command (`(defn …)` submission) is auto-submitted — proposed code is SHOWN, not run (negative: nothing enters the symbol table without confirmation) |

### Module-preamble read / edit (`§3.4`, U2)

Gated on the `/spec`-owned normative module-preamble form (Step 3.1 `/spec`
deliverable) + the R2 `SymbolTable.module_preamble` storage field (Phase-3 `/arch`).

| Planned test | Asserts |
|---|---|
| `agent_doc_module_reads_preamble` | `/doc <module>` prints the module's preamble text |
| `agent_doc_module_absent_preamble_neg` | `/doc <module>` on a module with no preamble → a clean "no preamble" message, NOT an error / empty crash |
| `agent_preamble_edit_path_round_trips` | the preamble edit path writes the preamble and a subsequent `/doc <module>` reads it back (persists across the module's backing-file regen — ties to the 0423 fix: the preamble write must also be lib-dir-relative) |

### Reverse-query commands `/refs` · `/tests-for` (`§4.4` corollary)

On-demand scan over in-memory bodies (no maintained reverse index —
`repl-embedded-agent.md §4.4` impl note). These GROW the REPL for everyone, so
they ALSO get default-lane (agent-free) coverage — they are plain introspection
commands, not agent-only.

| Planned test | Lane | Asserts |
|---|---|---|
| `refs_lists_referencing_symbols` | DEFAULT (agent-free) | `/refs <sym>` after defining two fns that call `<sym>` → both caller names listed |
| `refs_excludes_non_referencing_neg` | DEFAULT | `/refs <sym>` does NOT list a fn that never mentions `<sym>` (negative — the scan is precise) |
| `tests_for_lists_test_functions` | DEFAULT | `/tests-for <sym>` → the `test-*` fns whose bodies reference `<sym>` |
| `tests_for_empty_when_no_tests_neg` | DEFAULT | `/tests-for <sym>` with no referencing tests → clean empty result, not an error |
| `agent_pulls_refs_during_turn` | `agent` | an agent turn pulls `/refs` and renders it as a visible command (ties the reverse-query into the pull-as-command path) |

`/refs` + `/tests-for` are the one Stage-B sub-deliverable whose default-lane
tests can be authored as soon as the commands land (they are LLM-free), even
ahead of the rest of the agent lane.

---

## Verification (Step 3.1)

- `cargo nextest run --test spec_12_runtime -E 'test(conj_wrapper)'` → 3 GREEN.
- `cargo nextest run --test spec_08_modules -E 'test(inline_mod_test_extraction…)'`
  → 1 RED (the 0423 failing-not-ignored guard).
- `python3 tests/plan/spec_link_check.py --scope spec_12_runtime.rs` → clean.
- `python3 tests/plan/spec_link_check.py --scope spec_08_modules.rs` → clean.
- `cargo check --tests` → no warnings in the touched files.
- Full `--workspace` suite: S87 baseline 2870/0/0 + **1 new RED** (0423) — the
  3 DEF-2 guards are GREEN (not reds). So the close-time expectation is
  **2873 passed / 1 failed / 0 skipped** (one intentional failing-not-ignored
  guard: 0423). DEF-2 adds NO red (resolved).

## Ledger note (for `/qa` to fold into `ledger.md` at close)

- DEF-2: **resolved collaterally by FIXME 0417** (S87); 3 GREEN guards added; no
  RED, no owner triage. Stage D G2 swap unblocked.
- 0423: RED guard `inline_mod_test_extraction_writes_lib_dir_relative_not_cwd`;
  `out-of-scope (owner=/int)`; target S88 Stage A fix.
