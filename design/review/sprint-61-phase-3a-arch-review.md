# Sprint 61 Phase 3a — /arch Design-Doc Review

**Reviewer**: /arch
**Date**: 2026-04-22
**Scope**: Four design docs for Slices 0, 1, 3
**Verdict**: APPROVE

## Summary

All four Phase 2 FIXME(/arch) items are RESOLVED in-doc. Four docs are clean
on crate boundaries, Principle 8 durability, and interface stability — no
boundary-type changes are proposed; no serialised-format leakage; no
cross-crate coupling introduced. The Slice 3 skeleton correctly defers
hypothesis selection to post-evidence and records the update protocol in
§6. Cross-doc consistency between `observability.md` and
`io-trampoline-trace.md` is strong: same timestamp anchor, same
`ThreadId` domain, compatible merge-sort semantics. Residual FIXME(/arch)
items blocking Wave 2: **none**. Wave 2 implementation may open.

## Per-doc review

### design/int/observability.md

**FIXME(/arch) #1 (crate placement)**: **RESOLVED.** §4 contains a
pinned architectural-decision table (scheduler log → `src/`; IO log →
`cranelisp-runtime`), and §4's hard-constraints list enumerates the
four prohibitions: no boundary-type appearance, no serialised-format
appearance, no `cranelisp_alloc` usage, explicit `Send + Sync`. The
§3.1 and §3.2 code-site paragraphs restate this at the point of
implementation guidance — drift resistance is good. The `io_trace.rs`
rename (over `trace.rs`, which hosts the `(trace ...)` special form)
is documented in §3.2 with rationale.

**FIXME(/arch) #2 (env-var parse-once)**: **RESOLVED.** §5 specifies
the `OnceLock<TraceFilter>` pattern in full, with Rust sketch, and
explicitly names the prohibition: "Per-event parse is forbidden." §2's
inventory grounds the pattern in the existing six trace vars (frames
the new two as consistent, not novel). The phrase "reads the env var
**once** at session start... and stores a parsed filter" matches the
`tests/CLAUDE.md §"Diagnostic Logging"` convention.

**Principle 8**: **PASS.** §12 explicitly argues durability: scheduler
event taxonomy tracks persistent-worker topology (stable Ring 4
onwards per Decision 27 / `pipeline-v4.md §3`); IO event taxonomy
tracks spec-frozen surface (`spec/10-effects.md §10.12`, §10.10). The
infrastructure is declared a standing inspection instrument, not
Sprint 61 scaffolding. The framing aligns with the six existing trace
vars — this is a continuation of an established pattern, not a new
architectural layer.

**Crate boundaries (Principle 3)**: **PASS.** §4 hard-constraints list
names the prohibition four times (boundary types, serialised formats,
Cranelisp-heap allocation, `Send + Sync` explicit). §6 also confirms
that each crate owns its own event struct — NOT a shared type in
`cranelisp-types`. Correct.

**Interface stability**: **no changes required.** §4 confirms the
scheduler log lives as thread-local state in `src/observability.rs`
(new); the IO log lives as thread-local state in
`crates/cranelisp-runtime/src/io_trace.rs` (new). No `cranelisp-types`
changes, no `SymbolTable` additions, no `CacheEntry` field.

**Sketch comparison**: **adequate.** §8 cites the sketch's ad-hoc
`eprintln!` pattern in `sketch/src/session.rs` and justifies divergence
by the concurrent-topology shift. Meets `CLAUDE.md §"Sketch Oracle"`.

**Testability**: **adequate.** §10 gives two command-level acceptance
criteria (scheduler trace on `sprint23::cache_repl_loads_heisenbug_parallel_stress`;
IO trace on `examples/21-hello-io.cl`), the < 1% off-path regression
bound with a verification procedure in §9, and names unit-test shapes
inside each crate (bounded-capacity drop counter, `Send + Sync`
compile-time check, parse-once assertion). `/qa` can derive from
these directly.

**Concerns**: none.

### design/backend/io-trampoline-trace.md

**FIXME(/arch) #2 (env-var parse-once, /backend side)**: **RESOLVED.**
§2 contains an explicit "Parse-once discipline (resolves
`FIXME(/backend)` from `/arch` Phase 2 review)" paragraph and includes
the `OnceLock<Option<TraceFilter>>` shape sketch. The
`tests/CLAUDE.md §"Diagnostic Logging"` citation is present. Named
prohibition: "Per-event string parsing is forbidden." Matches
/int-side treatment in `observability.md §5`.

**Principle 8**: **PASS.** §3 event taxonomy is grounded in
`io.rs::run_io_trampoline` and `spec/10-effects.md §10.12` / §10.10 —
both surfaces stable per `/arch` Phase 2 review. §10 names the log as
the "instrument" for Slice 4 investigation; no scaffolding disposable
at close.

**Crate boundaries (Principle 3)**: **PASS.** §5 is unambiguous:
`cranelisp-runtime` only, new file `io_trace.rs`, thread-local ring
buffer, forbidden appearance in `cranelisp-shared` / `cranelisp-types`
/ any serialised format, events NEVER go through `cranelisp_alloc`
(avoiding RC-trace recursion). §4 also confirms `IoTraceEvent` has no
`Serialize` and does not appear in `CacheEntry` / `Code` /
`SymbolTable`.

**Interface stability**: **no changes required.** All state is
runtime-internal. No ABI change. The Decision 26 `scheduling_class`
+ `platform_fn_ptr` shape is payload-observed, not modified.

**Sketch comparison**: **adequate.** §8 documents the sketch's single
`eprintln!` on the panic-shape error path and justifies divergence
by (a) `rayon`-backed Par dispatch (Decision 26), (b) persistent-worker
subprocess topology (Decision 27), (c) the exit-201 intermittent race
that motivates instrumentation. Rationale stated at the correct
granularity.

**Testability**: **adequate.** §9 names four acceptance criteria: full
event sequence on `21-hello-io.cl`, < 1% off-path regression (5-run
wall-clock median), merge-sort compatibility with /int's scheduler
trace (shared `Instant` anchor + `ThreadId` domain — explicit cross-doc
contract), and a `cargo check -p cranelisp-runtime` zero-warnings
implementation gate.

**Concerns**: none.

### design/int/bare-primitive-value-path.md

No Phase 2 FIXME(/arch) was assigned to Slice 1. Review focuses on
standard dimensions.

**Principle 8**: **PASS.** The doc describes a single-site alignment
inside `src/session_v4.rs::check_bare_symbol_introspection`
(l.2179). No scaffolding; the fix collapses divergent paths onto the
same resolution mechanism. §3's reference to the Sprint 59
`dual-path-persistence-collapse.md` anti-pattern confirms this is
convergence, not new surface.

**Crate boundaries (Principle 3)**: **PASS.** §4 and §9 both state
"No boundary-type change. No `SymbolInfo` / `ModuleEntry` / `FQSymbol`
shape change." Single-site `src/`-only fix.

**Interface stability**: **no changes required.** The doc is explicit.
`FQSymbol.module` attribution is an internal data-flow fix, not a
type-shape change.

**Sketch comparison**: **thin but acceptable.** The sketch shares
`session.rs` as the ancestor of the affected code. The doc does not
contain an explicit §"Sketch comparison" heading, which strictly
violates `CLAUDE.md §"Sketch Oracle"`. However the problem is a
dual-path collapse fix — a class of problem explicitly documented as a
reimplementation-specific anti-pattern (`dual-path-persistence-collapse.md`)
that postdates the sketch. The sketch has no equivalent three-path
bare-value vs. introspection vs. call split (its single-threaded REPL
eval takes one code path). **Recommendation (non-blocking)**: add a
one-paragraph "Sketch comparison" section stating the sketch has no
equivalent divergence and citing the dual-path anti-pattern doc for
context. This is a Wave 2 doc-hygiene item, not a Phase 3a blocker
— the architectural content is sound.

**Testability**: **adequate.** §7 names the test shape (narrow
integration test launching a REPL subprocess, types bare name,
asserts stdout contains type-annotated qualified name) and the symbol
sample (`add-i64`, `eq-i64`, `mul-i64`, `sub-i64`, `int-to-string`,
`str-concat`). §5's expected-output format cites `repl/spec.md §1.1`
verbatim — `/qa` can derive the assertion string directly.

**Concerns**: Sketch-comparison section is thin (see above). One
minor ambiguity in §3: the diagnosis fork ("which of the two
divergences holds") is deferred to Slice 1's isolation step. This is
correct — evidence precedes fix choice — but the doc should make
explicit that if Slice 1's isolation reveals BOTH divergence paths
are active (one symbol misrouted, AND another fall-through rejected),
the fix widens to cover both. Currently §4 implies an either/or
choice. Non-blocking; a comment during Wave 2 implementation is
sufficient.

### design/int/heisenbug-race-closure.md

**FIXME(/arch) #3 (evidence-gated hypothesis naming)**: **RESOLVED.**
§6 ("Evidence-gated discipline") is a whole dedicated section that
tracks the Phase 2 FIXME, quotes the gate text verbatim, and names
the doc-update protocol: add §7 Evidence with trace excerpt, add §8
Chosen hypothesis with rationale, remove the §4 fix sketches for
rejected hypotheses (keep in git history), and ONLY THEN open the
fix. Rejection of skip-gated implementation is explicit: "Skipping
this gate — implementing a fix without event-log evidence — is
exactly the behaviour `/arch` review rejects." Auditability via git
blame is named. This is the correct discipline, correctly recorded.

**Three hypotheses named with distinguishing criteria**: **yes.** §2
names H1 (`is_typechecked` too permissive), H2 (symbol publication
outside critical section), H3 (pool transition before symbol
publication). §3's falsification rules give each hypothesis a
distinguishing event-log signature: H1 = `is_typechecked → true` with
empty symbol table; H2 = flip event before insertion event on
consistent timeline; H3 = structural inspection of worker loop shows
unconditional flip-before-merge. Good.

**Per-hypothesis fix sketch names touched files**: **yes.** H1 fix
touches `src/scheduler.rs::is_typechecked`. H2 fix touches
`src/session_v4.rs::SharedState`, `src/worker.rs`. H3 fix touches
`src/worker.rs` around `notify_typecheck_done` (l.3440). Each fix
sketch names a specific risk (H1 ordering sensitivity, H2 lock
contention, H3 waiter wake-up race).

**Boundary concerns enumerated**: **yes.** §5 enumerates per-hypothesis
boundary impact:
- H1: uses `SymbolTable::symbols.is_empty()` (already public DashMap
  API) — no shape change.
- H2: inside `src/scheduler.rs` + `src/worker.rs` + `SharedState` —
  existing locks only; no new sync primitive on a `cranelisp-types`
  boundary.
- H3: statement reorder in `src/worker.rs` — no boundary change.

Pre-authorisation explicitly: "none." FIXME(/arch) gate before any
`cranelisp-types` touch is named. Exactly what Phase 2 asked for.

**Principle 8**: **PASS.** The race closure is a completion of existing
publish-before-register discipline (Sprint 58 W6 Defect 1, Sprint 59
Workstream A §7, Sprint 60 Wave 2 Round 4). Not scaffolding; it is
the final state of a multi-sprint correctness-hardening thread. §7's
cross-reference trail is thorough.

**Crate boundaries (Principle 3)**: **PASS.** See §5 above.

**Interface stability**: **no changes required** (with the
pre-authorisation gate if evidence changes the picture).

**Sketch comparison**: **thin.** The doc does not have an explicit
§"Sketch comparison" section. The sketch has no equivalent
persistent-worker scheduler, so there is no sketch solution to
compare against — this is reimplementation-specific concurrency.
**Recommendation (non-blocking)**: add a one-paragraph
§"Sketch comparison" noting the sketch's absence of persistent-worker
topology (single-threaded session, see `sketch/audits/`) means there
is no sketch-side race of this shape; the reimplementation's
concurrent topology is itself the divergence and the three hypotheses
are endemic to it. Similar to Slice 1: doc-hygiene item for Wave 2,
not a Phase 3a blocker. The architectural content satisfies Phase 2
review.

**Testability**: **adequate.** §8 names the 10-run slice gate,
20-run close-gate contribution, and the evidence-artefact commit
path (`tests/sprint61/race-evidence/{failing,passing}.trace`) — the
artefact persistence is a nice touch for post-hoc audit.

**Concerns**: Sketch-comparison section is thin (see above). One
consistency question: §3 step 2 declares the artefact path as
`tests/sprint61/race-evidence/` and says this is "outside
`.gitignore`d paths." Phase 3 readout in SPRINT.md confirms `.gitignore:31`
covers `tests/sprint60/.runs/` only; `tests/sprint61/race-evidence/`
is indeed uncovered. This is intentional per the doc. Non-issue for
/arch; flagging only so `/qa` can confirm in Wave 2 the path survives
Slice 5 E-1 tempdir-audit edits.

## Cross-doc consistency

`observability.md` (/int) and `io-trampoline-trace.md` (/backend) are
companion docs that must agree on shared mechanics. Verified:

- **Timestamp domain**: both docs specify monotonic nanoseconds from
  `std::time::Instant`, anchored at process start.
  `io-trampoline-trace.md §9` names the anchor explicitly as "a
  runtime-exported `OnceLock<Instant>`" — this is the shared-anchor
  contract. `observability.md §6` names the same mechanism
  (`duration_since(ORIGIN)`). **Agree.** Recommendation
  (non-blocking): at implementation time, the two crates should
  depend on a single exported `Instant` rather than each observing
  its own `Instant::now()` at init — otherwise the two anchors drift
  by whatever wall-clock difference exists between the two
  `get_or_init` calls. The docs imply but do not mandate shared
  anchor; a one-line clarification during Wave 2 would eliminate
  ambiguity. Natural home: `cranelisp-runtime` exports the anchor;
  `src/` imports it. No `cranelisp-types` change required.

- **Thread-id domain**: both docs use `std::thread::ThreadId`.
  `io-trampoline-trace.md §4` specifies this by type;
  `observability.md §6` uses `ThreadId::as_u64().get()`. **Agree** —
  the merge-sort at dump time tolerates either representation as long
  as the two dumps are sorted by `(timestamp_ns, thread_id)`
  consistently.

- **Merge-sort semantics**: both docs specify
  `sort_by_key(|e| (e.timestamp, e.thread_id))` semantics at dump
  time. **Agree.**

- **Dump mode**: `observability.md §7` specifies scheduler log dumps
  on test failure (one shot); `io-trampoline-trace.md §6` specifies
  IO log streaming per-event (mode A) or crash-resilient per-event
  flush (mode B, reserved). **Different by design** — each log's
  dump strategy matches its consumption shape (races fire and leave
  evidence in the scheduler log; subprocess exits lose in-memory
  state and need streaming). No contradiction.

- **Allocator discipline**: both docs forbid `cranelisp_alloc`. **Agree.**

- **Env-var parse-once**: both docs specify `OnceLock`-backed
  single-parse-at-init. **Agree.**

- **Crate placement**: both docs agree scheduler log is `src/`, IO
  log is `cranelisp-runtime`; neither appears in boundary types or
  serialised formats. **Agree.**

No contradictions. One clarification point (shared `Instant` anchor
wiring, above) is a Wave 2 implementation concern, not a Phase 3a
design gap.

## Residual FIXME(/arch) items — blocking Wave 2

**None.**

Two non-blocking recommendations carry to Wave 2 implementation /
doc-hygiene:

1. **`bare-primitive-value-path.md`** lacks an explicit "Sketch
   comparison" section (strictly required by `CLAUDE.md §"Sketch
   Oracle"`). The architectural content is sound; adding a
   one-paragraph section stating "sketch has no equivalent three-path
   divergence; see `dual-path-persistence-collapse.md`" satisfies
   the convention. /int to append during Wave 2.

2. **`heisenbug-race-closure.md`** lacks an explicit "Sketch
   comparison" section. Sketch has no persistent-worker topology, so
   no equivalent race exists. /int to append a one-paragraph note
   during Wave 2 or as part of the §7/§8 post-evidence update.

Both are doc-hygiene items that do not block Wave 2 opening. Neither
is a FIXME(/arch) — they are /int self-improvements per the sketch
consultation convention.

## Recommendations to /sprint

1. **Open Wave 2.** All four Phase 2 FIXME(/arch) items are resolved;
   no boundary-type changes are pre-authorised (none requested);
   no blocking architectural concerns. Wave 2 may open on /int's
   Slice 0 + Slice 1 implementation tracks, and /port's Slice 2 can
   run in parallel per the existing execution-order plan.

2. **Share `Instant` anchor across crates.** Before Slice 0
   implementation commits land, /int and /backend should confirm the
   shared `OnceLock<Instant>` lives in `cranelisp-runtime` and is
   imported by `src/`. Otherwise the two dumps will have drifted
   anchors and merge-sort correlation will be noisy. Surface this in
   Wave 2 readout; it is a one-line API point, not a design change.

3. **Slice 1 fix-scope ambiguity.** /int's `bare-primitive-value-path.md`
   §3–§4 leaves the divergence diagnosis open (two candidates). If
   Slice 1 isolation reveals both candidates are in play, the fix
   must cover both — the current §4 implies either/or. Worth naming
   in the Slice 1 readout.

4. **No sprint-scope adjustment.** The architectural content across
   the four docs is internally consistent, externally consistent with
   /arch Phase 2 review, and the evidence-gated discipline on Slice 3
   is correctly recorded. No wave-sequencing change.

5. **Slice 4 correctly deferred.** No design doc authored yet; the
   instrument (`io_trace.rs`) is being built to produce the evidence
   that will pick the hypothesis. /arch will review whichever doc
   lands at Slice 4 readout. No preemptive action needed in Wave 2.

End of review. Wave 2 may open.
