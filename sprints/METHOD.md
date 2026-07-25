# Cranelisp Delivery Method

> **Owner**: `/sprint`.
> **Scope**: how we deliver — skills, sprint phases, artifacts and memory.
> **Out of scope**: architectural rules (`/arch` in `design/arch/`), per-crate implementation design (`/design` in `design/{crate}/`), agent-facing workflow detail (`.claude/commands/{skill}.md`). This document points to these rather than restating them.

---

## Table of contents

1. [Skills and roles](#1-skills-and-roles)
2. [Sprint phases](#2-sprint-phases)
3. [Artifacts and memory](#3-artifacts-and-memory)

---

## 1. Skills and roles

### 1.1 Inventory

14 skills.

| Skill | Category | Owns | Output |
|---|---|---|---|
| `/spec` | Authority (scribe) | `spec/` | Normative spec text, scribed — the **user** arbitrates semantics; `/spec` records and frames open questions as prose |
| `/arch` | Authority | `design/arch/`; `crates/cranelisp-types/`; public-API surfaces of every crate | Interface types, principles, Decisions, public-API approvals |
| `/qa` | Authority | `tests/plan/` (incl. `PLAN.md`, the normative spec → tests bridge) | Test strategy, risk assessment, coverage process & traceability audit, defect attribution & cross-crate triage briefs |
| `/testing` | Test production | Test sources under `tests/` (files, fixtures, helpers); `tests/CLAUDE.md` | Spec-traceable e2e tests authored to `/qa`'s plan; repro isolation & reduction; `// defect:` notation upkeep (`tests/CLAUDE.md` §"Defect-repro notation"; ledger retired S108) |
| `/audit` | Authority | `audits/` | Rolling whole-context assessments with recommendations (one bounded context per sprint; see §2.6) |
| `/design` | Per-crate triad — design role | `design/{crate}/{crate}.md` for all 6 crate-shaped surfaces (narrow deployment) | Crate overview + subordinate topic docs; does not edit code |
| `/dev` | Per-crate triad — implementation role | All 6 crate-shaped surfaces (narrow deployment) — see §1.3 | Implementation code + unit tests |
| `/review` | Per-crate triad — review role | All 6 crate-shaped surfaces (narrow deployment); no persistent directory | Quality findings on a round of change against design intent + accumulated state. Review execution is delegated to the external Codex reviewer; the invoking agent adjudicates the verdict and files the FIXMEs (`.claude/commands/review.md` §Delegated execution, ratified 2026-07-25) |
| `/sprint` | Coordination | `sprints/` | Sprint plans, wave organization, FIXME orchestration, outcome reports |
| `/stdlib` | User-proxy | `stdlib/` | Standard library |
| `/examples` | User-proxy | `examples/` | Learning-sequence examples |
| `/docs` | User-proxy | `user/` | User-facing documentation |
| `/repl` | User-proxy | `repl/` | REPL experience spec, demos, harness |
| `/port` | User-proxy | `exemplar/` | Showcase project |

### 1.2 Categories

- **Authority** (`/spec`, `/arch`, `/qa`, `/audit`) — arbitrate correctness and quality. Together they link the spec → architecture → release candidate. `/spec` is a **scribe**: its arbiter is the user, never itself. `/audit` judges accumulated whole-context state, one bounded context per sprint (§2.6).
- **Per-crate triad** (`/design`, `/dev`, `/review`) — generic skills, narrow-deployed one crate per invocation. Same triad shape applied to whichever crate is in scope.
- **Test production** (`/testing`) — authors the e2e suite and repro reductions to `/qa`'s plan, sprint-wide rather than per-crate.
- **Coordination** (`/sprint`) — orchestrates the sprint archetype. Owns no code or design content; routes technical questions to the appropriate authority.
- **User-proxy** (`/stdlib`, `/examples`, `/docs`, `/repl`, `/port`) — exercise the language outside-in. Operate during the user-facing phase of each sprint.

### 1.3 Per-crate triad

Three skills (`/design`, `/dev`, `/review`), one definition each, each invocation focused on exactly one crate. Per-crate specialization lives in `design/{crate}/{crate}.md` (the design doc) and `crates/{crate}/CLAUDE.md` (or `src/CLAUDE.md`), not in the skill definitions.

The crate-shaped surfaces (7 crates; the two runtime crates form one backend-paired runtime surface):

- `cranelisp-frontend`
- `cranelisp-typecheck`
- `cranelisp-backend`
- `cranelisp-primitives` + `cranelisp-intrinsics` — the **backend-emitted runtime library** (S73 Decision-43 split of the former `cranelisp-runtime`). **Paired with backend, NOT `/int`**: `cranelisp-backend` depends on these crates and emits calls into them (BC §4a/§4b — "backend declares them as imports"; the dep graph confirms it). `/int` is only a *host-client* of the runtime (constructs `HostCtx`, drives `block_on_reactor`) — it does not own the runtime library, and the IO-runtime internals (reactor, `consume_io_tree`, RC) are not an `/int` concern. See FIXME 0486 for the boundary review + the design-doc relocation.
- `cranelisp-platform` (consumer of runtime, not owner)
- `src/` (binary crate — pipeline, REPL, CLI, session; **host-client** to the runtime, not its owner)

Cross-crate work splits into sequential per-crate triad invocations, coordinated by `/sprint`. Any required interface change goes through `/arch` (in the types crate) before per-crate work proceeds.

### 1.4 Three-way content split

Three kinds of skill-relevant content, three distinct homes. This is the rule that lets generic narrow-deployment skills carry per-crate weight.

| Content kind | Lives in | Example |
|---|---|---|
| **How to work** (process, agent procedures) | Skill definition (`.claude/commands/{skill}.md`) | "Confirm the crate in scope, read the design doc, then proceed." |
| **What to decide** (direction, codified design decisions) | Per-crate design doc (`design/{crate}/{crate}.md`) | "RC discipline: borrowed-vs-consumed-vs-unique tracking." |
| **How the code is** (data structures, invariants, conventions) | `CLAUDE.md` per directory | "Cranelift v0.125: `jump`/`brif` take `IntoIterator<Item = &'a BlockArg>`." |

When in doubt: process / "before doing X, do Y" → skill definition; decision / target shape → design doc; mechanical / API-surface / convention → `CLAUDE.md`.

### 1.5 Model allocation

Which model tier each skill runs on, per-dispatch escalation triggers, and the
`.claude/agents/` shim contract are **normative in `sprints/artefacts.md`**
(ratified 2026-07-11): the allocation table §II.3, escalation §II.4, shims
§II.2, and the `/audit` rolling cycle §I.7/§II.1. Any model-tier change
requires user sign-off. `/sprint` records non-default dispatches in the
`SPRINT.md` dispatch log and audits frontmatter against the table at close.

---

## 2. Sprint phases

Every sprint follows seven phases. `/sprint` orchestrates by issuing skill invocations and gating between them.

### 2.1 Phase table

| Phase | Name | Agent invocations | Outputs | Exit gate |
|---|---|---|---|---|
| 1 | Scope | `/sprint` | `SPRINT.md` DRAFT; disposition of the prior sprint's audit assessment (accepted recommendations → FIXMEs, declined → recorded; §2.6) | User approval of scope |
| 2 | Architecture review | `/arch` | Interface changes approved/deferred; scope adjustments | `/arch` sign-off on scope |
| 3 | Design | `/spec`, `/arch`, `/design` per crate touched, `/qa` | Updated spec / interface types / per-crate design docs / test plan reflecting sprint scope | `/arch` confirms public-API + interface set is complete; `/qa` has enough to draft failing tests; touched design docs current |
| 4 | Wave organization | `/sprint` | Wave breakdown in `SPRINT.md`; `SPRINT.md` ACTIVE | Waves written |
| 5 | Language phase | `/testing` first (sprint-wide: failing e2e tests to `/qa`'s plan). Then per crate, parallel: D/D/R cycle (`/design` refines → `/dev` implements → `/review`). Iterate within crate as needed. | Passing e2e tests; per crate: refined design, implementation, unit tests, change-set review findings, public-API diffs approved | `/sprint` (with user) takes the **authoritative judgment of what ships this sprint**. Subsequent phases take what is given. |
| 6a | User-facing assessment | `/repl`, `/port`, `/stdlib`, `/examples`, `/docs`, `/sprint`; `/audit` dispatched on the rotation context (§2.6) | Plan for user-facing artifacts against what shipped; gap FIXMEs filed in `design/arch/fixmes/`; audit assessment in `audits/` | Plan agreed; gap FIXMEs filed |
| 6b | User-facing action | `/repl`, `/port`, `/stdlib`, `/examples`, `/docs` | New sprint demo; exemplar update; stdlib / examples / docs updates; prior demos replayed green | All planned artifacts delivered; demos play green |
| 7 | Close | `/sprint` (with user) | Outcome report; archive; ROADMAP update; FIXMEs forward | User approval of close |

### 2.2 Phase notes

**Phase 1 — Scope.** `/sprint` scans open FIXMEs (`design/arch/fixmes/`) + prior-sprint archive for carries. Proposes the next increment.

**Phase 2 — Architecture review.** `/arch` reviews scope for technical coherence, interim-architecture risk, public-API impact. Updates `crates/cranelisp-types/` if new cross-crate interfaces are required.

**Phase 3 — Design.** Each invoked skill updates its own artifact to incorporate sprint scope. `/design` covers all 6 crate-shaped surfaces — the implementing skill (`/dev`) does not author design. `/qa` drafts a test plan from spec + design docs.

**Phase 4 — Wave organization.** `/sprint` organizes parallel work into waves (sets of skill invocations with no inter-dependencies).

**Phase 5 — Language phase.** **QA-first across the entire solution** — `/testing` authors the failing e2e tests upfront, sprint-wide, to the plan `/qa` produced in Phase 3 — then per-crate D/D/R cycle in parallel across crates. Phase 5 conclusion is **conscious and explicit**: `/sprint` and the user decide what ships. Defects are addressed in Phase 5 or deferred with explicit rationale; speculative refactoring deferred; emergent refactoring (the third instance of a duplicate, a function over budget) handled in-sprint.

**Test-coverage discipline within D/D/R (binding).** Every fix lands with a **unit test (mandatory)**, and the need for an **e2e test is assessed BEFORE the fix is written** — not after. The unit test pins the seam where the bug lived; the e2e (added when the bug is observable end-to-end or crosses `--run`/`--link`/REPL modes) proves the user-observable path. Write the failing test(s) first; the fix flips them green; test(s) and fix land in the **same change-set**. Deferring a fix's test to a follow-up FIXME (the "test owed" anti-pattern) is not permitted. This is the same-skill complement to §2.3's failing-not-ignored cross-skill rule. Source-touching `/dev`/`/testing` agents run **serially** (one at a time — shared working tree; see root `CLAUDE.md` §Testing); only read-only fan-outs parallelise.

**Repro before fix (binding, added S115).** **No defect is fixed before its minimal reproduction is committed** — and this holds most sharply for a defect the *fixing skill discovers itself*, mid-wave, while working on something else. That case is the one the older rules missed: §2.3 governs cross-skill *handoff*, root `CLAUDE.md` §"Usability Findings and Defects" governs *closure*, and the paragraph above governs the *fix's own* tests — none of them reaches the moment a `/dev` agent, three hours into a wave, finds two more defects beside the one it was sent for.

Sequence, binding on that moment: **reduce → commit the repro RED → then fix** (the fix flips it, same change-set, per the paragraph above). Reduction is not overhead on the way to the fix; it is three deliverables the fix alone cannot produce:

1. **The category, not the instance.** A fix written from an unreduced symptom fits that symptom. Reduction is what turned "the curried closure leaks" into "every box-minting kind is fresh only through a catch-all" — three further live defects in one stroke (S115 W3b). The reduced form is also what makes the failure's *family* visible, so the matrix cell (`/qa`'s variant×{pos,neg} discipline) can be drawn at all.
2. **The weakness in our testing method.** "Why did the suite not already have this?" is answerable only against a minimal case; against a sprawling one the answer is always "it's complicated." This is the sibling of the instrumentation question below, and its answers feed the same two homes.
3. **The regression guard.** The repro is the only artifact that survives the sprint. A fix without one is unguarded by construction, and the FIXME that promises the test later is the "test owed" anti-pattern §2.2 already forbids — a *measured, reproducible* defect recorded only as FIXME prose is that anti-pattern wearing a different hat (S115: FIXME 0760's two leaks lived as prose with exact numbers and no failing test until an audit caught it).

**Ownership must not become an escape hatch.** A skill commits the repro at the tier it owns (`/dev`: the unit tier, always) and **requests the missing tier in-wave** — `/testing` for e2e, `/qa` for attribution or matrix placement. `/sprint` schedules that request inside the same wave; routing it to "a FIXME for next sprint" is not an available answer for a defect that already has a measured reproduction. Where the repro cannot be reduced (genuinely intermittent, environment-dependent), that is a finding to record with the evidence — not a licence to skip the step.

**Enforcement lives at `/review`, not in good intentions**: a fix whose defect has no committed minimal repro in the same change-set is a **Blocker**, exactly as an unguarded narrowing is. `/dev`'s precondition is the same rule stated forward — *no fix without a repro.*

**A repro confirms a symptom; only a control confirms a mechanism (binding, added S115).** Reproduction is necessary and not sufficient, and the gap between them is where this project's misdiagnoses live. S115 alone: the entry-payload leak's two design-named mechanisms were both falsified by probe; the curry leak's root cause was an unbalanced protect *inc*, not the predicted missing dec; the RC sweep's named candidate (`is_heap_type`) was falsified; a residual predicted "benign accounting" was a real leak; two of three repro cells filed against typecheck turned out to be a backend syntactic-shape test; and the `'='` and 0719 root causes were both elsewhere than designed. In every case the symptom reproduced exactly as recorded — and the mechanism was wrong.

So an attribution carries, in addition to the repro:

1. **A discriminating control** — a sibling program identical to the repro *except* for the claimed cause, which behaves differently. The S115 diagnoses that held up all had one: the arm-swapped twin (order-dependence); the variant-B supersede with an unrelated ADT (isolating the flush from the match-consume); the plain-returned-lambda and global-target curries (isolating the leak to the new arm); the direct concrete `(= 3)` (deciding the producer-vs-consumer fork). **If no control can be constructed, the mechanism is a hypothesis and the attribution is provisional** — say so in those words, so the receiving skill probes rather than implements.
2. **The mechanism observed at the seam**, not inferred from the symptom — a trace, a carrier dump, a CLIF diff, a measured count. "The symptom is consistent with X" is not evidence for X; the seam's own state is.
3. **A falsifiability clause** — what observation would refute this attribution — and the receiving skill's **first act is to attempt that refutation**. Where this was written into a dispatch (the MS-P7 adjudication: *"/dev first confirms the fact chain is absent at the publication seam; present-and-correct → re-attribute"*) it worked and cost nothing; where it was omitted, a wave was spent implementing against a false premise. Non-refutation is evidence; a refuted premise re-attributes immediately rather than being patched around.

The economics are the argument: a control costs minutes at diagnosis time and saves a wave at fix time, and it is cheapest exactly when the mechanism is freshly in hand — the same moment as the instrumentation question below.

**An attribution that explains an application-scale signal is not closed until that signal is re-measured (binding, added S115).** A reduced repro flipping green is **necessary and not sufficient**. When a defect was attributed *because it accounts for* a measured aggregate — a leak count, a timing, an allocation rate — closing it requires re-running **that measurement**, with a control build and the same input, not merely watching the reduction turn green.

S115's exhibit is unambiguous. At S114 the exemplar's ~11,800-objects-per-solve residue was attributed to an ADT-wrapped supersede loop on the arithmetic "≈5,900 supersedes × 2 objects ≈ 11,800". The reduction was found, pinned, fixed, and verified exact at every N — and the application-scale number moved by **3 objects (0.025%)**. The arithmetic had been fitted to the total rather than measured against it, and the real mechanism (an unreleased wrapper box, ~10⁴ per solve) was a different seam entirely; a propagation-only ablation later showed it accounts for 99.6% of the residue. The fix was real, the pin was real, and the conclusion was false for a full sprint.

So an aggregate-derived attribution carries: the **measurement re-run at a control build and at HEAD with the same input** (methodology reproduced exactly — if the control does not reproduce the original number, the comparison is void and must be said so); the **residual stated as a number**, not as "improved"; and, where the residual is large, an **ablation** that bounds which part of the workload carries it. `/qa` treats a closed aggregate-attribution with no re-measurement as an open item, and any record asserting the aggregate resolved is corrected in place when the re-measurement lands. `/review` treats a mechanism claim with no control and no seam observation as an **Important** finding, and a *fix* built on one as a **Blocker** (it is an unguarded narrowing of the search space).

**Probe hygiene: the repo root is not a clean room (binding, added S115).** Agents probe constantly — build a two-line `.cl`, run it, read the output — and the obvious place to do that is the repo root, because module resolution is **cwd-relative** and a probe run elsewhere fails to find the prelude. That convenience is a trap: the repo root is also where the REPL writes its **session-persistence file** (`user.cl`, git-ignored) and its history, so a REPL probe there *mutates state the next probe inherits*. S115 exhibit: several agents accumulated definitions in the shared root `user.cl`; a later agent's plain `(deftype Point [:Int x :Int y])` then failed with "expected symbol", which looked exactly like a live defect and was session pollution. It cost a diagnosis and was caught only because the reviewer re-ran in a fresh directory.

The rule, and it is one line of setup: **a probe runs in a private directory with the library path supplied explicitly** — `cd <own scratch dir> && CRANELISP_LIB=<repo>/stdlib <repo>/target/debug/cranelisp --run probe.cl`. That is the same shape the standing 0604 repro recipe already uses, so it is a convention to follow rather than invent. Consequences worth stating because each was violated at least once this sprint:

- **Never write to the repo root** — not `user.cl`, not `.cranelisp_history`, not a stray `probe.cl`. Git-ignored is not the same as harmless; these files are *inputs*.
- **A dispatch names the agent's scratch directory**, and agents do not share one. `/sprint` supplies it in the prompt (the session scratchpad, per-wave subdirectory).
- **Do not copy the repo to get an isolated build.** One S115 review exhausted a 7.6 GB tmpfs doing this and lost its shell mid-verification. Source-touching work is serial anyway, so revert-in-place (Edit, or `git stash`+`pop`) is both available and cheaper.
- **Clean up, or say you did not.** A probe left behind is the next agent's confounder.

This is the environmental face of the control rule above: an attribution must exclude the *environment* as the mechanism, not only the wrong code path. The reviewer who re-ran in a fresh directory was doing exactly that, and the discipline here is what makes that step unnecessary in the common case.

**The instrumentation question (binding, added S115).** Every defect isolation — by `/dev`, `/review`, `/qa`, or a user-proxy — MUST answer, in its report: **"what standing instrument or assertion would have caught this at its seam, and does it exist now?"** The answer is one of: (a) *it exists and fired* — record which, it earned its cost; (b) *it exists but was blind* — say WHY (wrong predicate, wrong variant, shape-limited claim, compiled out in release); the instrument is defective and its correction rides the fix; (c) *none exists* — name the instrument that would have, and route it (register row → `/arch` `safety-invariants.md` §4; coverage row → `/qa`). "The test suite caught it" is not an answer — a test is an example, an instrument is a standing mechanism.

**An instrument is unverified until it is proven to detect (binding, added S115).** Every assertion, gate, fence, validator, lane, or oracle ships with a **capability test that plants the fault it claims to catch and observes it catching it**. Until that test exists, the instrument's green is not evidence of health — it is evidence of nothing, and it will be read as the former. The proof takes the shape the instrument takes: a *gate* proves itself by **failing on revert** (revert the corrected predicate, the guard goes RED — S115's 0604 gate); a *validator over a variant family* proves itself **per variant** (each arm RED-then-GREEN, with a false-fire fence — S115's R6); a *lane or diagnostic mode* proves itself against a **planted synthetic fault** (never a live defect — planting on a real bug means the fence dies with the fix, the S114/S115 `m3` lesson); a *conditional fence* proves itself in **every build configuration it ships in** (a `debug_assert` needs its release-mode behaviour pinned too — S115's 0751).

This generalises a rule the project already had and had scoped one level too narrowly: `tests/plan/memory-safety-coverage.md` §4.1 has long mandated a synthetic self-test *per diagnostic mode*, and those fences existed and passed. The **lane composed of those modes** carried no such fence — so its signal (`imbalance(ON) == imbalance(OFF)`, a differential over two configurations of one codepath) sat green through five real leaks in the shared path, where every cell compared `0 == 0`. The modes were proven; the composition was not. **A composed instrument needs its own capability proof — the proofs of its parts do not compose.**

**A provisional implementation scope carries a back-edge to the ruling that will settle it (binding, added S115).** The sibling of the rule below, on the implementation side. When a skill deliberately ships a *narrower* scope than the design asks for — pending a user ruling, an `/arch` call, or a design fork — it fences the narrowing with a test so that widening is a deliberate re-decision. That is good practice and this project does it well. The failure mode is what happens **after the ruling lands**: the ruling is scribed in `spec/`, the fence still passes because it pins the *provisional* scope, and nothing anywhere carries the obligation to widen the implementation.

S115's worked case: a user ruling widened a trait-method rule from a nullary corner to a general requirement; `/spec` scribed it; the implementation kept the narrow guard for a further four waves; and it surfaced only when a user-proxy probed it by hand in Phase 6a. `/sprint` had recorded the routing and never scheduled the wave — **routing is not scheduling.**

What makes this sharper than an ordinary missed task is the shape of the evidence. As `/dev` put it, the arity cell **existed, with deliberately inverted polarity** — the provisional fence — so it was green throughout the divergence and structurally could not fire. *A hole is visible to a matrix audit; an inverted fence reads as coverage.* A provisional fence that outlives its provisionality is a false coverage claim, and it is invisible precisely because someone was careful.

So, binding:

- **The fence names its trigger.** A test pinning a provisional scope states, in its own comment, the ruling or decision that will invalidate it and what the widened assertion becomes. `/dev` did this at W4 and it is why the widening was a five-line change — keep it.
- **A ruling is scheduled at the moment it is recorded, not routed.** `/sprint` writes the implementing wave into `SPRINT.md` when it writes the ruling into the notes; a ruling with no scheduled slot is an open item, not a settled one.
- **The close checklist asserts it**: every ruling recorded this sprint has either landed its implementation or carries an explicit, owned deferral. This is the FIXME-vs-§Delivered consistency check extended from FIXMEs to rulings, and it exists for the same reason.

**The same back-edge runs from the DESIGN DOC, not only from the ruling (extended S115, third instance).** A ruling is not the only thing an implementation can silently ship narrower than. S115 produced three instances of one shape — *an implementation shipped narrower than its own design of record, and nobody compared the two*:

- the occurrence rule: `design/typecheck/traits.md` §2 **already specified** the wide scope ("reject on the conjunction no-param-occurrence ∧ no-self-return"); the implementation shipped the nullary corner, holding the narrowing in a code comment. Detectable at the landing wave by reading the design beside the code.
- the S108 test split: designed in detail, with an explicit rejected-alternative box, and the rejected alternative is what shipped — discovered two sprints later by an audit.
- the generative harness v1: `tests/plan/memory-safety-coverage.md` §2.1 **already lists** `match` ctor-pattern and var-pattern binds as flow operators; v1 replaced the operator algebra with fixed per-type reader functions and lost them — so the harness generated the one `match` shape that works and no other, and was blind to the memory-corruption defect a user-proxy found by hand a day later.

None was a lapse of care — each shipped a defensible narrowing for a stated reason. The failure is that **the narrowing was recorded only on the implementation side**, where nothing compares it back. So: a change-set that knowingly implements less than its design says states the deviation **in the design doc** (a dated "as-built narrower than designed, because …, widens when …" line), not only in a code comment or a commit message; `/review`'s design-vs-code step treats an undeclared narrowing as a finding; and where the design doc is another skill's, the deviation rides a FIXME rather than a comment. The asymmetry to remember: a design doc is read when the next change is planned, and a code comment is read only by whoever is already in that file.

**A spec change clears its coverage annotations (binding, added S115 — user-directed).** The traceability band (`[Tested …]` / `[Tested+Neg …]` / `[S{M}]`) asserts that a named test validates the requirement *as written*. When the requirement changes, that assertion silently becomes a claim about prose that no longer exists — and nothing today notices, because the citation is still *live* (the named test still exists; only its subject moved). So:

1. **The skill that changes a normative statement clears that row's annotation** in the same edit. Clearing is an **invalidation, not a coverage judgment** — which is what keeps it inside the existing ownership rule: `/spec` (or `/repl` for `repl/spec.md`) may clear, because only the author of the change knows a requirement moved; **only `/qa` may restore**, because restoring is the judgment, and the band is `/qa`'s authority.
2. **Clearing makes the row report as uncovered.** The machinery for this already exists — `tests/plan/spec_coverage_reconcile.py` detects "true gaps: heading/MUST sections with NO covering test" and builds a test→spec index keyed by (spec-file, §anchor). What it cannot detect today is a requirement whose prose changed underneath a live citation. Clearing converts that invisible case into the visible one the linter already reports.
3. **`/testing` reconfirms via the backlinks.** Every test carries a `// spec:` anchor, so the covering set for a section is a query the index already answers. Walk it; for each covering test decide whether it still validates the *new* prose; add cells for what is now uncovered — including the negative direction, since a changed requirement usually changes what must NOT happen.
4. **`/qa` restores the band to green** once the covering set actually covers, and the row returns to `[Tested …]` / `[Tested+Neg …]`.
5. **Sprint-close gate**: no row may be cleared-and-unrestored at close without an explicit, recorded carry. An uncovered requirement is a legitimate thing to ship; an *unnoticed* one is not.

Why this is load-bearing rather than bookkeeping: S115 supplied the worked failure. A user ruling changed §7.1.1's occurrence rule from a nullary corner to a general requirement; the spec was scribed, the annotation stayed green, the covering test still existed and still passed — and **the implementation was never widened, which nobody noticed until a user-proxy probed it in Phase 6a**. Under this rule the ruling clears §7.1.1's band, the linter reports it uncovered, `/testing` walks the backlinks and finds the covering test exercises only the nullary cell, the added non-nullary cell goes RED, and the missing implementation surfaces **mechanically** in the same wave. The same mechanism catches the softer case `/repl` found the same day: a row annotated `[Tested …]` whose behaviour a probe contradicts.

**A defect found by an instrument asks three questions, not one (binding, added S115).** The instrumentation question above asks *what standing mechanism would have caught this at its seam*. When the finder **was** an instrument — a new lane, a fence, a golden diff, a harness — two further questions are owed, and they are the ones that change where effort goes next:

1. **The coverage question** — *which unit scenario and which integration axis were absent?* Name them concretely (the seam that had no test, the axis the matrix never crossed), and route each to its tier. An instrument finding a defect in code the suite already exercised means the suite was asking the wrong question there, which is a fact about our tests, not about the instrument.
2. **The risk question** — *why did risk analysis not rank this area as needing that coverage?* This is the one that compounds. If the answer is "it did, and the mitigation was an instrument that turned out to be blind", the risk model was right and the register's status was wrong (→ the detection-proof rule below). If the answer is "the area was never enumerated", the **risk model itself has a gap**, and a repeat means the model is mis-shaped, not under-applied.

The S115 evidence names one such mis-shape precisely, and it should be treated as a prior: **the risk register enumerates SURFACES — which mechanism might be wrong — but not VARIANT FAMILIES × REACHING CONTEXTS — which shapes reach that mechanism.** Three of this sprint's finds are that single gap (a stranding site enumerated for closure captures but not for the curried partial application that reaches it identically; a re-impl enumerated for explicitly-provided methods but not for the default-method source; an operation enumerated for bare trait heads but not qualified ones). The reaching-context axis was already in use elsewhere in the plan when each of these shipped — it was available and simply not applied to that surface. `/qa` owns closing this: a risk row names its variant family and its reaching contexts, or it is an incomplete row.

Consequences, binding on `/qa` and `/arch` respectively: a row in an instrumentation/coverage matrix may be marked **VERIFIED only when it cites its detection proof** — "the mechanism exists at file:line" and "a test exercises it" are both weaker claims and neither substitutes; and a register row's `asserted`/`gated`/`dynamic-lane` status likewise requires the proof, otherwise the honest status is *asserted-but-unproven* (the S115 R7 precedent, where the recorded status was `asserted` and the predicate was structurally blind).

The question is cheap at isolation time and expensive later: the defect's mechanism is freshly in hand, and that is the only moment the right instrument is obvious. Answers accumulate into the register (§4 rows) and `/qa`'s coverage process; a recurring (c) is an architectural finding, not a testing gap. Known answer-classes from the S115 harvest, offered as priors rather than a checklist: a balance/no-leak claim is **shape-limited until parameterized by the escape/reaching-context axis**; a gate is unverified until a **synthesized trigger fails on revert** (existence ≠ discrimination); a `debug_assert` fence must have its **release-mode fallback polarity explicitly chosen and pinned** (leak-safe vs UAF-safe), because that fallback IS the shipped behaviour; a validation census over a **variant family** must be compile-enforced (exhaustive match) rather than prose, or it will guard the safe variant and miss the dangerous one; a name-vs-carrier decision wants **derive-and-fence** (record the producer's verdict, assert the consumer agrees) rather than a second derivation; and a value produced at a **process/session boundary** has no owner unless one is named — process exit hides the leak that a session accumulates.

**Implementation-strategy unit scenarios (binding, added S101).** The fix-level rule above guards *repairs*; this rule guards *features*. An implementation strategy (a staging/commit split, a retention pool, a cache layer, a batch-derivation pass, a generation counter) creates a scenario space **the spec knows nothing about** — so spec-derived tests, `/qa`'s included, structurally cannot cover it; only the implementer knows it exists. When `/dev` implements, it MUST derive unit scenarios from the strategy explicitly, per seam touched — where **the seam unit is the submodule** (the crate's internal module composition: `compiler/apply`, `heap`, `cache/linker`), not the crate as a whole:

- **Complexity cases** — each algorithmic path and state transition the strategy introduces;
- **Edge cases** — the boundaries the strategy creates: empty/full/exhaustion, collisions, and **every cell of any implied matrix** (displacement shapes, instantiation shapes), not only the cell the design document names;
- **Negative cases** — what the strategy must NOT do: wrong item absent, stale entry never served, forbidden transition rejected.

Scenarios are **expressed through the crate facade** wherever the seam is facade-reachable (internal-invariant tests are permitted, but the facade is the default — the tier then survives refactors and reads as a contract), and unit tiers are **organized by submodule × scenario class**: each strategy-bearing submodule carries its own test module (`foo/tests.rs` or `#[cfg(test)] mod tests` sibling to `foo.rs`), so coverage is attributable and auditable **per submodule** — `/qa` checks the matrix mechanically instead of reverse-engineering intent. A **monolithic crate-root `tests.rs`** is the named anti-pattern: it makes submodule-level coverage unattributable (S101 exhibit: backend's flat 5.9k-line `tests.rs` over 32.5k LOC of well-composed submodules — nobody can see which submodules are thin). The bounded contexts (crates) are settled; this rule governs composition and accounting *inside* them. `/review` verifies that new or changed seams carry all three classes; a strategy-bearing seam with only happy-path pins is an Important finding. (S101 evidence: 0479 — displacement matrix, only the design-named cell was pinned, review caught the complementary cell as a live UAF; 0483/0488 — instantiation matrix, single cells pinned, SIGBUS one step out; D1/D2 — regeneration/adoption strategies with zero unit scenarios.)

**Phase 6a — User-facing assessment.** User-proxy skills assess what was *actually* delivered (not what was scoped) and plan the user-facing work outside-in from spec + scope. Gaps file as FIXMEs to next sprint.

**Each user-proxy owns a standing QUALITY, not a regression surface (binding, added S115 — user-directed).** "Does it still compile / still run / still match the transcript" is the *floor* of a 6a pass, not its content. Every proxy owns a question that is never finished and is re-asked every sprint against the whole artifact, not just against the delta:

- **`/examples`** — *is this a comprehensive learning sequence, and the best way to learn the full language and its nuances by reading code?* That means coverage of the language (what is unteachable from the sequence today?), **order** (does each example earn its place and build on what precedes it?), **nuance** (does it teach the boundaries, traps and negative space, or only the happy path?), and the quality of the code *as reading material* — an example is prose that happens to compile.
- **`/docs`** — is this the best way to understand the language by reading prose?
- **`/repl`** — is every interaction self-documenting and genuinely useful (the §Design Principles bar), not merely non-erroring?
- **`/stdlib`** — is this a library a user would choose to use, and does it read as one design?
- **`/port`** — is the exemplar something a competent developer would admire, and does it still exercise the language the way a real project would?

`/sprint` writes the standing quality into the dispatch, not just the sprint's delta; a brief that lists only "verify X still works" has mis-scoped the phase. The tell that this went wrong in S115: `/examples` was briefed on exit codes and ruling-impact and *nonetheless* reported, on its own initiative, that **trait default methods are taught by no example at all** — while the spec's own worked example for defaults is the very `Ord` trait that example teaches. The skill knew its remit better than the brief did, and a narrower skill would have returned a green table and nothing else.

**Phase 6b — User-facing action.** Execute the 6a plan against what shipped. Demos test reachability of the spec'd capability through user surfaces.

**Phase 7 — Close.** `/sprint` authors outcome, archives `SPRINT.md`, updates ROADMAP. **User approves close explicitly** — `/sprint` does not close unilaterally. Checkpoint on adequacy of arch's architectural principles. **Close checklist asserts FIXME-vs-§Delivered consistency (added S115)**: every FIXME the Outcome records as resolved has its file deleted (or its table row updated), and no surviving FIXME file or close-table row contradicts a §Delivered line. (S110 counterexample: the close table carried 0590 "open" beside a §Delivered line recording its convergence — the seed of the S113/S114 zombie chain.)

### 2.3 FIXME flow within a sprint

- Filed at any time as files in `design/arch/fixmes/NNNN-name.md` (see §3.3).
- **Wave gate**: before `/sprint` advances to the next wave, scans for `target: /skill-in-wave` and `status: open`. Outstanding FIXMEs targeting a wave's skill block advancement.
- **Phase 6 → next sprint**: gap FIXMEs flow forward to the next sprint as scope input. Phase 6 does not reopen Phase 5.

### 2.4 Deferral principles

1. **Defects discovered in Phase 5 are addressed in Phase 5** — fix, defer with explicit rationale, or close Phase 5 short. Conscious and recorded. Phase 6 does not retroactively reopen.
2. **Speculative refactoring deferred; emergent refactoring mandatory in-sprint.** When the current work has made cleanup cheap (third duplicate, file over budget, `mirror` comment), extract in-sprint.
3. **Interim architecture avoided, not deferred** — if a feature would require throwaway infrastructure a later increment replaces, don't build it.

**2× escalation.** Items deferred once may be deferred again with rationale. Items deferred twice ship in the current sprint or require explicit user sign-off for a third deferral. Applies to FIXMEs, ignored tests, and `/review` findings.

### 2.5 Mid-sprint adjustment

If `/sprint` is invoked mid-sprint: report status; recommend continue / re-scope / close. Scope changes require user sign-off. `/sprint` never closes unilaterally.

### 2.6 Rolling whole-context audit

One bounded context is audited per sprint, in rotation (normative cycle:
`sprints/artefacts.md` §I.7/§II.1; role: `.claude/commands/audit.md`). The
`SPRINT.md` template carries a standing `Audit: {context}` field filled at
Phase 4 — the structural cue. The dispatch runs read-only in the Phase 6/7
window; the assessment lands in `audits/{context}-sNNN.md` with
recommendations (evidence, cost class, proposed owner). **Next sprint's
Phase 1 disposes each recommendation with the user**: accepted → `/sprint`
files the FIXME targeting the proposed owner; declined → recorded in the
assessment with rationale. `/audit` never files FIXMEs for its own
recommendations and never blocks the current sprint. At Phase 7, `/sprint`
checks the audit's calibration: recommendations that consistently die at
acceptance are a finding about `/audit`. Out-of-rotation pulls: escalation
trigger 6 (`artefacts.md` §II.4).

---

## 3. Artifacts and memory

### 3.1 Where things live

| Artifact | Path | Owner | Purpose |
|---|---|---|---|
| Language spec | `spec/` | `/spec` | What the language does |
| Architecture rules and principles | `design/arch/` | `/arch` | Cross-crate decisions, principles, Decisions log |
| Cross-crate types and traits | `crates/cranelisp-types/` | `/arch` | Single home for types and traits crossing crate boundaries |
| Per-crate design | `design/{crate}/{crate}.md` (+ subordinates) | `/design` | What the crate should be — direction, intent, codified design decisions |
| Code conventions per directory | `CLAUDE.md` per directory | Directory-owning skill | How the code is — data structures, invariants, conventions |
| Test plan + coverage process | `tests/plan/` (`PLAN.md` normative) | `/qa` | Spec → tests bridge; risk register; coverage verdicts |
| E2e tests | `tests/` (sources, fixtures, helpers) | `/testing` | Normative spec-conformance evidence, authored to `/qa`'s plan; repro tests carry `// defect:` tags |
| Whole-context audit assessments | `audits/{context}-sNNN.md` | `/audit` | Accumulated-state assessments + recommendations (§2.6) |
| Artefact structure & model allocation | `sprints/artefacts.md` | `/sprint` | Allocation table, escalation protocol, shim contract, audit cycle |
| Unit tests | `crates/{crate}/src/.../mod.rs` (`#[cfg(test)]`) | `/dev` | Per-crate invariants, written alongside implementation |
| Methodology | `sprints/METHOD.md` (this) | `/sprint` | How we deliver |
| Skill workflows | `.claude/commands/{skill}.md` | Skill owner | How an agent in that role works |
| Roadmap | `sprints/ROADMAP.md` | `/sprint` | Sprint-by-sprint progress |
| Current sprint plan | `sprints/SPRINT.md` | `/sprint` | Active sprint scope, waves, outcome |
| Sprint archive | `sprints/archive/sprint-{id}.md` | `/sprint` | Completed sprint records |
| FIXMEs | `design/arch/fixmes/NNNN-name.md` | Filing skill until resolved | Cross-skill change requests |

### 3.2 Reading order

For a new session on this project:

1. Root `CLAUDE.md` — project overview + pointers
2. The skill definition for the current role (`.claude/commands/{skill}.md`)
3. `sprints/SPRINT.md` for current work
4. `sprints/METHOD.md` (this) for the delivery method
5. `design/arch/` and `design/{crate}/` for current design context
6. Per-directory `CLAUDE.md` when entering a directory
7. `design/arch/fixmes/` for open requests targeting the current skill

### 3.3 FIXME file protocol

FIXMEs are files in `design/arch/fixmes/`, not inline comments. One file per issue. Avoids file-ownership ambiguity and multi-skill edit conflicts.

**Naming**: `design/arch/fixmes/NNNN-short-name.md`. NNNN is unique sequential. Filing skill scans for `max + 1`. `/sprint` resolves rare collisions at wave gate.

**Format**: frontmatter + body.

```markdown
---
number: 0042
target: /design
filed_by: /dev
filed_at: 2026-04-24
sprint_filed: 62
refers_to: crates/cranelisp-typecheck/src/checker.rs
status: open  # open | deferred
---

# Short description

## Issue
…

## Proposed resolution
…
```

**Lifecycle**:

1. Filing skill creates the file, commits.
2. Owning skill (`target`) sees the file at next wave gate or sprint Phase 1 scan.
3. Owning skill resolves — incorporates the change into its owned files — then **deletes** the FIXME file with a commit message naming what was resolved. Git history is the audit trail.
4. If deferred, owning skill sets `status: deferred` and adds rationale + target sprint; the file remains.

**Only the owning skill deletes.** `/sprint` orchestrates and gates on FIXMEs but does not delete them. Filing is the one exception to file ownership — any skill may file a FIXME targeting any other skill. (Narrow exception, S115: `/sprint` may delete a FIXME as a Phase-1 audit-disposal action when an `/audit` assessment has verified it resolved against source and the user has approved the disposal — the audit evidence + approval record substitute for the owning skill's resolution.)

**Verify-against-source first (binding, added S115).** Any disposition of a FIXME — resolve, defer, re-target, carry into scope, or a scheduling decision built on it — verifies the FIXME's central claim against its `refers_to` source as its **first act**, and the disposition note records what was opened. A record asserting something about source that a single file-open would refute must not propagate. (S114 exhibit: zombie 0590 — resolved S110, falsely re-dispositioned S113 with "convergence has not happened", then consumed /sprint scheduling, /arch sequencing, /design deferral prose, a /testing probe, and an S115 scope slot across a five-agent chain in which nobody opened the `refers_to` file.)

### 3.4 Skill handoff

Every skill plan ends with a **Next skills** section recommending invocation order, consulting `SPRINT.md` for the active sprint or `sprints/ROADMAP.md` otherwise.

### 3.5 Memory and signals

`memory/` holds point-in-time observations and user feedback. Non-normative — METHOD.md is the normative source for delivery method; skill definitions are normative for skill workflows; design docs are normative for crate direction. Memories are signals that may inform the next sprint or the next iteration of a skill definition, but they do not override the canonical sources.

When a memory's content becomes durable, it migrates into the appropriate canonical doc (METHOD, skill def, design doc, or `CLAUDE.md`) and the memory file is retired.

---

## Cross-references

- Architectural rules and principles — `design/arch/`
- Per-crate design intent — `design/{crate}/{crate}.md`
- Skill workflow detail — `.claude/commands/{skill}.md`
- Active sprint — `sprints/SPRINT.md`
- Open FIXMEs — `design/arch/fixmes/`
- Predecessor (consolidated current state, retained for reference) — `sprints/METHOD_OLD.md`
- Working draft with deeper prose, migration plan, and worked rationale — `sprints/METHOD_PROPOSED.md`
