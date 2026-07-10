# Sprint 106: FIXME Burn-Down — REPL/agent usability, aging-item drain, perf-track consolidation

**Status**: COMPLETE

**Goal**: Drain the FIXME backlog to near-empty — fix the fresh REPL/agent usability batch and the aging actionable carries, consolidate the suspended performance/parallel arc into an owned design backlog, and defer only what has a genuine unmet trigger.

## Scope

S106 is a **FIXME burn-down**. At Phase 1 there are 34 open/deferred FIXMEs. This sprint dispositions **every one**:

- **Fix in-sprint** — the fresh usability batch (0538–0551) plus the aging actionable carries (0050, 0365, 0416, 0463, 0496, 0498, 0499, 0544).
- **Consolidate** — the performance/parallel-analysis arc (11 items) migrates into a new `/arch`-owned `design/arch/backlog/performance.md`; the FIXME files are then deleted by their owning skills. This removes them from every future Phase-1 and wave-gate scan while preserving each item's pinned analysis + provenance as pre-assembled scope input for when the perf track is re-entered.
- **Defer (explicit, with rationale)** — **0052** (`/learn` subsystem) only: a whole REPL learning subsystem (watch mechanism, trigger evaluation, progress tracking) with no current pull. Deferred until the `/learn` capability is scheduled. Escalation count: this is its first hard deferral in the new-model tracking (originally filed S64, pre-S63 protocol).

### Explicitly out of scope

- **Perf/parallel re-entry** — consolidating the perf arc into the backlog doc is *not* re-entering it. No perf implementation or design-argument resolution happens in S106; the arc stays closed per the S105 accept-done sign-off.
- **Per-submodule test-file reorg** — the S101 coverage-audit split (flat crate-root `tests.rs` → per-submodule siblings) is **complete**: backend's 5,861-line flat file is split into 14 siblings; frontend/typecheck/intrinsics/types are fully per-submodule; FIXMEs 0495/0500/0501/0502 resolved and deleted. The residual crate-root `tests.rs` in `cranelisp-platform` (marshaling boundary — audit-blessed as one-concern) and `cranelisp-primitives` (665 lines) are left by intent. Confirmed done at S106 Phase 1; not re-opened.

## FIXME debt

Every open FIXME with its S106 disposition. Reference by number; content lives in `design/arch/fixmes/NNNN-*.md`.

### Workstream A — Backing-file & session fidelity

| FIXME | Owner | Disposition | Note |
|---|---|---|---|
| 0548 | /qa | fix | CONFIRMED — failed import persisted to backing file (root cause pinned) |
| 0549 | /arch | fix | non-defining `__expr` forms persisted; user ruled wrong (save.rs pinned) |
| 0550 | /repl | fix | `--link` output name collides with CWD dir (lifecycle.rs pinned) |
| 0551 | /qa | fix | CONFIRMED — `read-line` leaves stdin `O_NONBLOCK`, REPL exits (fully diagnosed). **/arch seam ruling delivered (Phase 2 §coherence):** fix at BOTH seams — (A) platform poll leaf restores fd-0 flags; (B) host stops treating `WouldBlock` as EOF. (C) split-brain buffer = pinned residual, no redesign. Co-lands with 0544 (same read loop). |
| 0538 | /dev (src/) | fix | save.rs §5–7 source-first regen (sibling of A) |

### Workstream B — Symbol-enumeration display

| FIXME | Owner | Disposition | Note |
|---|---|---|---|
| 0546 | /qa | fix | CONFIRMED — `/imports` prelude group bypasses shared layout (pinned) |
| 0545 | /repl | fix | reconcile §3.3 L3 letter-group packing (spec example inconsistency) |
| 0542 | /qa | fix | CONFIRMED — bare trait lookup omits `; defn:`/`; impl:` sections |

### Workstream C — `/search` discovery

| FIXME | Owner | Disposition | Note |
|---|---|---|---|
| 0540 | /repl | fix | `/search` matches docstrings (new axis + ranking) |
| 0543 | /repl | fix | `/search` drops exact in-scope match; add exact-above-partial ranking |

### Workstream D — agent/CLI surface

| FIXME | Owner | Disposition | Note |
|---|---|---|---|
| 0539 | /repl | fix | `--agent`/`--yes` error on non-agent build (user ruling) |
| 0541 | /qa | fix | CONFIRMED — multi-tool-call turn panics binary (provider.rs pinned) |

### Workstream E — Line editor (dependency gated on /arch)

| FIXME | Owner | Disposition | Note |
|---|---|---|---|
| 0544 | /repl | fix | up-arrow history + inline editing; **/arch rules on rustyline/reedline dep in Phase 2** |

### Workstream F — Docs

| FIXME | Owner | Disposition | Note |
|---|---|---|---|
| 0547 | /docs | fix | platform-consumption discoverability (not a defect; docs-only) |

### Workstream G — Aging test-hygiene

| FIXME | Owner | Disposition | Note |
|---|---|---|---|
| 0496 | /dev (src/) | fix | unit-tier drain — largely done per its S103 update; verify + close residual |
| 0498 | /dev (types) | fix | marshal byte-sync drift-guard test + zero-test module cover |
| 0499 | /qa | fix → **close** | e2e-lane refactor: 5/7 lanes already built (S102). Land **L-S1** (session-history preamble grid) — the one bounded remaining lane; **retire L-M1** (reference×referent×instantiation matrix) to WS-J, as its growth is driven by the parked backend `fn_as_value` seam. Both conditions met → delete 0499 at S106 close. |

### Workstream H — Language / spec features → **VERIFY-AND-CLOSE (already shipped S91)**

Phase-3 `/spec` finding: **both items were fully resolved at S91** (commit `9ba2ca91`) — spec + impl + passing tests all in the tree. The FIXME files are stale (never deleted). WS-H is therefore verify-and-close, NOT new implementation; the "gated on /spec" dependency is void. User ratified the two open semantics (2026-07-09): single arithmetic `shr`; shift-count mod-64.

| FIXME | Owner | Disposition | Note |
|---|---|---|---|
| 0365 | /spec | **verify-and-close** | `Type.member` accessors shipped S91 (`spec/05-definitions.md §5.2.6`, `spec/08-modules.md §8.5.2`; `tests/spec_field_accessor.rs`). `/spec` confirms green + deletes the stale FIXME. |
| 0416 | /arch (deletes file), /spec (semantics) | **verify-and-close** | bitwise primitives shipped S91 (`spec/appendix-a-builtins.md §A.3`; `crates/cranelisp-primitives/src/operator.rs`; `crates/cranelisp-backend/src/primitives_inline.rs`; `tests/spec_appendix_a_bitwise.rs` 9 GREEN). User ratified single arithmetic `shr` + mod-64 shift count. `/arch` deletes the stale FIXME (targets /arch). One additive `/spec` line recorded the no-logical-shift decision. |

### Workstream I — Learning-sequence + display protocol (start efforts)

| FIXME | Owner | Disposition | Note |
|---|---|---|---|
| 0050 | /arch, /int, /stdlib (+/backend) | fix (**design-only**) | /arch ruling: S106 covers **mechanism design only** — §1.5 List/Seq MUST-promotion deferred to the follow-on that lands the printer (promoting first = Principle-8 violation). Design MUST **extend the existing `DisplayDescriptor`** infra, not greenfield. Widest-surface item; design-first, parallel, time-boxed, non-blocking — may spill to "design started". |
| 0463 | /examples | fix (start) | poll-shape network/platform leaf example (needs example infra — S99) |

### Workstream J — Perf-track consolidation → `design/arch/backlog/performance.md`

`/arch` authors the backlog doc capturing each item's pinned analysis + provenance; owning skills then delete their FIXME files.

| FIXME | Owner | Disposition |
|---|---|---|
| 0506 | /design (backend) | consolidate |
| 0507 | /design (src/) | consolidate |
| 0510 | /design (backend) | consolidate |
| 0521 | /arch | consolidate |
| 0526 | /arch | consolidate |
| 0528 | /design | consolidate |
| 0534 | /design | consolidate |
| 0535 | /design | consolidate |
| 0536 | /design | consolidate |
| 0408 | /port | consolidate (Sudoku perf carry) |
| 0466 | /design | consolidate (GOT slot-hole reclamation) |
| 0499 / L-M1 | /qa | consolidate (matrix growth driven by the parked backend `fn_as_value` seam; recorded here so it re-enters when the perf track does) |

### Deferred

| FIXME | Owner | Disposition | Rationale |
|---|---|---|---|
| 0052 | /repl, /qa | defer | `/learn` subsystem — no current pull; revisit when scheduled |

## Architecture review (Phase 2)

**Overall verdict: APPROVE-WITH-REVISIONS.** The scope is technically coherent, correctly
debt-first, and carries no interim-architecture risk in the fix batch. Five revisions/rulings
below are load-bearing for Phase 4; two coherence corrections (0551 seam ruling, 0416
terminology) adjust owner/routing. **No item in scope requires a new `cranelisp-types` interface
type** — see §"Cross-crate interface impact". Waves must respect the dependency notes at the end.

### 1. Line-editor dependency (0544) — APPROVE `rustyline`, default-build

- **Crate: `rustyline`** (not reedline). Grounds: (a) markedly lighter dep tree than reedline's
  crossterm/nu stack — acceptable as a *default-build* dep for a REPL binary, and far smaller
  than the agent-feature HTTP/async tree; (b) battle-tested, MIT; (c) `repl/spec.md` §1698
  already names rustyline's `ExternalPrinter` as the home for the notification/partial-input
  reinstatement behaviour, so this choice keeps that aspirational note coherent rather than
  re-homing it. reedline's extra surface (menus, multiline widgets) is not pulled by anything in
  scope; rejected on weight.
- **Hard constraint — non-TTY path stays byte-identical (BLOCKING on the impl).** The editor is
  constructed and used **only** on the interactive-TTY branch, gated on `std::io::IsTerminal`
  for stdin. When stdin is not a terminal (piped/redirected — how the e2e harness and scripted
  input drive the REPL) the read path MUST remain the *exact* current `stdin.lock().lines()`
  code. rustyline is never instantiated on that branch. This is a `/dev` implementation
  obligation and a `/qa` guard (assert non-TTY output byte-identical pre/post).
- **Consent-line reader seam (§15.2 write gate) — one input source, no split-brain.** On the TTY
  branch, the agent consent-line read (`main.rs` pulls the next stdin line) MUST go through the
  **same `rustyline::Editor` instance** (a `readline` call), NOT a parallel `BufReader`. rustyline
  owns the terminal (raw mode during `readline`, cooked between); a raw read alongside it would
  desync the line discipline and race the buffer. On the non-TTY branch the consent read stays
  the plain line read from the same single reader. `/dev` must thread one input abstraction that
  has a TTY impl (editor-backed) and a non-TTY impl (plain lines); the consent seam calls it, not
  a second reader.
- **Not /arch's to decide (route to /repl → user):** whether history persists across sessions to
  a file (`~/.cranelisp_history`) or is session-only, and the bounded history length. Normative
  REPL-experience choices — `/repl` specs them in `repl/spec.md`; not a cross-crate/API question.
- **Public-API impact:** none. Binary-crate dependency only; no crate-boundary surface, no
  `public-api.txt` change, no facade change. `src/main.rs` interior + `Cargo.toml` dep line.

### 2. Perf-track consolidation (WS-J → `design/arch/backlog/performance.md`) — CONFIRMED

- **Mechanism confirmed.** Migrating the 11 items + the /qa L-M1 note into one `/arch`-owned
  backlog doc, then filing-skill-deletes each FIXME, is the correct resolution. It removes them
  from Phase-1 / wave-gate scans while preserving pinned analysis + provenance — and it is NOT
  re-entry (no perf design/impl is unblocked by the move; the S105 accept-done close stands).
- **Ownership:** `/arch` owns the resulting doc. It is a **backlog** doc, not a canonical-set
  member (it describes parked work, like `fixmes/`), so it does not join the mutually-consistent
  canonical set — no overview/BC/principle audit obligation beyond existing at its home.
- **Structure + provenance contract:** stubbed now at `design/arch/backlog/performance.md`
  (Phase-2 shape approved). Each entry MUST carry: (1) origin line (FIXME № · filed_by · target ·
  sprint), (2) `refers_to` anchors, (3) pinned analysis/measurement, (4) measured re-entry
  trigger, (5) reversibility note. Grouped by coupling into §1 ownership-lattice residuals
  (0521/0528/0510/0526), §2 create-gate/contention+density (0534/0535/0536/0408), §3 regen/capture
  spec holes (0506/0507), §4 GOT slot reclamation (0466), §5 /qa matrix note (0499/L-M1). Full
  per-item fill is **Phase 5**, done before each file is deleted.
- **Deletion ownership (filing-skill-deletes):** `/arch` deletes **0521, 0526** (its own).
  `/design` (narrow per crate) deletes **0506, 0507, 0510, 0528, 0534, 0535, 0536, 0466**.
  `/port` deletes **0408**. The **0499/L-M1** note migrates into §5 by `/arch`; the 0499 *file*
  closes under WS-G (`/qa`) once L-S1 lands. Each owning skill deletes only after confirming its
  substance is captured in the backlog doc — do NOT delete before Phase 5 fill.

### 3. `__expr` persistence (0549) — RULE: filter `__expr`-kind entries from regen. APPROVED.

- **Mechanism ruling:** `save.rs::generate_fns_and_macros` MUST exclude the synthetic
  `__expr*`-named `UserFn` entries from backing-file regeneration, symmetric with the existing
  `$`-mangled-name filter (~:732). This is a `src/save.rs` interior change; `/dev (src/)`.
- **Cross-crate / reload reconciliation (the reason it was filed to /arch): CLEAR.** Nothing in
  the T1-reload / monomorphisation / cache-restore paths *requires* `__expr` to be in the
  **backing `.cl` file**. The 0532/0537 "persisted `__expr`" the reload machinery reasons about
  is an in-session symbol-table artifact; excluding it from the *regenerated source text* does not
  remove the in-session entry. The backing file is source-regeneration output, not the reload
  substrate. So the filter is sound against the standing design. `/dev` must confirm in the
  change-set that the `__expr` entry still exists in the live symbol table for the session
  (only its *source emission* is suppressed) — that is the one thing the reload path could read.
- **Load-time-evaluation semantics — SETTLED by existing spec, low-risk; confirm-only to /spec.**
  The FIXME flagged "does module load evaluate top-level non-defining expressions?" as possibly
  the user's to arbitrate. Existing spec already answers it: top-level expressions are a
  **REPL-interactive-only** construct (`spec/02-grammar.md` §34: "In interactive mode (REPL),
  top-level expressions are permitted in addition to definitions"), and `spec/08-modules.md`
  §1245 treats a top-level expression in module-body position as "ambiguous and fragile." There
  is no module-init-evaluates-top-level-expressions semantics to preserve; batch mode runs
  `main`. Excluding `__expr` from the backing file is therefore semantically clean, not a loss of
  behaviour. **Action for /sprint:** this is a *scribe*, not an open normative gate — `/repl`
  records in `repl/spec.md` §18 that backing files contain definitions + structural forms only;
  if any doubt remains, `/spec` confirms the one sentence, but I judge it settled.
- **Set-coherence (WS-A 0548/0549/0550/0551/0538):** coherent as a backing-file-authorship-
  fidelity set. 0548 (failed structural forms leak — record-before-resolve ordering) and 0549
  (non-defining expr leak) are the two "regenerated file must reflect only real module content"
  halves; 0538 extends the source-first regen discipline to save.rs §5–7; 0550 is the `--link`
  output-name/location contract; 0551 is the stdin-ownership seam (see §coherence below). No
  conflict — 0548 and 0549 touch adjacent but distinct filters in the same file; `/dev (src/)`
  may co-schedule but they are separately testable. **Sequencing note:** 0538, 0548, 0549 all
  edit `save.rs`/the Pass-0 peel — land them in **one `/dev (src/)` serial slot** (shared-tree
  edit contention; CLAUDE.md single-agent rule) with each guarded by its own `/qa` repro.

### 4. Display-protocol mechanism (0050) — SCOPE TO DESIGN-ONLY. Do NOT promote §1.5 in S106.

- **Ruling:** S106 covers the **mechanism design only**. The §1.5 List/Seq MUST-promotion is
  explicitly deferred to the follow-on sprint that lands the mechanism + stdlib opt-in. Promoting
  the spec forms before the printer exists would be an interim-architecture violation (Principle
  8) — a normative MUST with no mechanism behind it.
- **Ballooning is a real risk; contain it by REUSE, not greenfield.** A type-directed
  pretty-printer naively touches typecheck (type→printer dispatch), backend (baking display
  data), int (REPL render), stdlib (opt-in impls) — too wide to *build* in a burn-down sprint.
  Containment: the design MUST be framed as an **extension of the existing `DisplayDescriptor`
  infrastructure** (`design/arch/tracing.md` §299+ — already a recursive, self-contained,
  codegen-baked, `.o`-cache-surviving descriptor with a JIT-leak path), NOT a parallel protocol.
  The trace feature already solved "how does compiled code carry a self-describing render
  descriptor across caching." The display protocol is the same problem one consumer over. A
  greenfield printer that ignores `DisplayDescriptor` would be a Principle-7 duplication defect.
- **Deliverable:** a `/arch` design section/subsystem doc answering (a) dispatch model (nominal
  type → printer selection), (b) where the custom printer lives (stdlib opt-in vs REPL-side
  type-recognition table), (c) explicit relationship to `DisplayDescriptor` (extend vs wrap),
  (d) the exit gate for the promotion follow-on. **Design-first, parallel to the fix waves**
  (WS-I). If it does not converge inside S106's design phase it degrades gracefully to
  "mechanism design started, promotion carried" — it does NOT block any fix wave.
- **Cross-skill surface:** `/arch` (mechanism + cross-crate shape) + `/int` (REPL render layer,
  the §1.5 consumer) + `/stdlib` (List/Seq opt-in) + **`/backend`** if dispatch bakes a
  descriptor (it should, via `DisplayDescriptor`) + `/typecheck` **only if** dispatch is
  resolved at compile time. Flag to /sprint: this is the widest-surface item in the sprint;
  keep it design-only and time-boxed.

### 5. Bitwise intrinsics ABI (0416) — CONFIRMED, no cross-crate interface change

- **ABI surface confirmed.** These are **inline-lowered primitives**, not extern/C-ABI
  intrinsics — same mechanism as arithmetic `+ - * /`: `DefKind::Primitive` entries seeded in the
  `cranelisp-primitives` static `SymbolTable`, dispatched and **inline-lowered by the backend** to
  their 1:1 CLIF ops (`band`/`bor`/`bxor`/`bnot`/`ishl`/`ushr`|`sshr`/`popcnt`). No new C-ABI
  extern symbol, no `intrinsics_table()` entry, no heap marshalling. (Terminology note: the FIXME
  title says "intrinsics"; the resolution body is correct — these are Ring-0 *primitives*. `/spec`
  should file them under appendix-a primitives, not the intrinsic-extern surface. Flag for
  /sprint so the workstream-H owners use the right seam.)
- **No `cranelisp-types` change, no new interface type.** `DefKind::Primitive` + the existing
  scheme/type-signature machinery already carry everything. The only "registry" touched is the
  primitives crate's seeded symbol list (crate-interior) + the backend's primitive-lowering match
  arm (crate-interior).
- **Public-API impact:** none at the Rust crate boundary — no `public-api.txt` line moves (the
  new names are *language* primitives, not Rust `pub` items). `/dev (primitives)` adds the seeds;
  `/dev (backend)` adds the lowering arms; both crate-interior.
- **Blocking upstream: `/spec` semantics.** Int width, `bit-not` two's-complement width, and
  **signed-vs-logical shift** (`shr` → `sshr` or `ushr`) are normative `/spec` decisions
  (`spec/appendix-a-builtins.md` §A.3). Backend lowering is gated on that ruling — sequence /spec
  before /backend in the wave plan (see dependency notes).

### Cross-crate interface impact — NONE

None of items 1–5 requires a new or changed `cranelisp-types` type/trait for S106. Verified item
by item: 0544 = binary dep + `src/` interior; WS-J = doc only; 0549 = `src/save.rs` interior
(the `__expr` entry is an existing in-session symbol-table artifact, not a boundary type); 0050 =
design-only, and its eventual mechanism should extend the existing `DisplayDescriptor` (already in
`cranelisp-types`/tracing infra) rather than add a new boundary type — any carrier lands with the
*implementation* sprint, not S106; 0416 = existing `DefKind::Primitive`, no carrier. **No
`crates/cranelisp-types/` edit made or owed this sprint.**

### Coherence pass — corrections & dependency notes

**Owner/routing corrections:**

- **0551 (read-line leaks non-blocking stdin) needs an /arch seam ruling the WS-A row omits.**
  The sprint lists 0551 owner `/qa` (fix), but the FIXME body step 2 explicitly requests an
  `/arch` ruling on the stdin-ownership seam (platform restore-flags vs host save/restore vs
  host-owned stdin) before `/dev` implements. **My ruling:** the fix belongs at **BOTH** localized
  seams, with the ownership boundary pinned as follows — (A) the **platform poll leaf**
  (`platforms/stdio/src/lib.rs::set_stdin_nonblocking`) MUST restore fd-0 flags on its terminal
  (Ready/EOF) — a poll leaf that mutates a **process-global** shared fd and leaves it altered is
  the primary defect (Principle: a borrowed shared resource is returned as found); (B) the **REPL
  host** (`src/main.rs`) MUST stop treating `WouldBlock`/`EINTR` as EOF (`Err(_) => break` is
  non-defensive) — distinguish genuine EOF from a retryable error. (A) is necessary; (B) is
  defense-in-depth and independently correct. The **(C) split-brain buffering** (`STDIN_BUF` in
  the platform leaf invisible to the REPL BufReader) is a latent seam issue — **do not attempt a
  buffer-unification redesign in S106**; note it as a pinned residual (a future stdin-ownership
  consolidation) and let (A)+(B) close the proximate exit bug. This ruling stands whether the row
  says `/qa` or not; `/sprint`: record the /arch seam ruling is delivered here, so 0551 is
  unblocked for `/qa` repro + `/dev` fix without a separate /arch consult.
  - **Interaction with 0544 (line editor):** the 0544 rework replaces the `stdin.lock().lines()`
    reader whose `Err(_) => break` is 0551's proximate cause (B). These two **touch the same
    `src/main.rs` read loop** — they MUST land in the **same `/dev (src/)` serial slot** (or 0551-B
    folds into the 0544 input-abstraction). Sequence 0551 and 0544 together; do not parallelise
    them across agents (shared-tree edit contention on the REPL read loop).

**Interim-architecture risk:** none in the fix batch — every fix is a localized seam correction
with a pinned root cause. The only design-shaped items (0050 mechanism, 0416 semantics) are
correctly staged design-first and gated (0050 = extend-not-greenfield; 0416 = /spec-first).
Principle 8 is honoured: no half-built printer promoted, no perf machinery pulled forward.

**Workstream groupings — sound, with these dependency constraints for Phase 4:**

1. **Shared-file serialization (BLOCKING on wave plan):** `save.rs` / Pass-0-peel edits
   (**0538, 0548, 0549**) and the `src/main.rs` read-loop edits (**0544, 0551**) each form a
   serial cluster — one `/dev (src/)` agent per cluster, not parallel (broken worktree isolation;
   CLAUDE.md single-agent-for-source rule). The two clusters (`save.rs` vs `main.rs`) touch
   different files and MAY run in different waves, but neither internally parallelises.
2. **WS-C (/search 0540, 0543)** depends on the /search index seam — confirmed; keep the two
   /search items in one owner's hands (both `/repl`) so the docstring-axis + ranking land coherently.
3. **WS-E (0544)** gated on this §1 dep ruling — now unblocked (rustyline approved). Sequence
   after/with 0551 per the shared-read-loop note.
4. **WS-H 0416** gated on `/spec` semantics (Int width / shift signedness) BEFORE `/backend`
   lowering — order /spec → /dev(primitives seeds) → /dev(backend lowering) within the wave.
5. **WS-I 0050** design-first, parallel to all fix waves, non-blocking, time-boxed; may spill to
   "design started" without blocking close.
6. **WS-J** is a Wave-1 `/arch` deliverable (doc authoring) + per-skill deletions; the deletions
   are gated on the Phase-5 doc fill — do not delete FIXME files before their substance is in the
   backlog doc.

**Route-to-user items (normative, not /arch's to decide):** 0544 history-persistence policy
(→ /repl spec); 0550 `--link` output name/location contract + the object-file-vs-executable
spec discrepancy (→ /repl/`/spec`, already correctly owned `/repl`); 0545 §3.3 L3 packing spec
example (→ /repl). None blocks the /arch rulings above.

## Skill plans (Phase 3)

### /qa — sprint-wide failing-test plan
- **Task:** author the QA-first failing test set for the burn-down. Full plan: `tests/plan/s106-test-plan.md` (registered in `tests/CLAUDE.md`).
- **Coverage:** 5 RED-first defect repros (~11 e2e: 0541, 0542, 0546, 0548, 0551) + 9 behaviour-change guards (~22 e2e: 0539, 0540, 0543, 0545, 0549, 0550, 0538, 0365, 0416) + 2 GREEN robustness (0544 non-TTY byte-identical, 0499 L-S1 preamble grid). 0496/0498 carry unit-tier obligations, no /qa e2e.
- **Blockers surfaced:** (1) `--features agent` does NOT compile on `main` — a `/dev` "step 0" build fix precedes the 0541 RED repro; (2) harness has **no PTY** — 0551 interactive-exit and 0544 arrow-keys are not e2e-reachable, so those seams get named `/dev` unit tests + piped guards instead.
- **Acceptance:** every in-scope fix has a failing-not-ignored test (or a documented unit-tier disposition); exact-output over substring; the 22 intentional guards untouched; 0499 deletable at close once L-S1 lands.

### /repl — REPL experience-spec contracts (all in `repl/spec.md`)
- **Task:** pin the experience contracts for the REPL/CLI batch. **Settled + user-signed-off 2026-07-09:** 0539 (§0.6 flag hard-errors), 0540 (§17.19 docstring axis + §17.19.1a ranking), 0543 (§17.19 exact-in-scope surfacing), 0549 (§15.7/§18.8 backing-file scribe), 0544 (§10.8 line editor — history persists per-project to `<project_root>/.cranelisp_history`, cap 1000), 0545 (§3.3 L3 rule kept, flawed example corrected), 0550 (§0.2.1/§0.2.1.1 — exe = entry-module stem next to its source, `-o` override, collision-diagnostic MUST, executable wording).
- **Acceptance:** `/dev (src/)` implements against the pinned §§; 0544+0551 co-land in one `src/main.rs` read-loop slot; 0538/0548/0549 co-land in one `save.rs` slot; `/qa` guards each.

### /spec — semantics (both items already shipped S91)
- **Task:** ratify + close WS-H. 0416 (bitwise primitives) and 0365 (`Type.member`) verified shipped S91 with green tests. One additive line in `spec/appendix-a-builtins.md §A.3` records the no-logical-`ushr` decision. User ratified single arithmetic `shr` + shift-count mod-64.
- **Acceptance:** spec matches shipped+tested impl; `/spec` deletes stale 0365 FIXME, `/arch` deletes stale 0416 FIXME (in Phase 5, after re-confirming green).

### /arch — display-protocol design + perf-backlog skeleton
- **Task:** (1) FIXME 0050 display-protocol **mechanism design** authored at `design/arch/display-protocol.md` — **CONVERGED at architecture level** (not just "started"): declarative structural render opt-in on the type def (data, not code), extending the landed `DisplayDescriptor` ABI (`DescriptorKind::Collection`), folded by the two existing formatters; typecheck is passthrough-only (the litmus the balloon was contained). §1.5 promotion explicitly deferred to the follow-on. (2) `design/arch/backlog/performance.md` skeleton refined (§1–§5, provenance contract, deletion-ownership table) — full per-item fill is Phase 5.
- **Open (user's to arbitrate, WS-I, non-blocking):** (a) should the language grow a `deftype` render-annotation surface at all? (arch rec: yes, type-local, Principle-19-clean); (b) does REPL display force a lazy `Seq` tail to a bound? (arch rec: no — non-forcing `+more`, keeps REPL echo ↔ trace byte-identical).
- **Acceptance:** design self-contained, cites landed ABI, no `cranelisp-types` edit this sprint, blocks no fix wave.

## Waves (Phase 4)

**All source-touching work runs SERIALLY** (user directive 2026-07-09 + broken worktree isolation). One `/dev` (or test-running) agent at a time; the next slot starts only after the prior slot's `/review` closes and the suite is green. Non-source work (docs, FIXME deletions, backlog fill) also runs serially in this plan.

### Stage 1 — QA-first (Wave 0)
- **W0 · /qa** — author the sprint-wide failing tests per `tests/plan/s106-test-plan.md`, failing-not-ignored, for everything buildable on the **default** build. The 0541 test (`--features agent`) is deferred into Slot 1 (needs the agent build fix first). Confirm RED via `cargo nextest run --no-fail-fast`; do not disturb the 22 intentional guards.

### Stage 2 — per-cluster D/D/R (serial slots, in order)
| Slot | Cluster | FIXMEs | Crate/area | Notes |
|---|---|---|---|---|
| **1** | Agent surface | build-fix (step-0) → 0539 → 0541 | `src/` (`main.rs`, `agent/`) | fix `--features agent` build break FIRST, then flag hard-errors, then transcript-pairing crash; /qa adds 0541 RED here |
| **2** | save.rs authorship | 0538, 0548, 0549 | `src/save.rs` + Pass-0 peel | co-land (shared file); each guarded by its /qa repro |
| **3** | main.rs read-loop | 0544, 0551 | `src/main.rs` | co-land (same read loop); adds `rustyline` default-build dep; TTY-gated; non-TTY byte-identical |
| **4** | `--link` output | 0550 | `src/session_v4/lifecycle.rs` | exe = entry-module stem next to source; `-o`; collision-diagnostic MUST |
| **5** | Introspection/display | 0542, 0546, 0545 | `src/repl.rs`, `src/display.rs` | trait `;defn/;impl`; `/imports` shared layout; L3 packing |
| **6** | `/search` | 0540, 0543 | `src/repl.rs` + index | docstring axis + exact-in-scope ranking (§17.19.1a) |
| **7** | Test-hygiene | 0496, 0498 | `src/`, `cranelisp-types` | verify src/ residual; types marshal drift-guard |
| **8** | Docs | 0547 | `user/` | platform-consumption discoverability (no source) |
| **9** | WS-I design | 0050, 0463 | `design/arch/`, `examples/` | finalize 0050 design → **USER REVIEW GATE**; 0463 example (needs infra) |
| **10** | Verify-and-close + WS-J | 0365, 0416; WS-J ×11 | FIXME files + `design/arch/backlog/performance.md` | confirm S91 green + delete stale 0365/0416; /arch fills backlog doc; owning skills delete perf FIXMEs |

**0499 L-S1** (session-history preamble grid) rides W0/Stage-1 (/qa). Wave-gate before each slot: scan `design/arch/fixmes/` for `target:` in-slot + `status: open`.

## Notes

- Phase 1 scope drafted + approved 2026-07-09. User direction: clean up all aging items; suspend perf/parallel to an owned design doc; defer 0052 only; start 0050 + 0463; bitwise (0416) + line editor (0544) included per /sprint recommendation (line-editor dep gated on /arch Phase 2).
- 0499 rescoped to L-S1 (land) + L-M1 (retire to WS-J) → closes at S106. Confirmed with user 2026-07-09.
- Per-submodule test-file reorg (S101 audit, FIXMEs 0495/0500/0501/0502) confirmed complete; platform/primitives crate-root `tests.rs` left by intent. Not in S106 scope.
- 2026-07-09: Phase 1 approved by user; advanced to Phase 2, /arch dispatched for architecture review.
- 2026-07-10: **Slot 2 (save.rs cluster) — CLOSED.** Cleanups applied (shared `is_internal_listing_name` predicate — Principle 7; corrected comment; stale doc fixed; data-loss guard `regen_preserves_user_defn_named_like_expr_wrapper` GREEN). Suite 4177 passed / 11 failed (other-slot REDs) / 1 skipped, zero new regressions. FIXMEs 0552 (/design, action before close) + 0553 (/typecheck+/backend, carry) filed by /arch.
- 2026-07-10: **Slot 7 (test-hygiene — 0496 + 0498) — CLOSED.** +24 unit tests; marshal byte-offset drift-guard; check.rs/newtype.rs covered; 0496 residual tested-or-documented-as-e2e-bound (/sprint ratified). Both unit obligations MET → closeable. Suite 4234 run / 4233 passed / 1 failed (0528 baseline). Latent findings noted (non-blocking): `MethodResolutions` not serde_json-safe; types↔typecheck marshal ctor-order edge unassertable-from-types.
- 2026-07-10: **0050 design review — USER RULED (2026-07-10).** (1) **NO render-annotation surface** — List/Seq render handled compiler-internally; user custom-render needs → a future Display-style trait (the code-bearing trait §9, out of this mechanism); overrides arch's declarative-annotation rec. (2) **NO forcing** — non-forcing `+more`, byte-identical to trace (confirms arch rec). /arch to reconcile display-protocol.md §3/§4/§8/§10/§11 to these rulings. Both non-blocking (design-only; §1.5 promotion is the follow-on sprint).
- 2026-07-10: **CLOSE-OUT SWEEP (FIXME burndown deletions + design reconciles):**
  - **/arch:** 0050 reconciled to user rulings (compiler-internal seed; Principle-19 narrowing; non-forcing); `performance.md` backlog authored (11 items + L-M1, 5-field provenance); deleted **0521, 0526, 0416**.
  - **/design:** 0552 §10 reconciled (false premise retired, driver-replay recorded); deleted **0552, 0506, 0507, 0510, 0528, 0534, 0535, 0536, 0466, 0538** (10).
  - **/repl:** §10.8 invalid-UTF-8 carve-out added; deleted **0539, 0540, 0543, 0544, 0550** (+ 0545 in progress).
  - **/qa:** agent-dormancy hermeticity fixed (`without_agent_provider()` — verified 63/63 with ambient key); reversed link test ratified; deleted **0541, 0542, 0546, 0548, 0551, 0499** (6). Suite: default 4233 passed / 1 failed (0528) / 1 skipped; `--features agent` 4384 passed / 1 failed (0528). S106 RED count zero.
  - **Remaining:** /repl 0545; /docs 0547 (+cli note); /arch 0549; /spec 0365; /port 0408; /examples 0463.
- 2026-07-10: **Source + test-hygiene slots (1–7) COMPLETE. Entering close-out tail** (non-source): 0050 design reconcile + WS-J perf consolidation (/arch); 0552 §10 reconcile (/design); verify-and-close 0365/0416; 0547 docs; 0463 examples; Phase-6 /repl Minor-2 note + /qa ratifications/hermeticity.
- 2026-07-10: **Slot 6 (`/search` — 0540 + 0543) — CLOSED.** `docstring_excerpt` UTF-8 panic fixed (match position scanned on original char boundaries) + Unicode guard test (verified panics on old code). Suite 4210 run / 4209 passed / 1 failed (0528 baseline) / 1 skipped, `--features agent` clean. **ALL SOURCE-FIX SLOTS 1–6 DONE — every S106 RED green.**
- 2026-07-10: **Slot 6 (`/search` — 0540 + 0543) — /dev + /review done; /dev fix in progress. ALL ~20 S106 REDs GREEN** (suite 4207 run / 4206 passed / 1 failed [0528 baseline] / 1 skipped). /dev: collapsed the index into one `entries` table with a docstring axis + `MatchTier` total-order ranking (§17.19.1a); exact-in-scope surfaced marked (0543); agent `/search` pull goes through the same ranked path; `--features agent` verified clean. /review: all 6 risk areas clean, one **Important** — `docstring_excerpt` UTF-8 byte-offset panic (offset from lowercased copy indexes original string; length-changing case-fold → panic on user input, violates no-panic-on-user-input). /dev fixing + a Unicode guard test. Source-fix slots (1–6) essentially complete after this.
- 2026-07-10: **Slot 5 (introspection/display — 0542 + 0546) — CLOSED.** Blocker fixed (both `src/agent/harvest.rs` callers pass `true`), doc link fixed. `--features agent` clean + agent lane passes; default suite at 5-failure baseline (0528 + 4 Slot-6 search REDs). 0542 + 0546 done. **Phase-6a /qa item (recurring):** `tests/agent.rs::agent_on_no_provider_is_dormant` is non-hermetic (fails when ambient `ANTHROPIC_API_KEY` is set) — the `.env()` builder should unset it. Flagged in Slots 1 & 5.
- 2026-07-10: **Slot 5 (introspection/display — 0542 + 0546) — /dev + /review done; /dev fix in progress.** 0542: root cause was subtler than the pin — the `; impl:` section was dropped when a trait had zero impls; /dev threaded a `full_trait_sections` context bool (bare-lookup/`/sig`/`/info` = show empty `; impl:`; definition-echo = omit per §1.1). 0546: extracted `append_layout_body`, routed the prelude group through the shared L0–L4 formatter (Principle 7), header comment preserved. /review: risks 2–5 clean, but **BLOCKER** — the new 4th param broke two `--features agent` callers in `src/agent/harvest.rs` (default `nextest` doesn't compile the agent module, so /dev missed it). Fixing (+ a dangling doc-link nit). **METHODOLOGY NOTE (recurring):** any slot changing a shared/`pub` signature MUST verify `cargo check --features agent` — hit in Slot 1 (build break) and again here. Fold into remaining slot briefs + the sprint retro.
- 2026-07-10: **Slot 4 (`--link` output, 0550) — CLOSED.** `derive_link_output_path` (entry-stem beside source), `-o`/`--output` flag, directory-collision diagnostic; 6 units + 2 /qa guards GREEN; suite 4191 passed / 8 failed (other-slot REDs) / 1 skipped. /review CLEAN. **Phase-6 follow-ups:** /qa ratifies the one reversed test `link_default_output_is_entry_stem_no_extension` (correct, boundary formality); /docs/§0.2.1.1 one-line note that the `entry.cl`+`entry/`-submodule layout now gets a clean "use -o" diagnostic (was a raw `ld` error). FIXME 0550 fully actioned (spec+guards+impl), ready to delete.
- 2026-07-10: **Slot 3 (read-loop / line editor) — CLOSED.** Important-1 fixed (`saw_newline` flag → `\r` stripped only on `\n`-delimited lines, matching `.lines()`; 2 `\r`/EOF guards GREEN); dead prompt methods removed; golden byte-identical. Suite 4193 run / 4183 passed / 10 failed (other-slot REDs) / 1 skipped, zero new regressions. rustyline 14 added. **Phase-6 /repl task:** record the intentional §10.8 invalid-UTF-8 lossy-continue divergence (Minor-2).
- 2026-07-10: **Slot 3 (read-loop / line editor) — /dev + /review done; /dev cleanup in progress.** New `src/repl_input.rs` (`ReplInput`: TTY rustyline / Piped direct fd-0 byte-wise); `rustyline 14` default-build dep; per-project history `<project_root>/.cranelisp_history` cap 1000; consent seam shares the one reader; 0551 BOTH seams (platform restore-flags + host WouldBlock≠EOF + byte-wise no-over-read). /dev root-caused 0551: the old `stdin.lock().lines()` 8 KiB BufReader read the whole piped input ahead → read-line hit EOF. /review: no Blocker (rustyline tree clean, both seams load-bearing, prompts can't drift), but found **Important-1** — unconditional trailing-`\r` strip diverges from `.lines()` on an unterminated final line (byte-identical MUST violation the single golden missed) + dead prompt methods (Minor-3). /dev fixing both + a `\r`/EOF guard. **Minor-2 (deferred to Phase-6 /repl):** the new invalid-UTF-8 lossy-continue is BETTER than the old session-kill — /review said keep it; /repl records the intentional §10.8 divergence in the spec at Phase 6 (not a code change).
- 2026-07-10: **Slot 2 (save.rs cluster) — /dev + /review + /arch done; /dev cleanup in progress.** 0538 (source-first regen — /dev found REPL trait/type decls were DROPPED entirely; now emitted verbatim-source-first), 0548 (record-after-resolve in the Pass-0 peel — failed structural forms never persist), 0549 (`__expr` filter). **Escalation:** /dev found the Phase-2 ruling #3 premise FALSE — the T1 reload re-reads the FILE, so the persisted `__expr` re-mints the same-module mono; naive filter regressed a guard. /dev added driver-replay (`capture_instantiation_drivers` + `reload_module(extra_forms)`). /review: no Blocker, but escalated the design-conformance divergence (driver-replay vs §10 CS-1 SET-capture) + a Minor data-loss edge (`starts_with("__expr")`). **/arch ruled ACCEPT** (legitimate S106 endpoint, parity, full SET-capture needs a nonexistent int-side entry point). New FIXMEs: **0552** (`target:/design` — reconcile §10; ACTION before close, small doc edit) + **0553** (`target:/typecheck+/backend` — general SET-capture entry point; CARRY, rides increment-I monomorphisation). /dev applying the 2 Minor cleanups (exact-match filter + comment) + a data-loss guard to close. Suite after Slot 2: 4176 passed / 11 failed (other-slot REDs) / 1 skipped.
- 2026-07-10: **Slot 1 (agent surface) — CLOSED.** /review's wire-coalescing Blocker resolved: rig-core 0.39 confirmed NOT coalescing; /dev added `transcript_to_messages` (folds contiguous ToolResult run → one wire User message), 2 wire-level tests (RED-before verified), guarded the submit-not-last residual (`submit_repair_interleaved_in_batch_is_known_wire_invalid_residual`), cfg-split usage string. Agent lib 107/107, e2e 63/63, default build zero new failures. 0539 + 0541 (both halves — recording + wire) DONE. (Baseline note: FIXME 0488 guard `composition_over_fold…` is nondeterministic/flaky — pre-existing.)
- 2026-07-10: **Slot 1 (agent surface) — /dev done, /review iterate in progress.** /dev: fixed `--features agent` build break (`mode_summary: None` at two test-helper sites); 0539 flag hard-errors (4 guards GREEN); 0541 transcript-pairing root-fix + 2 repro tests (RED-before verified — exact FIXME panic reproduced then eliminated). /review found the fix resolves the **Turn-level panic** but the **wire lowering** (`request.rs` `history_messages`/`turn_to_message`) emits N separate single-`tool_result` user messages — the Anthropic API needs them coalesced into one; so the live multi-tool-call feature is unproven (symptom-stopped ≠ fixed). Also flagged a submit-not-last residual (#2) + usage-string nit (#3). Sent back to /dev to verify rig-core coalescing, coalesce if needed, add a wire-level test, and disposition #2. **BASELINE CORRECTION: pre-existing failing = 2** (`ownership_reuse::chaining_toggle_off_allocates_intermediate` FIXME 0528 + `generic_value_use_mono::composition_over_fold…` FIXME 0488), not 1 — reconcile the stale CLAUDE.md figure at close.
- 2026-07-09: **Phase 5 Stage 1 (QA-first) complete.** 20 new RED tests authored (default build), no regressions. **FINDING — CLAUDE.md "22 intentional guards" is STALE:** the S101 6a/6b + 0474 guards were all fixed S102–S105; actual pre-existing failing baseline is now **1** (`tests/ownership_reuse.rs::chaining_toggle_off_allocates_intermediate`, FIXME 0528). Surface to user at close (root CLAUDE.md is outside /sprint's edit boundary). **FINDING — 0538 scope:** REPL `deftrait`/`deftype` are dropped entirely from regen today (not just reformatted) — /dev must emit them first. **0545 is GREEN** (impl already conforms to reconciled §3.3; tests are boundary guards, not a fix). 0541 deferred to Slot 1 (needs agent build fix). Full detail: /qa Stage-1 report.
- 2026-07-09: **Phase 3 complete.** Four design/authority agents (/qa, /repl, /spec, /arch) ran; plans collected above. Key outcomes: (a) **WS-H reframed to verify-and-close** — /spec found 0416+0365 already shipped S91 (stale FIXMEs); voids the "gated on /spec" wave dependency. (b) **Spec review + 7 user rulings (2026-07-09):** 0544 history → per-project `<project_root>/.cranelisp_history`, cap 1000; 0545 → keep L3 rule, fix flawed example; 0550 → exe = entry-module stem next to source (`foo/user.cl`→`foo/user`), `-o` override, collision-diagnostic MUST, executable wording; 0539/0540/0543/0549 settled; 0416 → ratify single arithmetic `shr` + mod-64. All PROPOSED markers removed from `repl/spec.md`. (c) **0050 CONVERGED** as design (extend `DisplayDescriptor`); two language-level 0050 questions (deftype render-annotation surface; Seq forcing) remain open for WS-I, non-blocking. (d) **Two /qa blockers:** `--features agent` build break on `main` (a /dev step-0); no PTY in harness (0551/0544 interactive surfaces → unit tests + piped guards).
- 2026-07-09: Phase 2 complete — /arch verdict **APPROVE-WITH-REVISIONS**. Rulings: rustyline approved (default-build, TTY-gated); WS-J consolidation confirmed + provenance contract + `design/arch/backlog/performance.md` stubbed; 0549 filter ruled in; 0050 scoped design-only (extend `DisplayDescriptor`); 0416 = primitives not intrinsics, /spec-first; 0551 seam ruling delivered. Debt-table rows 0050/0416/0551 updated to match. No `cranelisp-types` change. Awaiting user sign-off to advance to Phase 3.

## Outcome (Phase 7)

### Delivered
**A FIXME burn-down: 32 open/deferred FIXMEs at Phase 1 → dispositioned every one.** ~28 resolved-and-deleted, 11 perf items consolidated to an owned backlog, 1 deferred, 1 carried (narrowed), 2 new filed (1 future-dep, 1 candidate).

- **Fresh usability batch (0538–0551), 6 serial D/D/R slots — all fixed, all guarded:**
  - **Agent surface:** 0539 (`--agent`/`--yes` hard-error on non-agent build), 0541 (multi-tool-call crash — fixed at BOTH the transcript-recording AND the wire-coalescing layers; `--features agent` build break fixed as prerequisite).
  - **Backing-file fidelity:** 0538 (source-first regen §5–7 — trait/type decls were being dropped entirely), 0548 (failed structural forms no longer persist), 0549 (`__expr` not persisted; required the §10 driver-replay Q1 prerequisite).
  - **Read-loop:** 0544 (rustyline line editor, per-project `~/.cranelisp_history`→`<project_root>/.cranelisp_history`, TTY-gated, non-TTY byte-identical), 0551 (stdin `O_NONBLOCK` leak — fixed at both platform + host seams).
  - **`--link`:** 0550 (exe = entry-module stem beside source, `-o` override, directory-collision diagnostic).
  - **Introspection/display:** 0542 (trait `;defn:`/`;impl:`), 0546 (`/imports` shared layout), 0545 (L3 packing — impl already conformant, boundary guards + corrected spec example).
  - **`/search`:** 0540 (docstring axis + §17.19.1a ranking), 0543 (exact-in-scope surfaced marked).
- **Test-hygiene:** 0496 (src/ residual — tested or documented e2e-bound), 0498 (marshal byte-offset drift-guard + check.rs/newtype.rs cover); **0499** e2e-lane L-S1 landed → deleted.
- **Design:** 0050 display-protocol design authored + reconciled to the user's 2026-07-10 rulings (compiler-internal seed, non-forcing Seq); §1.5 promotion is the follow-on sprint.
- **Perf-track consolidation (WS-J):** 11 parked parallel/memory-model items (0506/0507/0510/0521/0526/0528/0534/0535/0536/0408/0466) + 0499-L-M1 → `design/arch/backlog/performance.md` (5-field provenance), FIXMEs deleted.
- **Verify-and-close (already shipped S91, stale FIXMEs):** 0365 (`Type.member`), 0416 (bitwise primitives — user ratified single arithmetic `shr` + mod-64).
- **User-facing:** 0547 → new `user/guide/using-platforms.md` (the two-step platform-consumption walkthrough) + `cli-reference.md` `-o`/naming; 0463 → new green `examples/34-async-io-leaf.cl` (poll-shape platform-leaf).
- **Tests added:** 20 QA REDs→green + ~30 /dev unit tests + review-driven guards (wire-coalescing, `\r` byte-identity, docstring UTF-8 panic, `__expr`-lookalike data-loss, marshal drift). Suite: **default 4234 run / 4233 passed / 1 failed / 1 skipped; `--features agent` 4385 run / 4384 passed / 1 failed** — the sole failure both builds is the pre-existing 0528 baseline (`ownership_reuse::chaining_toggle_off_allocates_intermediate`). S106 RED count zero; zero new regressions.

### Deferred (with rationale)
- **0052** (`/learn` subsystem) — no current pull; first hard deferral (originally S64). Revisit when scheduled.
- **0463** — CARRIED, narrowed: the poll-shape **network/socket** example (the leaf example 34 was the start). Narrowed scope: "a shared `platforms/` socket leaf (accept/read/send) + client-connect leaf so a single `--run` self-drives." Owner `/platform` + `/arch`.
- **Perf/parallel arc (11 items)** — NOT deferred-in-place; consolidated to the backlog doc as pre-assembled re-entry scope (S105 accept-done stands).
- **New this sprint:** **0553** (`/typecheck`+`/backend` — general SET-capture "instantiate symbol at types" entry point; rides increment-I monomorphisation) — genuine future dependency, not S106-actionable.

### Findings
- **⚠️ Root `CLAUDE.md` "22 intentional failing guards" figure is STALE** — those S101 6a/6b + 0474 guards were all fixed S102–S105; the actual pre-existing failing baseline is now **1** (`tests/ownership_reuse.rs::chaining_toggle_off_allocates_intermediate`, FIXME 0528), plus the **flaky/nondeterministic** `generic_value_use_mono::composition_over_fold…` (FIXME 0488). Root CLAUDE.md is outside `/sprint`'s edit boundary — **flagged for the user to correct** the §Testing itemization.
- **Methodology (recurring, worth a standing rule):** any slot changing a shared/`pub` signature MUST verify `cargo check --features agent` — the default `nextest` run does not compile the agent module, so signature drift there is invisible (bit Slot 1 as a build break and Slot 5 as an uncompiled-caller Blocker).
- **The serial D/D/R + adversarial `/review` cadence paid off every source slot** — each `/review` caught a real defect the `/dev` self-verification missed: wire-coalescing Blocker (S1), reload-fidelity false premise (S2), `\r` byte-identity (S3), agent-feature build break (S5), docstring UTF-8 panic (S6). Strong validation of "verify the fix, not the symptom's absence."
- **Phase-2 /arch ruling #3 premise was found false in Slot 2** (the T1 reload re-reads the file, not the in-session entry) — corrected via 0552 (§10 reconcile); the general fix is 0553.
- **Two already-shipped features carried stale un-deleted FIXMEs** (0365, 0416 from S91) — verify-and-close should routinely sweep for these.
- **Latent, non-blocking** (noted for future): `MethodResolutions` is `Serialize`-derived but not serde_json-safe (Span-keyed maps; never JSON-cached); the types↔typecheck marshal ctor-order edge is unassertable from `cranelisp-types` (dependency direction).
- **Candidate follow-up (user's call, NOT filed):** a friendlier `platforms.stdio` near-miss diagnostic ("did you mean `platform.stdio`?") — docs closed the discoverability gap; this is an ergonomic nicety, `/dev` src module-resolution, wording via `/repl`/`/spec`. Left unfiled per user (2026-07-10) to avoid re-inflating the FIXME count.

### Close actions (Phase 7, user-approved 2026-07-10)
- Root `CLAUDE.md` §Testing "22 intentional failing guards" itemization + hard-coded pass/fail counts **REMOVED** (user directive: brittle, constantly-changing, already knowable) — replaced with a durable pointer to `cargo nextest run` + `design/arch/fixmes/` + `tests/plan/ledger.md`. This resolves the stale-figure finding without re-introducing a figure to rot.
- FIXME directory drained **32 → 4 carried** (0050 follow-on-gate, 0052 deferred, 0463 narrowed-carry, 0553 future-dep). SPRINT.md archived → `sprints/archive/sprint-106.md`; `ROADMAP.md` updated; committed to `main`.
