# S109 attribution: the racy background stdlib file-index feed (phantom prelude write)

**Author:** `/qa` · **Date:** 2026-07-15 (S109 Phase 6 attribution dispatch) ·
**Status:** ATTRIBUTED — user-ruled disposition: attribute now, **fix carried to
S110** (tracking FIXME `design/arch/fixmes/0604-index-feed-phantom-prelude-write-race.md`;
coverage gate FIXME `0605-stdlib-compile-smoke-gate.md`).

This is the durable attribution record for the S109 Phase 6 concurrency defect
(defect #1, the `num.bits` super-import failure) and the family verdict
connecting it to the other S109 index-feed findings. The `/testing` twin guards
(`ea77dad8`) are the committed behavioural record; this document is the
mechanism/ownership record.

---

## 1. The defect

**Symptom.** Importing `stdlib/num/bits` fails intermittently with:

```
dependency 'num.bits.test' failed: type error … ambiguous bare name 'bit-and'
— provided by distinct sources 'num.bits/bit-and' and 'primitives/bit-and'
```

Blast radius: all 27 `num.bits` self-tests blocked; `num.bits` is unimportable
whenever the race fires. Any stdlib module with the same shape (a `.test`
submodule `(import [super [name]])`-ing a parent wrapper whose bare name also
names a primitive) is exposed.

**Established root cause** (two `/testing` reduction passes + `/sprint`
verification): a **race in the background stdlib file-index feed**
(`src/session_v4/index_worker.rs` + the import/prelude installer path it drives)
intermittently injects a **phantom public `bit-and → primitives/bit-and` entry
into the live `prelude` module's symbol table** — even though
`stdlib/prelude.cl` exports only `[Int Bool Float String]` and no stdlib module
re-exports `bit-and`. With the phantom present, `num.bits.test`'s legitimate
`(import [super [bit-and]])` (terminal `num.bits/bit-and`) meets the phantom
prelude terminal (`primitives/bit-and`) — two DISTINCT terminals — and the
§8.6.5 peer-poison fires **spec-correctly**. The compile fails.

**What is NOT the bug** (attribution boundaries, so no one re-litigates them):

- `src/imports.rs::insert_detecting_ambiguity` (prelude-overlap branch,
  ~L547–560, via `prelude_terminal`) — the poison-CONSUMER — is **CORRECT**.
  The deterministic `_neg` twin proves the same poison is required when the
  prelude legitimately provides the primitive (glob export). Do not weaken it.
- Not a cache defect: fires with all `.cranelisp-cache` cleared AND `--no-cache`.
- Not the §8.6.5 spec semantics: the spec ruling (prelude glob is a PEER of an
  explicit import, no precedence tier) is settled and pinned.

**The bug is the phantom WRITE into the live prelude table**, upstream of the
(correct) poison.

## 2. Mechanism and seam

The index worker's branch (c) (`index_worker.rs::index_branch_c`) typechecks
candidate stdlib modules **through the real import-installing path**
(`cluster::process_cluster` — installs the module's `(import …)` decls and the
prelude env, runs `check_forms`) **directly against the LIVE
`symbol_tables`**, then "REMOVES the live residue" claiming the R13 invariant
(the four `SharedState` maps stay byte-unchanged). That
**mutate-live-then-undo** discipline, running concurrently with user compiles
and with other index workers, is the structural defect surface: a binding
written during a concurrent index pass either lands in the WRONG table (a
mis-attributed import-direction write reaching `prelude`'s table) or escapes
the residue cleanup. R13 is violated in the observed failure — the prelude
table is NOT byte-unchanged after the feed runs.

**Fingerprint of a concurrent mis-attribution** (not a systematic resolver
bug): only `bit-and` leaks — never the identically-shaped `bit-or` / `bit-xor`
wrappers sitting beside it in the same module. A deterministic resolution
defect would leak all three uniformly; leaking exactly one of three identical
shapes is scheduling-dependent write placement.

**Scheduling dependence.** Deterministic in some environments (16/16 for
`/sprint`, repo-root and clean cwd), 0/140 in `/testing`'s earlier runs.
Consistent with a worker-interleaving-dependent write, not with input-dependent
logic. Per the forbidden-dispositions doctrine (`tests/CLAUDE.md`
§Failing-test discipline): this is a real race, not "flaky" — the environment
sensitivity is itself evidence of the class.

## 3. Repro and committed evidence

**Deterministic repro recipe** (fires ~16/16 in the `/sprint` environment;
scheduling-dependent elsewhere):

```bash
printf '(import [num.bits [bit-and]])\n(import [primitives [Int]])\n(defn use-it [:Int x] :Int (bit-and x 7))\n' > /tmp/di.cl \
  && CRANELISP_LIB=/home/alilee/cranelisp/stdlib \
     /home/alilee/cranelisp/target/debug/cranelisp --no-cache --run /tmp/di.cl
```

Trace the write with `CRANELISP_MODULE_TRACE=1` over the full `stdlib/`.

**Committed guards** (`/testing`, `ea77dad8`,
`tests/spec_08_prelude_outer_scope.rs`) — both GREEN, twin-shaped:

- `super_import_wrapper_over_specific_prelude_compiles_clean` — the CORRECT
  pole: specific-export prelude (never provides `bit-and`) → the super-imported
  wrapper is the sole terminal → compiles clean, runs to 8. Goes RED if the
  phantom write ever becomes deterministic in the reduced fixture.
- `super_import_wrapper_collides_when_prelude_globs_primitive_neg` — the
  deterministic twin of the SEAM the defect abuses: glob-export prelude
  legitimately provides `bit-and` → two distinct terminals → poison fires,
  spec-correct. Reproduces the exact live error signature.

The difference between the twins is exactly the phantom prelude binding. There
is **no stable RED for the race itself** — the free-standing reduction could
not make the WRITE trigger deterministic, and committing an intermittent RED
would itself be a defect. This is the case the FIXME protocol exists for (a
testless-in-the-RED-sense defect: the GREEN twins pin the poles; FIXME 0604 is
the record + trigger). The S110 fixing change-set OWES the fail-on-revert
guard: a repetition sweep (≥25 iterations, per the S109 C1-e2e precedent) of
the deterministic recipe against the full stdlib, landing WITH the fix.

## 4. The family — "racy background index feed" (one root, several faces)

Class name: **concurrency mis-attribution in the background stdlib file-index
feed** — background index workers sharing LIVE session state with the
foreground compile, with correctness resting on undo-discipline instead of
isolation.

| Face | Status | Linkage |
|---|---|---|
| **#1 phantom prelude write** (this record) | OPEN — the root instance | The write race itself; FIXME 0604 |
| **#4 `/search` private-submodule leak** | Surfacing fixed (`fff94fa7`, subtree-visibility filter at search time); **underlying index WRITE-race NOT fixed** | Same feed. The search-time filter cures what the index SHOWS, not what it WRITES — which is why #1 still fires after `fff94fa7`. Folded into FIXME 0604 |
| `concurrency_capacity::same_token_capacity_n_blocking_admits_n_concurrent_nplus1_parks` timing flake (pass/fail/pass in isolation, `/sprint` S109) | CANDIDATE same-root — **unverified** | Different subsystem (token-capacity trampoline scheduling), but the same scheduling sensitivity. Listed as a verification step in 0604, NOT asserted — folding an unverified instance is exactly the mis-attribution failure this record exists to prevent |
| `agent_flag_errors_on_non_agent_build` build-interleave race (SPRINT.md §Findings) | SEPARATE root — test-infra (nextest build-artifact clobber), not the index feed | Related in spirit only (background work racing a foreground consumer). Stays a `/qa`/`/testing` infra carry; addressed alongside the 0605 gate work, not folded into 0604 |

**Historical lineage (why the cure must be structural).** The
shared-live-table concurrency class has prior form in `src/`:
`design/int/heisenbug-race-closure.md` (S61) documents a treadmill of
per-interleaving patches (H4→H7) that each closed one window while the race
resurfaced through the next; the durable close was structural (the S93
signature/body pre-pass barrier, `design/int/signature-body-prepass.md`). The
index feed re-instantiates the same shape: background workers mutating live
shared state, correctness by cleanup. Expect the same lesson — **isolate the
indexer's typecheck from live state (staging/discard substrate), don't patch
interleavings** — and treat any proposed one-window fix with suspicion.

## 5. Owner attribution

**Owner: `/dev`, narrow-deployed to `src/` (int layer), with `/design` (int)
recording the isolation contract.** Reasoning:

- The seam is wholly int-owned: `src/session_v4/index_worker.rs` (the write
  path and the R13 undo discipline) + the import/prelude installer it drives
  (`src/imports.rs` writers). No crate boundary is crossed by the fix.
- It is **NOT folded into FIXME 0583** (the S110 centrepiece:
  backend-as-pure-keyed-consumer). 0583 is a *backend* bounded-context
  violation (two resolvers, one name — backend re-resolving what typecheck
  already resolved). This defect is an *int-layer shared-state isolation*
  violation (one resolver, but its live substrate is written concurrently by a
  background feed). Different crate, different seam, different cure. Folding
  them would blur both attributions. They ARE thematically adjacent — both are
  S110 "one source of truth for resolution state" work — so 0604 is scheduled
  S110 alongside 0583 and `/sprint` may wave them together, but they remain
  separate FIXMEs with separate acceptance criteria.
- `/design` (int) participation: the durable cure is a design decision
  (indexer typechecks into isolated staging / the discard substrate, never
  live; R13 becomes true by construction, not by cleanup), and the S61→S93
  precedent says the design record is what prevents the patch-treadmill.

**One-vs-many verdict: ONE family FIXME (0604)** for the write-race, folding
#1 and #4's residual underlying race (same feed, same fix); the
`concurrency_capacity` flake rides as a named verify-after-fix step; the
build-interleave infra race stays separate (different root). Plus ONE process
FIXME (0605) for the coverage gate — a gate is not a fix and has a different
owner (`/testing`), so it does not share 0604.

## 6. The coverage gap that let it ship — and the gate

**Gap:** stdlib self-tests are not in `cargo nextest`. By design, `tests/` is
stdlib-free (root `CLAUDE.md` §Design Principles, Stdlib separation), and the
only sanctioned stdlib touchpoints are the narrow
`use_workspace_stdlib_for_stdlib_conformance_only()` call-sites (repl_persist,
regression — none of which import the full stdlib module surface). So a
compiler regression that breaks *stdlib compilation or importability* —
exactly this defect's blast radius — is invisible to the suite: 27 self-tests
were failing and no CI signal existed. This is a real gate gap, not a
discipline lapse: the separation principle is correct for language validation,
but it needs a paired conformance gate on the stdlib side.

**Recommendation (FIXME 0605, target `/testing`, S110):**

1. **Stdlib-compile smoke gate** (the cheap, high-value tier): one e2e test
   family behind the existing named exception
   (`use_workspace_stdlib_for_stdlib_conformance_only()`) that `--run`s a
   program importing **every top-level stdlib module** (enumerated from
   `stdlib/`, not hand-listed, so new modules join the gate automatically) and
   asserts clean compile + exit 0. Catches the deterministic face of any
   "stdlib unimportable" regression class. Single-shot — it will NOT reliably
   catch this race in environments where the race is quiet (0/140), and that
   is acceptable: its job is the CLASS (stdlib-breaking compiler regressions
   can't ship invisibly), not this instance.
2. **Race-specific guard rides the S110 fix** (owner `/dev`, enforced by the
   0604 acceptance criteria, per §3): the ≥25-iteration repetition sweep of
   the deterministic recipe lands WITH the fix and fails on revert. Not
   committed before the fix — an intermittent RED is its own defect.
3. **Stdlib self-test execution gate** (follow-on, `/stdlib` + `/testing` to
   size): drive the stdlib's own test runner (`discover-tests` over
   `stdlib/**/*.test`) as a suite-level job so the 27-self-test class fails
   loudly, not silently. Sized separately because it couples to the test
   runner's maturity; the compile smoke (tier 1) is the S110 must-have.
