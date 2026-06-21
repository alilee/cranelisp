# S87 — Cost-to-Clear: All Non-Phase-H FIXMEs

> **What this is.** A read-only planning analyst pass (in support of `/sprint`) scoping
> exactly what it would take to clear **every open FIXME except the three Phase-H carries
> the user confirmed STAY** (0050, 0052, 0365). The user's stated goal: *"we don't want
> to carry anything."* For each of the 10 remaining FIXMEs this gives concrete work,
> size, ordering/dependencies, risk, verification, and a clear-now-vs-stay recommendation.
> Then a serialized clear-all plan with the critical distinction the user must see:
> **debt-closure vs feature-build vs design-ruling** — not all "clears" are the same kind
> of work. Date: 2026-06-20. READ-ONLY; this is the only file written.

---

## 0. Headline — the three kinds of "clear"

The 10 FIXMEs do **not** clear by the same mechanism. Sorting them by *kind of work*
(not by owning skill) is the single most important framing for the gate:

| Kind | Meaning | FIXMEs |
|---|---|---|
| **A. Debt-closure** | Consolidate/refactor already-shipped, correct code; or write a missing test/doc. No new user-facing capability. Safe to force-clear. | 0406, 0409, 0415, 0417, 0419, 0420 |
| **B. Design-ruling-gated** | Blocked on a `/spec` (or `/arch`) decision *before* implementation; the ruling is the real work, the code is small. | 0410, 0416 |
| **C. Feature-build** | Clearing = building a genuinely new capability (ABI surface, exemplar rework). This is NOT "closing debt" — it is committing engineering to a feature. Forcing it to clear is a roadmap decision, not a cleanup. | 0407, 0408 |

**The user's "don't want to carry anything" is cheap for kind A, a decision-cost for
kind B, and a real-feature-commitment for kind C.** 0407 (Model-B closure-callback, ABI
v3→v4) and 0408 (Sudoku parallel-search rework) are features dressed as FIXMEs; clearing
them means *building them*, with the attendant risk and multi-day cost. They are flagged
throughout as "unwise to force-clear as cleanup."

A second cross-cutting fact: **0419 is the hard prerequisite for 0407**, and the
synthesis is explicit ("Do NOT widen `HostCallbacks` for 0407 before this builder
lands"). So if both clear, they serialize: 0419 → 0407. And **0408's parallel-search
axis is independent of 0407's web-concurrency axis** (the FIXMEs say so explicitly), so
0408 does not need 0407.

---

## 1. Per-FIXME cost-to-clear

### 0406 — /int — friendly `--link` rejection for REPL-only externs

- **Kind:** A (debt-closure / better-error). Pure `/dev` int change, one crate seam.
- **What it takes:** In the `--link` artifact-assembly path (`src/`, before the `cc`
  invocation), scan modules pulled into the link for a referenced
  `DefKind::PrimitiveExtern` whose body is dev-session-promised (today: `discover-tests`)
  and emit a friendly `CranelispError` instead of letting `cc` produce
  `undefined reference to discover-tests`. Use a **kind/metadata predicate**, not a
  string match on `discover-tests`, so it generalizes. Must NOT reject `catch-runtime-error`
  (self-contained, resolves under `--link`). Backend's `apply.rs` `Linkage::Import` arm
  is unchanged — int is the seam that knows build mode.
- **Owner(s):** `/int` (impl). `/arch` records §4.5 interim→friendly when it lands. `/qa`
  **retargets the existing repro** (the `assert_failure` half is stable; only the message
  substring shifts from `cc`'s "undefined reference" to the friendly "REPL/dev-session-only").
- **Size:** **S** (<½ day). One scan + one error construction; the design sketch is in
  the FIXME.
- **Dependencies / ordering:** None. Standalone.
- **Risk:** **Low.** No semantics change ("dev-session-only" stays settled); purely a
  better diagnostic. Only subtlety: getting the predicate generic (kind-driven) rather
  than name-matched, and not catching `catch-runtime-error`.
- **Verification:** **Repro already exists** —
  `tests/link.rs::link_module_referencing_discover_tests_extern_resolves_at_aot_link`
  currently asserts the interim (non-zero exit + raw linker substring). `/qa` retargets
  the substring; same `assert_failure`. Add a `/dev` unit test on the gate predicate.
- **Recommendation:** **Clear-now-feasible.** Cleanest of the 10. Aligns with the
  root-CLAUDE.md "no opaque error" principle. Do it.

### 0407 — /arch — Model-B closure-callback (ABI v3→v4)

- **Kind:** **C — feature-build.** This is *not* debt; it is an unbuilt capability
  (platform DLL calling back into a cranelisp closure, the `serve port handler` model).
- **What it takes:** (1) a `CLClosure`/`CLFn` `#[repr(transparent)]` wrapper type
  (likely `cranelisp-platform`, mirroring `CLAdt<T>`); (2) a new `HostCallbacks` method
  `invoke_closure(c, args…) -> i64`, wired host-side in `cranelisp-intrinsics` over the
  existing `call_continuation` mechanism, with a **defined contract** for capture/RC
  (closure retained for the DLL's hold-lifetime, released on `serve` return), **error-slot
  ferry** (callback panic → joining thread; intersects the standing fork-join ferry
  obligation), and **threading** (RC + error-slot must hold if the DLL calls the handler
  from a thread pool); (3) `ABI_VERSION` bump 3→4; (4) manifest/sig support unchanged.
- **Owner(s):** `/arch` (HostCallbacks ABI extension + `CLClosure` home), `/dev` platform,
  `/dev` intrinsics, possibly `cranelisp-types`. Cross-crate.
- **Size:** **L** (multi-day). New ABI surface + RC contract across FFI + threading + the
  error-slot ferry (which is itself a *pre-existing un-fixed obligation*, see §3).
- **Dependencies / ordering:** **0419 is a hard prerequisite** (synthesis §4-b: do not
  widen `HostCallbacks` by 3 fields across 2 hand-mirrored sites until one shared builder
  exists). The fork-join error-slot ferry obligation (recorded in `test-discovery.md`) is
  a co-resolution point, not yet a committed repro.
- **Risk:** **High.** New cross-FFI RC discipline + threading + panic propagation is
  exactly the class that produced DEF-6. ABI bump is a release-surface commitment.
- **Verification:** No repro exists and **none should be authored as a defect** — this is
  a missing feature, not a bug. Verification = a new e2e exercising Model-B `serve` with a
  closure handler (and a threaded-callback stress for the RC/error-slot contract). That
  e2e *is part of building the feature*, not a pre-existing guard.
- **Recommendation:** **Genuinely-should-stay-open as a FIXME** unless the user
  *decides to build Model B as a feature*. Model A already serves the complete showcase
  roundtrip; Model B's only added value is the "purity enables concurrency" teaching
  moment (documentation, not capability). Force-clearing this = committing an L-size
  ABI-bumping feature for a teaching demo. **If the user truly wants zero carries, the
  honest answer is "build it (0419 then 0407, multi-day, ABI v4) OR formally retract Model
  B from the roadmap and delete the FIXME with a rationale" — not "clean it up."**

### 0408 — /port — Sudoku parallel-search lenient-eval showcase (+ copy-per-guess perf)

- **Kind:** **C — feature-build** (demo/showcase-quality rework of real solver code).
- **What it takes:** (1) **Parallel backtracking search** — at each guess point, evaluate
  the recursive solve per candidate digit as independent `let` bindings (sparkable →
  lenient-eval parallel), take first `Success`; this is the flagship lenient-eval/auto-IO
  showcase. (2) **Fix copy-per-guess** — `eliminate`/`set-cell`/`assoc` currently copy the
  full 81-cell Vec on every edit (quadratic); replace with in-place candidate-mask or
  structural-share Vec. (3) **Supersede the Wave-4 verdict** in `plan-exemplar.md` (the
  "inherently sequential / counterexample" conclusion is wrong for the *search* dimension).
- **Owner(s):** `/port` (solver + plan-doc). Benefits from `/backend` Tier-2 (Phase H)
  for raw speed; benefits from 0416 bitwise intrinsics for the mask representation.
- **Size:** **L** (multi-day). A demo-quality solver rewrite + a representation change +
  a perf campaign (~3.3s easy 9×9 baseline; hard puzzles "run for minutes").
- **Dependencies / ordering:** lenient eval (live since S25) + auto-IO (S85) are present.
  **Soft-depends on 0416** (bitmask representation is the natural copy-per-guess fix) and
  on the **Phase-H release/Tier-2 backend** for the perf numbers (the FIXME says "a
  release build may be the better moment to land the perf numbers"). Downstream: 0409
  refresh of `sudoku.demo`; re-include the hard-puzzle test.
- **Risk:** **Medium-high.** Speculative parallel branches do pruning-skipped work
  (net-win-with-work-stealing claim is plausible but unmeasured); the representation change
  touches the curated-Vec RC path (intersects 0417/DEF-2 territory). Correctness of a
  rewritten solver needs re-validation.
- **Verification:** No defect repro (it's a quality/feature item). Verification = the
  refreshed exemplar solving correctly *and* demonstrably exercising parallelism, plus a
  re-included (now-fast) hard-puzzle test. That work *is* the feature.
- **Recommendation:** **Genuinely-should-stay-open** until coordinated with Phase-H
  Tier-2 (its own FIXME says so). Force-clearing it pre-Tier-2 lands perf numbers against
  the debug backend that the release build will invalidate — wasted measurement. **Best
  cleared as a Phase-H-adjacent showcase task, not a debt sweep.** Note: this is the only
  FIXME whose *natural home is inside the Phase-H arc* despite not being a Phase-H carry.

### 0409 — /repl — number the showcase demos for guided order

- **Kind:** A (debt-closure / affordance). Pure `/repl` change, no compiler dependency.
- **What it takes:** Rename the 8 active-set `.demo` files to numbered stems
  (`01-tour.demo` … `08-sudoku.demo`) so the alphabetical `--list` sort coincides with the
  pedagogical arc. **Preserve bare-name resolution** (`./repl/showcase sudoku` must still
  work — resolve against the numbered stem suffix `*sudoku.demo`). Update
  `repl/demos/CLAUDE.md` §"The active set" table. Optionally print a "Guided order"
  heading in `--list`. Archive demos stay unnumbered.
- **Owner(s):** `/repl`.
- **Size:** **S** (<½ day). File renames + a suffix-match tweak in `demo-player.py`/the
  `showcase` script + a doc table.
- **Dependencies / ordering:** None standalone. **Soft downstream of 0408** only in that
  0408 refreshes `sudoku.demo` content — but renaming is orthogonal to content and can land
  first.
- **Risk:** **Low.** Only hazard is breaking muscle-memory bare-name invocation; the FIXME
  explicitly calls that out as the thing to preserve.
- **Verification:** A `/repl` test-script check that `--list` order matches the arc and
  that `showcase <bare-name>` still resolves each of the 8. Per the project's repl-harness
  conventions (no compiler test needed).
- **Recommendation:** **Clear-now-feasible.** Trivial, self-contained, good `/repl` pass
  candidate. Do it.

### 0410 — /repl — scaffold default `Cranelisp.toml` on project root

- **Kind:** **B — design-ruling-gated.** The file-writing mechanics are S; the blocking
  work is a `/spec §8.11.4` semantic ruling.
- **What it takes:** **First**, settle §8.11.4 (the fork in the FIXME): either (1) confirm
  that a **present file with an absent `lib-dirs` key** falls through to lower tiers (verify
  `#[serde(default)]` + `assemble_lib_dirs` treat absent-key ≠ empty-replaces; may need a
  §8.11.4 clarification), OR (2) define normatively that "a default/empty scaffold behaves
  identically to absent." **Then** `/repl` decides the trigger + experience (recommend:
  REPL mode only, §0.5-rule-3 explicit project-root target, `[created Cranelisp.toml]`
  notice, never overwrite) and records it in `repl/spec.md §0.5`. **Then** `/int`
  implements the scaffold writer in `src/session_setup.rs` beside
  `load_project_config_lib_dirs`.
- **Owner(s):** `/repl` (experience + trigger) → `/spec` (§8.11.4 semantics, the gate) →
  `/int` (impl). Three-skill chain.
- **Size:** **M** (~1 day across three skills, but only if the §8.11.4 ruling is quick;
  the impl alone is S).
- **Dependencies / ordering:** **§8.11.4 ruling MUST land first** — this is the blocking
  design decision, not the mechanics. The footgun is real: a naive `lib-dirs = []` scaffold
  *suppresses* the tier-4 `{root}/stdlib/` fallback (fully-replaces semantics) and could
  silently break prelude loading for a project that previously worked.
- **Risk:** **Medium** — *only because of the footgun*. With the §8.11.4 ruling settled,
  the impl is low-risk. Without it, scaffolding is unsafe to ship.
- **Verification:** `/int` unit test (default-content + no-overwrite + resolution-unchanged)
  + e2e (REPL launch on a bare project dir creates the file and still resolves the prelude).
- **Recommendation:** **Clear-now-feasible but serialize the chain.** Get the `/spec`
  ruling first (cheap if §8.11.4 already implies absent-key fall-through; the FIXME's
  resolution-1 is the low-risk path). Then `/repl` + `/int`. Do not let `/int` write the
  scaffold before the ruling.

### 0415 — /repl — symbol-layout algorithm normativity + coverage

- **Kind:** A (debt-closure / normativity + test coverage). A `/repl` spec decision +
  `/qa` tests; a `/dev` int fix *only if* live output diverges.
- **What it takes:** (1) `/repl` decides normativity: promote the §3.3 multi-column
  line-breaking layout from **SHOULD** to **MUST** (recommended — exact layout is a
  self-documenting-REPL feature; SHOULD is untestable-as-written) OR keep SHOULD but state
  the example is the reference layout tests assert. (2) `/qa` authors coverage pinning each
  rule against real REPL output: operators-first + mandatory break; letter-group early-break;
  hard-wrap-at-6 in an oversized group; the <7-names single-line case; and that the **same**
  formatter serves `/list`, `/imports`, AND `/exports` (one shared formatter, not three).
  (3) `/repl` annotates §3.3/§3.4/§3.5 with `[Tested …]`. (4) **If** live output diverges
  from the algorithm, that's a defect → `/qa` files failing-not-ignored repro → `/int`
  fixes `src/pretty.rs`/the symbol-list formatter.
- **Owner(s):** `/repl` (normativity, the gate), `/qa` (tests), `/int` (only if divergence).
- **Size:** **S–M.** Normativity call is trivial; the test authoring is the bulk (M if the
  three-command-shared assertion needs new harness; S otherwise). **Unknown until tests run:
  does live output already match?** If yes, S and pure coverage. If no, a defect-fix adds M.
- **Dependencies / ordering:** Normativity decision gates the test shape (can't assert exact
  output against a SHOULD).
- **Risk:** **Low-medium.** Low if output already conforms (pure coverage). Medium if a
  divergence surfaces — then it becomes a real `/int` formatter defect with its own fix.
- **Verification:** The `/qa` tests themselves are the verification; whether they go green
  immediately (coverage gap closed) or red-first (latent divergence defect) is the unknown
  to resolve **by writing them first**.
- **Recommendation:** **Clear-now-feasible.** Make the normativity call, write the tests.
  Authoring the tests is also the cheapest way to discover whether a latent formatter
  divergence exists. Good combined `/repl` + `/qa` pass.

### 0416 — /arch — bitwise intrinsics for bitmask domains

- **Kind:** **B — design-ruling-gated feature** (it is a forward-flow language feature
  whose codegen is near-trivial, but it needs a `/spec` semantics ruling first).
- **What it takes:** (1) `/spec` decides Int width semantics + signed-vs-logical shift
  behaviour and adds the appendix-a rows (`bit-and`/`bit-or`/`bit-xor`/`bit-not`/`shl`/`shr`,
  optionally `popcount`). (2) `/backend` lowers each 1:1 to its CLIF op (`band`/`bor`/`bxor`/
  `bnot`/`ishl`/`ushr`|`sshr`/`popcnt`) — near-trivial. (3) `/stdlib` curates `num/bits.cl`
  with Clojure-aligned names over the primitives. (4) `/qa` tests each op.
- **Owner(s):** `/arch`/`/spec` (semantics — the gate), `/backend` (lowering), `/stdlib`
  (wrappers), `/qa` (tests). Cross-crate but each step is small.
- **Size:** **M.** The spec ruling + 6–7 trivial CLIF lowerings + a wrapper module + tests.
  The codegen is "near-trivial 1:1"; the spec decision (shift semantics, Int width) is the
  thinking.
- **Dependencies / ordering:** `/spec` semantics ruling first, then `/backend`, then
  `/stdlib`. **0408 soft-depends on this** (the bitmask grid representation), so if both
  clear, 0416 lands before 0408's representation fix.
- **Risk:** **Low-medium.** Codegen risk is low (direct CLIF ops). The risk is *scope
  creep* in the spec decision (signed/unsigned shift, overflow, Int width) and that this
  is a **new permanent primitive surface** — once shipped it cannot be casually removed.
- **Verification:** `/qa` positive+negative tests per op (no repro exists; it's a
  missing-feature gap, correctly a FIXME not a failing test).
- **Recommendation:** **Clear-now-feasible IF the user wants the feature.** It is a real,
  recurring application-domain gap (flags, sets-as-masks, hashing), not Sudoku-specific.
  But it is a **feature addition** (new primitives), so it is "build a feature" not "close
  debt" — smaller than 0407/0408 (codegen trivial) but still a permanent-surface commitment
  requiring a spec ruling. The synthesis (B16) rates it **NO for must-fix-before-Phase-H**
  (forward-flow feature). **Clear it only as a deliberate feature decision, not a sweep.**

### 0417 — /arch — vec RC-model alignment (PAIRED-OR-UAF)

- **Kind:** A (debt-closure / single-source-of-truth refactor of correct-but-divergent
  code). The synthesis ranks this **#1 by leverage×hazard** and **lean must-fix-before-Phase-H**.
- **What it takes:** Make vec-set match vec-push (fully-symmetric RC design): (1) hoist the
  consuming inc up-front in `compile_vec_set` (gated by `element_consuming_inc`, like
  vec-push); (2) **stop** `vec_set_copy` inc'ing `val` at `vec_runtime.rs:220` (drop the
  `call_elem_fn(elem_inc_fn, val)`; the *retained*-element inc is unchanged); (3) **delete**
  `emit_vec_set_copy_temp_compensation` (`vec_codegen.rs:404-456`). Removes a runtime
  branch + a codegen helper + the only labor-split divergence.
- **Owner(s):** `/arch` dispatches a **paired** `/dev` backend + `/dev` intrinsics change
  as **one change-set** (do NOT split). Consider co-scheduling the **DEF-2 `conj` repro
  fix** (same root cause) and re-routing primitives' `str_split`/`str_join` through a
  `vec_runtime` element-store accessor in the same RC pass.
- **Size:** **M.** Two coordinated crate edits + a unit test each side. The DEF-2 co-fix
  adds scope if folded in.
- **Dependencies / ordering:** **PAIRED-OR-UAF** — changing the runtime inc without
  removing the backend compensation (or vice-versa) is a use-after-free regression of
  FIXME 0296. Both crates land together. **Strongly recommend co-scheduling B17/DEF-2**
  (the active `conj` heap-ADT corruption defect — same root cause); fixing the Vec-element
  RC convention once before Phase H is cheaper than twice after.
- **Risk:** **High *if mis-sequenced*** (UAF); **medium if done correctly** (the paired
  change is well-specified with file:line, and the suite is green today so net behaviour is
  pinned). The hazard is the split, not the change.
- **Verification:** Unit test each side (intrinsics: `vec_set_copy` no longer inc's `val`;
  backend: vec-set copy path inc's a Var, transfers a temporary, no compensation). **DEF-2
  has a repro queued for `/qa`** (failing test is its record; it is *not* a separate FIXME).
  The full suite (green today) guards against net-RC regression.
- **Recommendation:** **Clear-now-feasible AND should-clear** — this is the highest-value
  debt item and the synthesis leans it into the Phase-H gate. Do it paired, with the DEF-2
  `conj` fix in the same RC pass. This is the strongest "clear it now" of all 10.

### 0419 — /arch — shared HostCallbacks builder (the 0407 prerequisite)

- **Kind:** A (debt-closure / divergence-proofing of correct-but-hand-mirrored code).
  Synthesis B3 / theme T3.
- **What it takes:** Introduce ONE shared consumer-side `HostCallbacks` builder in the
  lowest crate that can name both intrinsic pointers (`cranelisp-intrinsics`, or a host-side
  `fn host_callbacks() -> HostCallbacks` both call). Both production sites
  (`src/platform.rs:253` JIT/REPL; `cranelisp-exe-bundle/src/lib.rs:131` `--link`) **plus
  the test mirror** (`src/platform.rs:932`) call it. The platform crate stays unchanged (it
  is the correct, dependency-clean contract definition; it must NOT depend on intrinsics —
  Principle 3 DAG). Removes the 10-line cross-file "this-makes-the-`--link`-path-match"
  comment that is itself the tell.
- **Owner(s):** `/arch` decides the builder's home + ABI surface; `/dev` int + `/dev`
  backend implement. Cross-crate (consumer-side).
- **Size:** **M.** A builder fn + repoint 3 call sites; `public-api.txt` regen if the
  builder is a public surface.
- **Dependencies / ordering:** None upstream. **It is the prerequisite for 0407** — the
  synthesis is explicit: do NOT widen `HostCallbacks` for 0407 (3 fields × 2 sites) before
  this builder lands. So **0419 → 0407** if both clear.
- **Risk:** **Low-medium.** Consumer-side refactor of code that already agrees (DEF-6 is
  fixed); the change makes the agreement structural. Low behavioural risk; the only care is
  the builder's crate home (DAG-clean) and the `public-api.txt` discipline.
- **Verification:** The existing host-callback tests + the test mirror now routing through
  the builder; a `/dev` unit test that both modes construct identical callbacks. No new
  defect repro needed (DEF-6 already has its history).
- **Recommendation:** **Clear-now-feasible.** Low-cost divergence-proofing that closes the
  DEF-6 root enabler. **Phase-H gate disposition is conditional** (synthesis: gate-in iff
  0407 is on the near roadmap; otherwise deferrable bucket-ii). But for a "clear everything"
  goal it is cheap and worth doing **regardless** — and doing it unblocks 0407 cleanly if
  the user later wants Model B. Do it.

### 0420 — /arch — FQ Type-rendering consolidation (5 walks → 1)

- **Kind:** A (debt-closure / duplication consolidation of correct-as-shipped code).
  Synthesis B4 / theme T1; the headline **recurrence** escalation.
- **What it takes:** Introduce ONE parameterized `Type` walk in `cranelisp-types::types`
  taking a small config (`primitive_naming: Bare|Qualified`, `var_naming:
  Numbered|Lettered(&var_names)`, optional constraint map). Repoint the sites:
  `impl Display` (#1) → Bare+Numbered; `format_type_fq` (#3, typecheck) → Qualified+Numbered
  (the cross-crate re-impl disappears); `display.rs` #4/#5 → Qualified+Lettered; **delete**
  dead `format_type_display`/`format_type_with_vars` (#2); no-impl renderers (#6) → consume
  the unified walk with Qualified (fixes the half-FQ `(no impl of Eq for Color)` message →
  `user/Color`) **without** changing `concrete_type_name` itself (its mangled-name call
  sites need the bare name). **Keep** `type_var_names` (live).
- **Owner(s):** `/arch` (owns `Type`) authors the walk + config in `cranelisp-types`;
  `/dev` typecheck + `/dev` src/ re-point callers; `/qa` owes a narrow repro for the no-impl
  FQ fix (two same-named ADTs in different modules, missing impl, assert the FQ name appears).
- **Size:** **M.** One new walk + 5–6 caller repoints across 3 crates + dead-export
  retirement + `public-api.txt` regen (the baseline-diff discipline) + one `/qa` repro.
- **Dependencies / ordering:** Ships with `public-api.txt` regen per the baseline-diff
  discipline. No hard upstream dep. (T5 dead-export retirement folds into this change-set.)
- **Risk:** **Low.** Correct-as-shipped today; the only behavioural change is the
  intended no-impl FQ-message fix. The "keep-distinct" advisory survives at the *output*
  level (conventions become config values, not copies). Mechanical-but-broad.
- **Verification:** `/qa` narrow repro for the no-impl FQ message (red-first, flips green);
  the existing type-display tests guard the unchanged conventions; `public-api.txt` diff is
  the surface guard.
- **Recommendation:** **Clear-now-feasible.** Synthesis rates it **high-value-but-deferrable,
  NOT must-fix-before-Phase-H** (correct as shipped). But the escalation warning is "do not
  deepen it further" — every new type-name-into-message site adds the Nth copy. For a
  "clear everything" goal it is a clean M-size consolidation that also fixes a real (if
  minor) half-FQ message bug. Do it; it pairs naturally with any typecheck/src work.

---

## 2. Summary table

| FIXME | Owner | Kind | Size | Hard dep / ordering | Risk | Has repro? | Clear-now? |
|---|---|---|---|---|---|---|---|
| **0406** | /int | A debt | S | none | Low | yes (retarget) | **YES** |
| **0407** | /arch+platform+intrinsics | **C feature** | L | **after 0419**; fork-join ferry | **High** | no (e2e=build) | **STAY** (build-or-retract) |
| **0408** | /port | **C feature** | L | soft: 0416 + Phase-H Tier-2 | Med-high | no (e2e=build) | **STAY** (Phase-H-adjacent) |
| **0409** | /repl | A debt | S | none | Low | repl-harness | **YES** |
| **0410** | /repl→/spec→/int | **B ruling** | M | **§8.11.4 ruling first** | Med (footgun) | unit+e2e | **YES, serialized** |
| **0415** | /repl→/qa(→/int) | A debt | S–M | normativity call first | Low-med | tests-first | **YES** |
| **0416** | /spec→/backend→/stdlib | **B feature** | M | spec ruling first; 0408 soft-deps it | Low-med | no (feature) | **YES if feature wanted** |
| **0417** | /arch→backend+intrinsics | A debt | M | **PAIRED-OR-UAF**; co-fix DEF-2 | High-if-split | DEF-2 repro queued | **YES (top pick)** |
| **0419** | /arch→int+backend | A debt | M | unblocks 0407 | Low-med | host-cb tests | **YES** |
| **0420** | /arch→typecheck+src | A debt | M | public-api regen | Low | /qa repro owed | **YES** |

**Rough totals if all clear:** 2×S (0406, 0409) + 1×S–M (0415) + 5×M (0410, 0416, 0417,
0419, 0420) + 2×L (0407, 0408). The two L's are the feature-builds (0407, 0408) and carry
the bulk of the risk and time.

---

## 3. Clear-all plan (zero non-Phase-H carries)

If the user wants ZERO non-Phase-H FIXMEs, here is a realistic serialized plan. **Recall
the single-agent-at-a-time constraint for source-touching work** (worktree isolation is
broken on this project) — so the "parallel" notes below mean *independent enough to batch
across sessions/skills*, not literally-concurrent source edits.

### Wave 1 — the cheap, independent debt (clear first; high confidence)
Serial source edits, but each is self-contained:
- **0417** (vec RC-model, PAIRED, co-fix DEF-2) — **do this FIRST**; it is the
  highest-value item and the synthesis leans it into the Phase-H gate. Paired backend +
  intrinsics, one change-set, unit test each side, fold in DEF-2 `conj`.
- **0406** (friendly `--link` rejection) — S, int-only, retarget the existing repro.
- **0420** (FQ Type-rendering consolidation) — M, `cranelisp-types` + repoints + public-api
  regen + the no-impl FQ repro.
- **0419** (shared `HostCallbacks` builder) — M, consumer-side; **lands before any 0407
  work**.

These four are all kind-A debt, low/medium risk, no upstream design dependency. ~1×M-heavy
+ 1×S each. Call it **~3 working days** of `/dev` time across the four (0417 and 0420 are
the meat).

### Wave 2 — the `/repl` + `/spec`-gated debt (decisions then small impl)
- **0409** (number the demos) — S, `/repl`-only, no dependency. Can land anytime; group
  here.
- **0415** (symbol-layout normativity + coverage) — `/repl` normativity call → `/qa`
  tests; S–M. Writing the tests reveals whether a latent `/int` formatter divergence
  exists (adds M if so).
- **0410** (Cranelisp.toml scaffold) — **gated on the `/spec §8.11.4` ruling**. Get the
  ruling (recommend resolution-1: absent-key ≡ fall-through, verify serde), then `/repl`
  experience, then `/int` impl + tests. ~1 day if the ruling is quick.

~**1.5–2 days**, fronted by two small design rulings (`/repl` normativity, `/spec`
§8.11.4).

### Wave 3 — the feature-builds (these are NOT debt cleanup — flag to user)
- **0416** (bitwise intrinsics) — **B/feature**, M. `/spec` semantics ruling (shift
  behaviour, Int width) → `/backend` 1:1 CLIF lowering → `/stdlib` `num/bits.cl` → `/qa`.
  A real recurring-domain feature; clear only as a deliberate feature decision. **Land
  before 0408** if 0408 will use the bitmask representation.
- **0408** (Sudoku parallel-search + perf) — **C/feature**, L. Best coordinated with the
  **Phase-H Tier-2 backend** (its own FIXME says perf numbers belong on a release build).
  Soft-depends on 0416. Downstream-refreshes 0409's `sudoku.demo`.
- **0407** (Model-B closure-callback) — **C/feature**, L, **after 0419**. ABI v3→v4, new
  cross-FFI RC + threading + error-slot-ferry contract. The highest-risk item.

~**multi-day each** (L). This wave is where "clear everything" stops being cleanup and
becomes a feature-roadmap commitment.

### Critical caveats — items unwise to force-clear as "debt"

1. **0407 (Model-B) — debt-closure ≠ feature-build.** Clearing it means *building a new
   ABI-bumping capability* for a teaching demo (Model A already serves the full showcase).
   The honest options are **(a) build it** (0419→0407, multi-day, ABI v4, high risk,
   carries the fork-join error-slot ferry obligation) or **(b) formally retract Model B
   from the roadmap and delete the FIXME with a rationale** — NOT "tidy it up." If the user
   wants zero carries, push for option (b) unless Model B concurrency is genuinely wanted.

2. **0408 (Sudoku rework) — natural home is the Phase-H arc, not a debt sweep.** Landing
   perf numbers against the debug backend now wastes measurement the Tier-2 release build
   will invalidate. Schedule it *with* Phase H, not before.

3. **0416 (bitwise) — a permanent new primitive surface.** Cheap codegen, but a spec
   ruling and a forever-API-commitment. Clear it as a feature decision, not reflexively.

4. **0417 (vec RC) — PAIRED-OR-UAF.** The one item where mis-sequencing *introduces* a
   use-after-free. Must land as a single change-set; never split the two crates.

5. **0410 (scaffold) — footgun behind a spec ruling.** Do not let `/int` write the
   scaffold before §8.11.4 is settled; a naive `lib-dirs = []` silently breaks prelude
   resolution.

### The realistic recommendation to the gate

- **Clear now, cleanly (6 items, ~kind A + the 2 ruling-gated A/B):** 0406, 0409, 0415,
  0417, 0419, 0420 — and 0410 once its §8.11.4 ruling lands. This is genuine debt-closure
  and divergence-proofing, mostly M/S, low-to-medium risk. **This is the "we don't carry
  debt" win.** ~1 sprint of serialized `/dev` + a couple of small rulings.
- **Treat as feature decisions, not carries to "clear" (3 items):** 0416 (build-the-feature
  or accept-the-gap), 0408 (Phase-H-adjacent showcase), 0407 (build-or-retract Model B).
  Forcing these to "clear" is committing multi-day feature engineering (and an ABI bump for
  0407). **If the user insists on literal zero carries, the cleanest disposition for 0407
  is retract-with-rationale; 0408 folds into Phase H; 0416 is a yes/no feature call.**

**Net:** zero *debt* carries is achievable in roughly one sprint (Waves 1–2). Zero *FIXME*
carries additionally requires building/retracting two-to-three features (Wave 3), which is
a roadmap decision the user should make consciously — that is the debt-vs-feature line this
assessment exists to draw.
