# Slice 4 — `21-hello-io.cl` investigation

**Sprint 61 Wave 4, steps 4a+4b — REDUCTION + EVIDENCE CAPTURE.**
Author: `/backend`. Captured SHA `776a6cf`, 2026-04-22.

Scope of this doc: record the evidence collected, name candidate
hypotheses, implicate specific code sites. Per SPRINT.md §Wave 4
ordering, `/arch` at step 4c picks the hypothesis; `/qa` authors
hypothesis-specific tests; the assigned owner (probably `/backend` on
current evidence) implements the fix at step 4e.

## Failure surface

The four affected tests:

| Test                                                                                            | Status |
|-------------------------------------------------------------------------------------------------|--------|
| `examples_run::every_example_file_runs_under_examples_prelude`                                  | Accepts `21-hello-io.cl` exit in `[101, 133, 141]` — all three are SIGABRT/panic signatures per the S60 ledger, so the test *passes* only because it accepts the bug's visible faces as "OK". The accepted-exit table masks the defect. |
| `sprint61_observability_io::io_trace_hello_io_emits_full_trampoline_sequence`                   | FAILS — asserts a matched `TrampolineEnter ... TrampolineExit` pair; the process panics between. |
| `sprint61_observability_io::io_trace_hello_io_observes_core_sequential_event_types`             | FAILS — asserts taxonomy coverage; panic truncates the stream before taxonomy completes. |
| `sprint61_observability_io::io_trace_platformeffect_carries_scheduling_class_byte`              | FAILS — panic fires before any `PlatformEffect` event can be emitted because the crash-minimum doesn't depend on platform IO at all (see reduction). |

## Reduction narrative (step 4a)

### Failure rate — no concurrency dependency

Standalone loops (5 rounds × 6 concurrent procs = 30) give:

    code 133 (SIGTRAP)  22 / 30  73%
    code 201 (i32 trunc of abort)  4 / 30  13%
    code 101 (clean panic)  4 / 30  13%

The three exit codes are surface variants of one underlying bug
(different outcomes of stderr/panic-hook sequencing during the
`abort`/`panic_fmt` path, not distinct root causes). Running standalone
without concurrency gives the same distribution; concurrent pressure
does not change the rate materially. **H(4-3) nextest crosstalk is
ruled out — no concurrency shape reproduces anything different from
isolation.**

### Source-level reduction — 7-line repro, 100% crash

Shrinking `21-hello-io.cl` yielded the minimum trigger
(`tests/sprint61/race-evidence/21-hello-io-failing-min-776a6cf.log`):

    (import [primitives [Pure bind]])

    (defn then [a b]
      (bind a (fn [_] b)))

    (defn test-then []
      (bind (then (Pure 999) (Pure 42))
        (fn [x] (Pure (add-i64 x 8)))))

    (defn main []
      (bind (Pure 1) (fn [r1]
        (bind (test-then) (fn [r2]
          (Pure (add-i64 r1 r2)))))))

Four removals that ALL restore clean runs:

- Drop `(bind (Pure 1) (fn [r1] ...))` outer wrapper around `test-then`.
- Drop `(bind (test-then) (fn [r2] ...))` and just `(test-then)` directly.
- Inline `then` so no user fn constructs a Bind with a captured IO param.
- Replace `then` with a 2-arg fn body that doesn't construct a Bind
  (e.g. `(defn pick-io [a b] a)`).

The **necessary conjunction** is:

1. A user-defined function that constructs `(bind x (fn [_] captured-IO))`
   — i.e. a `then`-like combinator.
2. A call to that function inside an outer `bind`'s continuation.
3. An outer trampoline step that reaches a second `BindEnter` INSIDE the
   freshly-produced subtree.

Platform IO (Part 7 of the example) is **not** required. The 8-test
variant (parts 1-6 only, tests 7 and 8 being `test-conditional-io` +
`test-then`) reproduces at ≥95% rate; the 11-test variant reproduces at
100%.

### What rules out H(4-2) and H(4-3)

- **H(4-2) stdio DLL buffer ordering**: ruled out. Minimum repro does
  not import `[platform.stdio [print]]` or call `print`. The stdio
  platform is not on the stack trace. 100%-reproducing minimum has
  **no IO Effect node** of any kind — only Pure + Bind.
- **H(4-3) nextest subprocess-environment crosstalk**: ruled out.
  Standalone and 6-way concurrent have the same failure distribution;
  `--test-threads=N` does not influence the rate. The bug is
  deterministic on the failing source.

### What supports H(4-1)

The IO-trace tail from the minimum repro:

    [IO] ts=17583 BindEnter inner=0xb0f01d530 cont=0xb0f01d680 fresh=true
    [IO] ts=17667 ContPush  cont=0xb0f01d680 fresh=true depth=1
    [IO] ts=18625 BindEnter inner=0xb0f01d440 cont=0xb0f0acf40 fresh=true
    [IO] ts=18667 ContPush  cont=0xb0f0acf40 fresh=true depth=2
    [IO] ts=19125 BindEnter inner=0xb0f0acfc0 cont=0xb0f01d470 fresh=true
    [IO] ts=19208 ContPush  cont=0xb0f01d470 fresh=true depth=3
    [IO] ts=19292 PureStep  value=999 fresh=true
    [IO] ts=19375 ContPop   cont=0xb0f01d470 fresh=true depth=2
    [IO] ts=20583 BindExit  new_current=0xb0f0acf60     <-- points at garbage

    panicked: cranelisp_run_io: unknown IO tag 6578533

The closure invoked is `(fn [_] b)` where `b` is the Pure-42 parameter
from `then`'s second argument. Its body returns `b` directly — but the
`BindExit new_current=0xb0f0acf60` is neither the Pure-42 node
(`0xb0f01d440`, seen earlier as `inner`) nor any other previously-
tracked IO node. It lies in the `0xb0f0acxxx` region adjacent to
`cont=0xb0f0acf40`. 6578533 = 0x6457E5 has the magnitude of a JIT
code-relocation offset.

**Interpretation**: either (a) the closure body's compiled code returns
the wrong pointer value when loading the captured parameter, or (b) the
captured Pure-42 node has been freed/clobbered by the trampoline's
`dec_shallow_io` logic before the continuation accesses it.

## Code sites implicated

Primary (H(4-1) candidates):

- `crates/cranelisp-runtime/src/io.rs:92-329` (`run_io_trampoline_inner`)
  — specifically the `current_is_fresh` state-machine and the
  `if current_is_fresh { crate::drop::dec_shallow_io(current); }`
  shortcut that fires on Pure/Effect/Bind arms (lines 136-138, 151-153,
  197-199, 209-211, 240-244, 307-308, 319-320).
- `crates/cranelisp-runtime/src/io.rs:345-356` (`call_continuation`)
  — the `if cont_is_fresh { consume_closure(cont_ptr); }` after
  invocation. If `cont_is_fresh=true` but the closure captures an IO
  node, `consume_closure` may be transitively walking the captures via
  the drop-glue pointer, freeing the captured IO node, which the
  outer trampoline then reads as `new_current`. This matches the
  observed `0xb0f0acf60 = unknown-tag` pattern.
- `crates/cranelisp-backend/` closure drop-glue generation for
  continuations that capture IO nodes. If the drop-glue emitted by
  `compile_fn_lambda` (or the defn that lowers to it) for `(fn [_] b)`
  includes a dec for the captured `b` on the same step that the
  trampoline already consumed `b` via the Pure `current_is_fresh` dec,
  we get a double-free.

Secondary (feasibility checks):

- `cranelisp_run_io` (io.rs:51-61) — the top-level `consume_io_tree`
  dec at return time. Not on the failure path (we panic before
  `run_io_trampoline` returns).
- The IO-AST construction in `crates/cranelisp-backend/src/compile/`
  — does the Bind node allocated by `then`'s body correctly inc the
  captured `b` parameter when it's stored into field1 of the Bind?

## Hypothesis candidates

Weights are this agent's best reading of the evidence; the design
discipline is that /arch at step 4c makes the final assignment.

| Hypothesis  | Supporting evidence                                            | Weight |
|-------------|----------------------------------------------------------------|-------:|
| H(4-1) trampoline continuation-state leak (fresh-Bind closure over captured IO param is double-free'd) | Minimum repro deterministic, 100% rate, no platform IO, no concurrency; panic reads stale memory at a `cont`-adjacent address; exactly the code-shape the `current_is_fresh` + `call_continuation` + `consume_closure` chain was introduced to handle (S57 Wave 3 per `design/backend/ring2-rc.md §3.5`). | **0.85** |
| H(4-2) stdio DLL buffer ordering under concurrent subprocess loads | Minimum repro has no platform IO. 100% rate with zero concurrent pressure. | 0.00 |
| H(4-3) nextest-level subprocess-environment crosstalk              | Standalone reproduces at same rate as concurrent; minimum repro deterministic. | 0.00 |
| H(4-1')  variant: closure drop-glue (backend-emitted) dec's the captured IO param before the trampoline steps through it | Same surface as H(4-1) but the root cause is backend-side, not runtime-side. Observably indistinguishable from H(4-1) at the trace level. | 0.15 |

Summed weight above 1.0 reflects that H(4-1) and H(4-1') are not
mutually exclusive — the fix may touch both the trampoline logic AND
the closure drop-glue emission. /arch adjudication should clarify
which one owns the fix and whether the test coverage needs to exercise
both paths.

## Fix-plan outlines (step 4d input)

**If H(4-1) holds (runtime)**:

- Option A: Track captured-IO-node references on fresh Bind continuations
  explicitly. Before `consume_closure(cont_ptr)` in `call_continuation`,
  walk the closure's captures and **detach** any IO-node captures that
  are still live in the trampoline's `current`/`cont_stack` frontier.
- Option B: Refactor the `current_is_fresh` protocol so the
  trampoline's fresh-dec and the closure's capture-dec don't both fire
  on the same Pure parameter. Candidates: inc the captured IO node
  on Bind construction (backend-side) so its rc is 2 when
  `consume_closure` dec's it, leaving rc=1 for the trampoline to
  consume on its next step.

**If H(4-1') holds (backend drop-glue)**:

- Audit the drop-glue emitted for closures that capture heap
  parameters. For a `(fn [x] b)` body where `b` is a heap parameter,
  the drop glue should NOT dec `b` if the closure's body has already
  transferred ownership of `b` out (last-use transfer — the body's
  return value is `b` itself).
- Related: check `sketch/src/codegen.rs` `borrowed_vars` / last-use
  analysis for parameter-return cases. The sketch may handle this via
  "return-value auto-upgrades borrowed to transferred" logic (see
  `sketch/docs/codegen.md` §"Scope cleanup").

## Sketch comparison

The sketch's trampoline (`sketch/src/runtime/io.rs` — confirm path at
implementation time) predates the Wave-3 RC fix described in
`design/backend/ring2-rc.md §3.5` and does not distinguish
`current_is_fresh` from caller-tree ownership. It relied on
`consume_io_tree` at the top level to walk the entire tree and release
everything. That design has a different failure mode (O(N) RC leak on
long bind chains, documented in the same file §3.5.1) but not the
type-confusion we see here.

The reimplementation's `current_is_fresh` protocol was introduced to
fix the leak but appears to have introduced this new bug. The design
principle (inline-dec fresh-produced nodes so memory doesn't grow)
is correct; the problem is that a captured IO parameter inside a
continuation closure can be reachable via BOTH the trampoline's
`current` frontier AND the closure's drop glue, and the current code
doesn't coordinate.

## Ownership recommendation

**`/backend`** on current evidence. The implicated code site is
`crates/cranelisp-runtime/src/io.rs` (runtime) + possibly
`crates/cranelisp-backend/src/compile/` (drop-glue emission). Both are
within `/backend`'s remit. If /arch at step 4d determines the fix
requires changes to the backend's closure-drop-glue emission, `/backend`
still owns it. Neither `/platform` (no platform IO involved) nor `/qa`
(not a test-authoring issue) is implicated.

## Readiness for /arch step 4c/4d

- Evidence dumps: `tests/sprint61/race-evidence/21-hello-io-failing-776a6cf.log`,
  `21-hello-io-failing-min-776a6cf.log`, `21-hello-io-passing-776a6cf.log`,
  `21-hello-io-README.md`.
- Minimum repro: 7-source-line program, 100% crash rate, no concurrency,
  no platform IO.
- Implicated sites: listed above with line-number ranges.
- Hypothesis-weighted disposition: 85% H(4-1), 15% H(4-1') backend-drop-glue
  variant. H(4-2) and H(4-3) ruled out.
- Open questions for /arch:
  1. Is the fix runtime-side (detach captures before consume_closure) or
     backend-side (drop-glue emission for parameter-captured-then-returned)?
  2. Does the post-fix trampoline need a new invariant in
     `design/backend/ring2-rc.md §3.5` about closure-capture-vs-current
     reachability?
  3. Should `/qa` author the regression test using the 7-line minimum
     repro (small, spec-traceable) or the 8-test reduced main (closer
     to real usage)?

Fix is NOT attempted in this doc — /arch adjudicates at step 4d, fix
lands at step 4e.

## 4d. /arch mini-review verdict (Slice 4 closure hypothesis)

**Reviewer**: /arch
**Date**: 2026-04-22
**Verdict**: APPROVE WITH REVISIONS. H(4-1)/H(4-1') split re-cast as
H(4-1'') — both sides contribute; the fix must coordinate them. Step 4e
is GO contingent on adopting a single coherent rule (below) rather than
an option-A/option-B point fix on one side only.

### Hypothesis discrimination

Confidence split is directionally right but the naming was too clean.
H(4-2) and H(4-3) are correctly eliminated — the 100% deterministic
standalone repro with no platform IO and no concurrency pressure rules
them out decisively. Within the remaining 1.0 of weight, /backend's
0.85/0.15 between H(4-1) and H(4-1') presumes they are alternatives.
Walking the minimal trace against `io.rs:136-353` and
`control_flow.rs:812-1056` shows they are **composed**, not alternative:

1. Trampoline-side (§H(4-1)): `call_continuation` invokes the closure,
   the closure returns `b` (= the captured Pure(42)). The closure body
   emits NO protective inc on the returned capture because
   `protect_return_value` (mod.rs:1134-1176) gates on
   `has_cleanup_targets` — which examines `scope_stack` only.
   Captures are not on `scope_stack` (control_flow.rs:961-963 is
   explicit about this). The param `_` is Int, so `has_cleanup_targets`
   is false. `b` flows out at the rc it had going in.

2. Drop-glue-side (§H(4-1')): `consume_closure` then fires because
   `cont_is_fresh=true`, and the embedded drop-glue dec's the closure's
   one ref to `b`. If `b`'s rc was exactly 1 at that moment (the common
   case — the capture-inc happened at closure construction, `b`'s
   original caller-ref has been dec'd at `then`'s scope exit), the dec
   reaches 0 and frees the node the trampoline is about to read.

Both arms fire; removing either alone would close the bug (inc in the
closure body on the returned capture; or teach the trampoline not to
dec captures still reachable via the returned tree). The trace cannot
distinguish them — it is blind to whether the inc is missing on the
return path or whether the dec is firing on a still-live node.

### H(4-1) vs H(4-1') ruling

**H(4-1'') — coordinated defect; fix belongs on the backend side.**
Rationale:

- The trampoline's `current_is_fresh` + `consume_closure(cont_ptr)`
  protocol is internally consistent: a fresh closure owns its
  captures, so dec'ing it releases them. That invariant is how O(N)
  leaks on long bind chains were closed in §3.5. Changing the
  trampoline to "detach captures before consume" (Option A from §Fix
  plans) would weaken that invariant for the narrow case where a
  capture happens to be the returned value, and would require the
  trampoline to introspect the closure's capture layout, which it
  currently does not — layout is backend-owned. This is the wrong
  boundary to cross.
- The closure body DOES know, at codegen time, when its return
  expression is a bare `Var(b)` where `b` is in `captured_vars`. That
  is exactly the site where an inc-on-return must be emitted to
  balance the drop-glue's upcoming dec. The fix is Option B from §Fix
  plans, relocated to the backend: `protect_return_value` (or an
  explicit capture-return path inside `compile_lambda_body` before
  `pop_scope_with_cleanup`) must inc the return value when the
  inferred return type is heap-typed AND the returned expression
  resolves to a captured variable. Today `protect_return_value`
  refuses to inc when `has_cleanup_targets` is false, but the gate is
  wrong for this case: captures are NOT on scope_stack but the
  drop-glue IS going to dec them after the body returns.

The owner is `/backend` on both counts. No runtime-side edits to
`io.rs` are required; the `consume_closure` + `current_is_fresh`
protocol stays as specified.

### Fix surface soundness

Interface-internal per Principle 3. No boundary-type change; no
`cranelisp-types` change; no `design/arch/interfaces.md` change.

- Primary edit: `crates/cranelisp-backend/src/compiler/control_flow.rs`
  `compile_lambda_body` return path OR
  `crates/cranelisp-backend/src/compiler/mod.rs` `protect_return_value`
  gate. /backend picks the cleaner site — /arch's preference is a new
  explicit helper (`emit_capture_return_inc`) called from
  `compile_lambda_body` so `protect_return_value`'s
  scope-stack-bound logic stays coherent for all its other callers.
- No edit in `io.rs`. Do not weaken `consume_closure`.

### Interaction with ring2-rc.md §5.5

This is a NEW rule adjacent to §5.5's borrowed_vars discipline, not a
case under it. §5.5 covers three ownership categories that gate
last-use transfer (captured, borrowed, regular). The new rule covers
**capture-flow-through-return**: when a closure body's return value is
a captured heap variable, the body must emit `rc_inc` on that value to
balance the drop-glue dec that runs when the closure's one-shot
lifetime ends.

/arch flags ring2-rc.md §5.5 for an additive bullet (FIXME to
`/backend` below). The new bullet should read (approximately):

> - **Capture-return inc (new; Slice 4)**: When a lambda body's return
>   expression resolves to a captured variable of heap type, the body
>   MUST emit `rc_inc` on the returned value before `return`. The
>   closure's drop glue will later dec the captured value; without
>   this inc, the returned value is freed before the caller can
>   read it. The `protect_return_value` gate on `scope_stack` does
>   not cover this case because captures are not on the scope stack.

`/backend` owns the ring2-rc.md edit. `/arch` does not touch it
directly per skill ownership; the FIXME at §5.5 will carry the
language above as the requested additive rule.

### Test authoring (step 4f) requirements

Two tests, both authored by `/qa` per cross-skill defect protocol:

1. **Integration test (Layer 3)** — the 7-line minimum repro. Path:
   `tests/integration/ring4_io.rs` or the nearest ring-4 IO file.
   Compiles the 7-line source, runs it under `compile_unit`, asserts
   result == 50 (= 1 + (999+8 → 1007? no — the test returns
   `r1 + r2` where r1=1 and r2=(test-then)=50). Asserts no panic,
   no SIGTRAP, RC balanced. `// spec: spec/10-io.md §X` — /qa picks
   the exact section. This is the regression guard.

2. **Unit test (backend crate)** — owned by `/backend`, not `/qa`.
   Inside `crates/cranelisp-backend/src/compiler/control_flow.rs`
   `#[cfg(test)]` mod, a test that builds an AST for `(fn [_] b)`
   where `b` is a capture of a heap type, compiles it, and inspects
   the generated CLIF to verify the inc-on-return is present. This
   prevents the fix from regressing via a `protect_return_value` gate
   change elsewhere.

Naming: `io_trampoline_then_combinator_does_not_double_free_capture`
(integration), `lambda_return_captured_heap_var_emits_inc` (unit).

The 8-test reduced main is NOT required as a second test — it reduces
to the same root cause, and the minimum repro is strictly stronger as
a regression surface. The 11-test full `21-hello-io.cl` is the E2E
gate (Layer 4); it passes implicitly when the minimum repro passes.

### Step 4e readiness

**GO.** Adopt the H(4-1'') ruling: backend-side inc-on-return for
captured heap values. Do not edit `io.rs`. /backend implements fix at
step 4e against the helper-in-control_flow.rs site; /qa authors the
integration test at step 4f; /backend authors the unit test alongside
the implementation (per `feedback_unit_tests_with_dev.md`).

### Recommendations for /sprint

1. Step 4e prompt to /backend must (a) state H(4-1'') (both sides
   contribute; fix is backend-only), (b) name the preferred site
   (explicit `emit_capture_return_inc` helper in control_flow.rs), and
   (c) require a FIXME(/backend) on `design/backend/ring2-rc.md §5.5`
   adding the capture-return bullet — file, don't edit, per skill
   ownership.
2. Do NOT instruct /backend to alter `io.rs`. The runtime protocol is
   correct as specified.
3. Wave gate: step 4e closes only when both tests (integration +
   unit) exist and pass. Do not close on "integration test passes,
   unit deferred" — the unit is the structural regression guard.
4. The three `sprint61_observability_io::*` tests should clear
   automatically once the panic goes away; /qa confirms at step 4g
   without further work.
5. The `examples_run::*` accepted-exit tolerance for `21-hello-io.cl`
   (exits 101/133/141) should be tightened to exit=0 post-fix. File
   FIXME(/qa) during step 4f.

## 4e. Fix implementation notes

**Author**: `/backend`. **Date**: 2026-04-21. **Verdict executed**: H(4-1'') backend-only.

**Mechanism.** `compile_lambda_body` (`crates/cranelisp-backend/src/compiler/control_flow.rs`) emits closure-body IR. Its prior contract sequenced: `compile_expr(body)` → `protect_return_value` → `pop_scope_with_cleanup`. `protect_return_value`'s inc-on-return only fires when `scope_stack.last()` has heap-typed cleanup targets — but captures are deliberately excluded from `scope_stack` (they are released by the closure env's drop-glue, not the body scope). For a body shape `Expr::Var { name: b }` where `b` is in `captured_vars` and non-heap params are the only scope entries, no inc was emitted. The drop-glue built by `build_closure_drop_glue` then dec'd the capture after the body returned, freeing the value at the pointer the caller still held.

**Fix site.** New helper `emit_capture_return_inc(&mut self, body, result)` added in `control_flow.rs` just above `compile_lambda_body`. Invoked from `compile_lambda_body` between `protect_return_value` and `pop_scope_with_cleanup`. It emits `rc_inc` (or `rc_inc_guarded` for `Mixed`) when and only when `body` is an `Expr::Var` naming a heap-typed capture. `protect_return_value` is unchanged; its `scope_stack` discipline stays correct for all other return shapes. The helper is therefore additive — the set of programs for which inc-on-return fires strictly grows; no prior inc disappears.

**Unit test.** `cranelisp-backend::tests::lambda_return_captured_heap_var_emits_inc` in `crates/cranelisp-backend/src/lib.rs` (sits in the existing `#[cfg(test)] mod tests` alongside `test_compile_lambda_closure`; `control_flow.rs` has no tests module and the `test_compile_and_run` helper is private to `lib.rs`). Shape: `(let [s "hello"] ((fn [_] s) 0))`. Runs the full backend pipeline through the JIT and asserts (i) the returned pointer round-trips through `read_string_as_str` as `"hello"`, (ii) the allocation is still tracked by `LIVE_ALLOCS::is_live` after return. Verified to fail without the fix (by temporarily disabling the helper call site) with the exact `LIVE_ALLOCS` assertion.

**Integration acceptance.**
- 7-line minimum repro (`/tmp/slice4-repro.cl` shape from §Reduction narrative, with `primitives/add-i64` added for the bare-REPL environment): 10/10 runs exit=51 (= 1 + 50), no panic, no SIGTRAP.
- `cargo nextest run --test sprint61_observability_io`: 7/7 pass (3 were failing pre-fix).
- `cargo nextest run --test examples_run`: `every_example_file_runs_under_examples_prelude` passes after tightening the 21-hello-io accepted-exit list from `[101, 133, 141]` to `[243]` (the direct-invocation value 499 & 0xFF; 21 does not read stdin, so 133/141 were crash artefacts not harness artefacts).
- `cargo nextest run -p cranelisp-backend`: 175/175 pass (was 174/174 — the new unit test is the +1).
- `cargo check --workspace`: clean.
- `cargo clippy -p cranelisp-backend --all-targets`: zero new warnings (pre-existing unrelated warnings unchanged).

**Post-fix trace.** `tests/sprint61/race-evidence/21-hello-io-post-fix-776a6cf.log` (23 lines) captures the minimum-repro trampoline sequence: `TrampolineEnter → BindEnter/ContPush ×3 (nested) → PureStep 999 → ContPop → BindExit/PureStep 42 (the returned capture, now live) → ContPop → BindExit/PureStep 50 → ContPop → PureStep 51 → TrampolineExit result=51`. Balanced Bind/Cont/Enter/Exit pairs, clean termination.

**Normative update.** `design/backend/ring2-rc.md §5.6 Capture-return inc` — new rule, sibling to §5.5's borrowed_vars rule, documenting the invariant and pointing back to this investigation doc.

**Open items.** None in this slice. /qa authors the Layer 3 integration test at step 4f using the minimum repro; /review closes Wave 4 at step 4g.
