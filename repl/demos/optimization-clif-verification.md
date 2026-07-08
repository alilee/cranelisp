# S105 Wave-2 — CLIF verification of the optimizer demo

**Author:** `/repl` · **Date:** 2026-07-08 (Phase-5/6 Wave-2) ·
**Demo:** `repl/demos/optimization.demo` (replay: `DEMO_FAST=1 ./repl/showcase optimization`) ·
**Companion to:** `tests/plan/s105-attribution-results.md` (the Wave-1/1b attribution + the
"deeper finding" this demo tests) · **Binary:** `target/debug/cranelisp`, `/clif` on each snippet.

> **Purpose.** The demo's `/clif` captures are the honest verification of the SPRINT
> Wave-1b "deeper finding": *the register win for loop-local aggregates is multi-field
> SSA-decomposition (SROA / value-flattening beyond one word), NOT the stack-slot path;
> multi-field SROA is not built; stack slots are memory, not registers; gate 3 gates the
> stack path out of loops.* Every claim below is read directly off emitted IR. **Verdict:
> the IR CONFIRMS the diagnosis at every point.** One honest divergence from the task's
> Act-1 wish-list is recorded (§Act 1, item 4).

All snippets are free-standing on `(import [primitives [*]])` — bare ops, no prelude
sugar — so each function's IR isolates exactly the optimization under test. Every `/clif`
was also captured in an isolated cwd (fresh `.cranelisp-cache`); the demo player's per-run
chdir gives the same isolation, so the demo shows one function's IR at a time.

## Act 1 — the wins (all confirmed in IR)

| # | Snippet | Optimization | IR verdict |
|---|---|---|---|
| 1 | `sumto` (tail-self-recursive Int accumulator) | loop scalars → SSA/registers | **CONFIRMED.** Loop-carried `n`,`acc` are `block1(v2, v3)` block params; tail is `jump block1(v9, v10)` (back-edge, no call, no frame); zero allocation. |
| 2 | `unwrap` over `(deftype Cell (MkCell [:Int v]))` | single-field value ADT → flattened word | **CONFIRMED.** `(MkCell n)` emits nothing; arg `v1` flows straight to `block2(v1)` → return. No alloc/store/load. (Mechanism: scalar-replacement of a statically-known single-ctor scalar payload — the effective "single-field flatten." Note this is NOT the §7 `HeapCategory::Value` arm, which is still unbuilt; the boundary is field-count 1 — see Act 2 #6.) |
| 3 | `set-first` (`vec-set` on a fresh unique vec) | reuse / mutate-in-place vs COW | **CONFIRMED.** `load v6+8` (refcount) → `icmp eq …, 1` → `brif block2, block3`: block2 stores in place, block3 (`call fn1`) is the copy-on-write fallback. Both arms emitted; runtime picks on rc==1. |
| 4 | `get-h` (`:Box` param, read-only) | borrow-elision (no inc/dec pair) | **CONFIRMED for borrow-elision; DIVERGED on non-atomic RC.** get-h has **0** `atomic_rmw` — the borrowed param carries no refcount traffic at all. But the *non-atomic-RC-for-Confined* half of the task's item could **not** be exhibited by default: every heap-value RC op observed across the whole demo (and additional probe shapes) is `atomic_rmw`. The non-atomic arm is built (`heap::use_nonatomic_arm`, fires when a node's `confined = Some(true)`), but the confinement analysis is conservative and produced no default-Confined heap RC site in these shapes — atomic is the sound default, and confinement precision (0526/0528) is exactly the unbuilt frontier the attribution named. Recorded honestly rather than forcing a `CRANELISP_NONATOMIC_RC` probe (documented-unsound) into a "win." |
| 5 | `area` over `(deftype Rect …)` (straight-line, 2-ctor phi, all-Int) | escape→stack (narrow class) | **CONFIRMED.** `ss0`/`ss1 = explicit_slot 40` + `stack_addr`; immortal header `0x4000_0000_0000_0000` at `+8` (so the residual `atomic_rmw sub` never frees — dead free path); no allocator call. **But fields live in stack MEMORY** (`store v+24/+32`, `load v+24/+32`) — the seam of Act 2. |

## Act 2 — the frontier (each limit's actual CLIF verdict vs the diagnosis)

| # | Snippet | Claimed limit | **Actual CLIF verdict** | Confirms / diverges |
|---|---|---|---|---|
| 6 | `pair-sum` over `(deftype Pt (MkPt [:Int x :Int y]))` — 2-field, statically-known single-ctor, non-escaping, straight-line (the BEST case) | multi-field aggregate is NOT register-promoted (no SROA) | **STACK-MEMORY.** `explicit_slot 40` + `stack_addr`; fields written/read through memory (`store v+24`, `store v+32`, `load v+24`, `load v+32`). Only `call fn0(…,12)` is the match-fail panic (span 12), NOT an allocator call. The single-field `Cell` (#2) became a register; this two-field `Pt` does not. | **CONFIRMS** the diagnosis: value-flattening is single-field-only; no multi-field SSA-decomposition; a stack slot is memory, not registers. |
| 7 | `sum-areas` — the SAME `Rect` built inside a tail-self-recursive loop | gate 3 declines the stack path inside loops | **HEAP.** No `explicit_slot`; `iconst.i64 24` (header+payload) → allocator `call` per iteration, with a live `atomic_rmw sub` + free path. The escape fact is unchanged from `area`; the self-call is what declines it. | **CONFIRMS.** Cranelisp has no loop form — iteration is self-recursion — so gate 3 gates the stack path out of the entire iterative core, exactly as Wave-1b (i) found. |
| 8 | `label` over `(deftype Tagged … [:Int n :String s])` — a heap (String) field | all-scalar-payload (gate 2) required; heap-field → heap | **HEAP.** No `explicit_slot`; allocator `call`; `atomic_rmw add` (the inc keeping the String field alive in the box). | **CONFIRMS.** A heap-typed field disqualifies the whole aggregate from the stack path; no SROA to registers either. |
| 9 | `vsum` — a `Vec` local, read-only, non-escaping | dynamic size (gate 1) → heap | **HEAP.** Allocator `call` for the backing buffer; stores through the returned pointer; `atomic_rmw sub` + free on exit. | **CONFIRMS.** A dynamically-sized buffer cannot occupy a fixed stack slot regardless of escape/uniqueness. |

## Conclusion the IR supports

The optimizer is strong on the **scalar / unique / borrow** axes (Act 1 #1–#3, #5 confirmed;
#4 borrow-elision confirmed). The **frontier is register-residency for aggregates**:

- a multi-field record is **never** scalar-replaced into SSA registers — its best case is a
  stack **slot** (memory), and even that is declined inside loops (gate 3), for heap-field
  payloads (gate 2), and for dynamically-sized values (gate 1);
- **the missing mechanism is multi-field SSA-decomposition (SROA / value-flattening beyond
  one word)** — not built (`ownership-codegen.md §7` `HeapCategory::Value` is single-word,
  single-ctor, and gated behind the unbuilt `cranelisp-types` carrier);
- this is the **precondition for a future `--release` (LLVM) tier** — mem2reg/SROA promote
  such locals into registers, never onto the heap — to register-promote inner-loop aggregate
  locals.

**No divergence from the Wave-1b diagnosis was found in the IR.** The one place the demo
could not follow the task brief is the *non-atomic-RC-for-Confined* Act-1 item (§Act 1 #4):
by default the compiler emits atomic RC conservatively, and no shape in the demo produced a
default non-atomic RC op — itself consistent with the attribution's "residual
conservatively-atomic RC" finding and the unbuilt confinement-precision lever. Every other
claim in `optimization.demo` is grounded in the IR it displays.
