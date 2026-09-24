# RC discipline — the conservative lowering

> **Owner**: `design`, narrow-deployed to `cranelisp-backend`. Subordinate to
> [backend.md](backend.md).
>
> **What this document is**: the backend's reference-counting discipline when no
> ownership refinement applies — the uniform consuming convention as emitted,
> its extern application, the binders that own nothing, and
> the opt-in spark-capture borrow. Every refinement is defined against this
> lowering ([Principle 25](../arch/principles/25-narrowing-carries-its-check.md)).
>
> **Section numbers are citation anchors.** Source comments and tests cite them,
> so they are stable; a missing number is a retired section whose content now
> lives in one of the homes below.

## 0. Where the rest of RC lives

| Question | Canonical home |
|---|---|
| The convention as a boundary rule, and the extern boundary | [bounded contexts](../arch/bounded-contexts.md) §3 invariant 2; §4b invariants 3, 5 and 6 |
| Heap word layouts and header | `spec/12-runtime.md` §12.1 (descriptive); the "Heap Object Layouts" and "Heap Classification" sections of [interfaces](../arch/interfaces.md); the offsets are the associated constants beside each `#[repr(C)]` layout, starting with `HeapHeader` in `crates/cranelisp-types/src/heap.rs` |
| Why classification never sees a type variable | [concrete-boundary-type.md](../arch/concrete-boundary-type.md) §2 |
| Release emission, drop glue, match scrutinee lifetimes, the TCO transfer predicate | [transitive-drop-glue.md](transitive-drop-glue.md) §4–§6 |
| Ownership refinements narrowing this lowering | [ownership-codegen.md](ownership-codegen.md); the [ownership inference contract](../arch/ownership-inference.md) |
| Runtime IO teardown and trampoline transitions | [intrinsics ownership and disposal](../intrinsics/ownership-and-disposal.md) §6–§7 |
| Allocation ledger, RC tracing and double-free checks | [intrinsics diagnostic modes](../intrinsics/diagnostic-modes.md) |
| Capturing a heap parameter in a platform effect closure | [platform-dlls.md](../platform/platform-dlls.md) §4 |
| Where each mechanism sits in source | `crates/cranelisp-backend/CLAUDE.md` |

## 2. RC emission

### 2.1 Atomicity

- Increments and decrements are emitted inline as Cranelift `atomic_rmw` on the
  header count, never as extern calls.
- The last-reference path fences before it reads fields for release, then runs
  the value's release and deallocates.
- The one exception is a cell the ownership analysis proves `Confined`, which
  may take the non-atomic arm (`ownership-codegen.md` §5.1, §5.2). The ordering
  policy itself is intrinsics'
  ([intrinsics context](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics),
  invariant 3).

### 2.2 Guarded operations

A known ADT with both nullary and data constructors is `Mixed`: its word is a
bare tag below `NULLARY_TAG_THRESHOLD` or a heap pointer. Its RC operations skip
the count when the word is a tag. The guard is sound only because the type is
known and its tags are bounded; classification takes a concrete type, so no
guard is ever emitted for an unknown type.

## 3. Calling convention

### 3.1 The uniform consuming convention

One convention governs every call — user functions, closures, trait methods,
signature dispatch, constructors, inline builtins, Vec operations and externs.
It is the ⊤ of the ownership lattice: an edge without an inferred mode vector
compiles exactly this way, and closure-valued, constructor, extern, intrinsic
and platform-effect edges always do.

- **Caller.** A heap-typed variable argument is incremented before the call, so
  the caller's binding survives. A temporary starts at one and transfers without
  caller action. A sparked argument is forced at its position and transfers as
  a temporary.
- **Callee.** The callee owns every heap parameter and releases what it does not
  return. A user function releases at scope exit (§5). An extern releases in its
  Rust body (§3.3). A constructor stores the argument as an owned field that the
  ADT's release discharges later. An inline builtin on scalar operands has
  nothing to release.
- **Temporary closure callee.** After calling a closure that was itself a
  temporary, the caller releases the closure. A heap result is retained first in
  case it aliases a capture.
- **Balance.** A variable argument nets zero (caller +1, callee −1); a temporary
  nets −1 and is freed by its callee.

The convention is uniform because the split alternative — borrowing for
builtins and externs, with a caller-side release of temporaries — puts a
callee-classification branch at every application site. That is the parallel
structure Principles [7](../arch/principles/07-single-source-of-truth.md) and
[11](../arch/principles/11-single-pipeline-mode-parameters.md) exclude; the
per-extern cost of releasing its own arguments is small and enumerable.

### 3.3 Extern consumption

Every extern releases each heap argument it neither returns nor retains. For
each heap parameter an extern author decides exactly one of:

| Parameter fate | Extern obligation | Declared ownership fact |
|---|---|---|
| Flows out unchanged through the result | Return it; the caller's reference leaves with it | `AliasOf` |
| Stored in a structure that outlives the call | Store the transferred reference, or increment into storage | `Retained` |
| Only read | Release it before return; the caller adapts at the site when the analysis declares the read | `Borrowed` (analysis fact; the extern still consumes) |
| Otherwise | Release it before return | `Consumed` |

- The per-primitive record is the declaration row in
  `crates/cranelisp-primitives/src/declarations.rs`: its shim signature types
  each argument as owned or borrowed, and its ownership summary carries the
  fact. There is no separate audit table to keep in step.
- Runtime helpers behind an extern are not bound by it; the extern entry is.
  `cranelisp_run_io` consumes the caller's tree while the trampoline it drives
  borrows that tree (§3.5).
- **Vec operations compiled inline.** The operation releases its Vec operand
  only when that operand is an owned temporary by provenance, not by expression
  kind — an `if` or `match` that yields a binding is not a temporary. The
  release is rc-checked: it frees only at the last reference, because a
  temporary reached through a borrowed field is still owned by its parent (§5.5).

### 3.5 The IO extern and the trampoline

`cranelisp_run_io(io_ptr)` is a consuming extern. It drives the trampoline to
completion and then releases the caller's whole tree with one structural
`consume_io_tree(io_ptr)`. The trampoline itself borrows the caller's tree and
owns only what continuations produce during the walk. The node teardown table
and the trampoline's ownership transitions are intrinsics'
([§6](../intrinsics/ownership-and-disposal.md#6-the-io-family),
[§7](../intrinsics/ownership-and-disposal.md#7-trampoline-ownership-transitions));
this section states only the balance the extern entry relies on.

#### 3.5.4 Caller-tree and fresh nodes

- **Two disjoint owners.** Caller-tree nodes and their continuation closures are
  reachable from `io_ptr` and released by the terminal structural walk. Fresh
  nodes — produced by a continuation during the walk — are owned by the
  trampoline and released when it replaces them.
- **Freshness is viral.** Once a continuation returns a fresh node, everything
  reached from it is fresh: a fresh `Bind`'s inner and continuation, a fresh
  `Par`'s or `Select`'s branches. It never reverts, so a fresh subtree contains
  no caller-tree node and nothing is released twice.
- **Release sites.** A finished fresh node is released with `dec_shallow_io`
  under the `SpineTransferred` disposition. A fresh `Bind` is descended by
  acquiring its inner and continuation before releasing the parent, per
  intrinsics §7. A fresh continuation is released after it is invoked; a
  caller-tree continuation is left to the terminal walk.
- **Rejected: release at every replacement.** Releasing each replaced node
  unconditionally double-releases the caller's tree, because the terminal walk
  still reaches it. Ownership decides the release, not the replacement.

#### 3.5.7 Evidence is heap balance

Acceptance for trampoline release is alloc/dealloc balance, not a passing
program. The module guards are `decision24_run_io_pure_rc_balanced`,
`run_io_trampoline_rc_balanced` and the deep bind-chain balance test in
`crates/cranelisp-intrinsics/src/io/tests.rs`; a 1000-bind chain must end
balanced.

#### 3.5.10 Fresh `Par` and `Select` release

- A `Par` or `Select` node keeps its branches in a branch container, not on the
  `current` spine. The trampoline hands them to recursive trampolines (`Par`) or
  the reactor (`Select`) and leaves the sub-trees to the node's teardown
  ([io-trampoline.md](io-trampoline.md) §16.5).
- A fresh `Par` or `Select` therefore discharges its branch container when
  released. Their `SpineTransferred` rows match their `Structural` rows in the
  intrinsics teardown table, so `dec_shallow_io` discharges the branches through
  the same teardown tail as `consume_io_tree`
  ([Principle 7](../arch/principles/07-single-source-of-truth.md)).
- The release is timely: the node is replaced only after interpretation, when
  `Par` branches have joined and `Select` losers' futures have been dropped.
- It cannot double-free: the branches are fresh (§3.5.4), so the caller's
  terminal walk never reaches them.
- Evidence: `dec_shallow_io_select_deep_frees_branch_vec_and_all_branches` and
  `dec_shallow_io_par_deep_frees_branches` in
  `crates/cranelisp-intrinsics/src/drop/tests.rs`; the heap-balance e2e
  `fresh_select_in_continuation_rc_balanced` and
  `fresh_par_in_continuation_rc_balanced` in `tests/concurrency_fanout.rs`.

## 5. Scope cleanup

- At the end of every `let` body and function body, scope cleanup releases the
  frame's heap-typed owning bindings — for a function, its parameters too —
  except the binding the body returns, whose owner transfers to the caller.
- When the body is not a bare binding but may yield one (an `if` or `match`
  whose result aliases a binding), the result is retained before cleanup. A
  body whose result is an independently owned reference needs no retain, and
  borrowed bindings do not count as cleanup targets. `protect_return_value`'s
  rustdoc carries the exact gate.
- The frame tracks owning references only. Captures and borrowed binders live
  outside it; §5.5 and §5.6 are the rules that follow.

### 5.5 Captured and borrowed binders

Two kinds of binder may never transfer ownership by last use:

- **Captured variables.** The closure environment holds its own retained
  reference and the enclosing scope still releases its reference at exit, so
  no textual use is the value's last.
- **Borrowed variables.** A binder projected from a scrutinee's field in a
  constructor pattern is neither incremented at extraction nor released at scope
  exit; the scrutinee still owns the value.

Last-use analysis marks the final use of each variable as a transfer candidate,
on which Vec COW may mutate in place; `is_last_use` rejects captured and
borrowed binders.
Violating this lets COW mutate an aliased Vec in place, after which the owner's
release frees it a second time. The Sprint 61 reduction
`(consume (Box [0]))`, which read length `0`, is the pinned regression
(`tests/regression.rs`).

The ownership analysis treats both as inferred cases —
`borrowed_vars` seeds borrow-through-projection
([ownership inference](../arch/ownership-inference.md) §8.2). These structural
rules are the conservative lowering beneath it.

### 5.5.2 Spark-capture borrow (opt-in)

A structurally joined spark may borrow, rather than retain, its heap captures:
the capture-store increment and the matching closure-release decrement are both
skipped. It generalises §5.5's borrowed binder to a new introduction site. It is
off by default behind `CRANELISP_CAPTURE_BORROW=1`, and byte-identical when off.

**Open condition before default-on.** The parent-outlives-spark argument (§5.5.2.3)
is proven for the synchronous apply-argument and `let` joins. It is **not**
established for the `ParBind` continuation: that closure may capture values in a
returned IO tree that the trampoline runs later, so the capturing frame may not
outlive the borrow — the lifetime-across-suspension class. The toggle raises the
borrow at that site. Making the borrow default-on requires first proving that
site or gating it out. The ownership analysis resolves the same question by
classifying suspension crossings as escapes (ownership inference §2.2 rule 4);
that ruling does not govern this toggle.

#### 5.5.2.1 The structural-join gate

Borrowing is admissible only when every spark joins inside the capturing
frame's dynamic extent:

- apply-argument sparks, forced at the barrier before the call is emitted
  ([lenient-eval.md](lenient-eval.md) §4.4);
- independent `let` sparks, forced before the body (lenient-eval §4.2);
- `ParBind` branch continuations — structured fork-join
  (`spec/12-runtime.md` §12.4.3), subject to the open condition above.

**`LaunchContinue` must retain.** A launched sub-tree runs on a detached strand
with no join in the parent's extent (`spec/10-io.md` §10.12.7); a borrowed
capture there is a use-after-free once the parent's cleanup runs.

**Dependent `let` sparks must retain.** Their synthetic IVar-pointer captures
are keep-alives, not borrows of a live parent binding
(lenient-eval §4.4.1).

The gate reads the lowering site; it does not analyse. `ParBind` and
`LaunchContinue` are distinct `MonoExpr` variants so a joined spark cannot be
lowered as detached or the reverse
([Principle 20](../arch/principles/20-model-invariants-by-representation.md)).
A compiler flag is raised only around the joined emission sites; the launch
lowering never raises it. Both the capture increment and the release decrement
read the same flag, so they cannot be skipped separately.

#### 5.5.2.2 Coarse retain

Every capture of a joined spark borrows; there is no per-capture escape
decision. The only reference crossing the join outward is the spark's result.
It is an ordinary temporary under §3.1, and the degenerate case of a result that
is itself a capture is covered by §5.6.

#### 5.5.2.3 Why it is sound

1. **The parent outlives the spark.** Each eligible join completes inside the
   capturing frame's extent, so the parent's owning reference covers every read
   and its cleanup runs after the join — the §5.5 scrutinee argument.
2. **No COW hazard.** The spark only reads. Being rc-invisible, the borrow also
   stops inflating the parent's count during the spark.
3. **One escape, already audited.** The result travels by §3.1 and §5.6.

#### 5.5.2.4 Failure modes the shape excludes

- Admitting a detached launch frees the cell under a still-running strand;
  excluded by representation, not by a predicate.
- Letting a capture escape by any path other than the result outlives the
  parent's release; excluded by having no per-capture classifier. A bespoke
  classification traversal with a blind spot is the failure class this avoids
  (FIXME 0494's starved consuming increment).

#### 5.5.2.5 The boundary

Borrowing a capture because an analysis shows it does not escape is escape
analysis. It belongs to the ownership analysis, which widens the admit set on
the same borrowed/owned axis; it must not be added to this toggle.

#### 5.5.2.6 Evidence and measured effect

- **Permanent UAF guard.** A `LaunchContinue` capturing a heap value keeps its
  increment and release with the toggle on — at the backend seam
  (`compiler/control_flow/par_codegen_tests.rs`) and end to end.
- **Parallel ≡ serial.** The S99 fixtures (`tests/fixtures/s99/`) produce the
  same result lenient and under `CRANELISP_NO_LENIENT=1`, with heap balance
  (`tests/s99_fixtures.rs`).
- **Measured effect.** With the toggle on, parallel `rc_inc` falls to exactly
  the serial count: the borrow elides precisely the joined-spark capture
  increments. That is hundreds of increments, not millions — spark count is
  bounded by the create-gate budget, and capture arity is about one. The
  measurement is `tests/plan/s99-measurement.md` §8.

#### 5.5.2.7 Where the contention actually is

The dominant atomic-RC traffic in the S99 workloads is in-leaf Vec COW: each
copy re-increments every retained element. The spark-capture borrow does not
reach it, and neither the saturation gate nor the allocator swap removed it
(`tests/plan/s99-measurement.md` §9–§10). The levers that do are owned-copy
mutation in place, uniqueness-driven reuse and non-atomic confined RC — the
ownership work in [uniqueness and reuse](ownership-codegen.md#6-uniqueness-and-reuse),
[value flattening](ownership-codegen.md#7-one-word-value-flattening) and
[confined RC](ownership-codegen.md#51-one-decision-point-two-gates), under the
ownership inference contract. It is an extension of §5.5's last-use
rule, not a widening of this borrow.

### 5.6 Capture-return inc

When a lambda body is a bare reference to a heap-typed captured variable, the
body increments the value before returning.

- The closure's release decrements its captures after the body returns, so a
  returned capture needs a reference of its own. `protect_return_value` cannot
  see it, because captures are absent from the scope frame.
- The balancing increment belongs in the closure body, which knows at codegen
  time that it returns a capture. The alternative — having the trampoline detach
  captures before releasing a one-shot closure — would make the runtime read the
  closure's capture layout, which is backend-owned. Do not reopen this as a
  runtime change.
- It is a separate helper, `emit_capture_return_inc`, so
  `protect_return_value` keeps its scope-frame rule.
- Evidence: `lambda_return_captured_heap_var_emits_inc`
  (`compiler/control_flow/lambda.rs`) and the then-combinator RC block in
  `tests/spec_10_io.rs`. The raw S61 reduction logs are in
  [Git](https://github.com/alilee/cranelisp/tree/fc49541f/tests/sprint61/race-evidence).
