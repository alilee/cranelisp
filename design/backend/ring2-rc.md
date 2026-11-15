# RC discipline — the conservative lowering

> **Owner**: `design`, narrow-deployed to `cranelisp-backend`. Subordinate to
> [backend.md](backend.md).
>
> **What this document is**: the backend's calling convention as emitted, its
> extern application, the IO extern's balance and the RC emission primitives.
> *When* a reference is duplicated, moved or dropped is
> [uniform counting](uniform-counting.md), built at S123 W2; the scope-exit
> release, borrowed binders, spark-capture borrow and capture-return increment
> this document used to carry are retired with it.
>
> **Section numbers are citation anchors.** Source comments and tests cite them,
> so they are stable; a missing number is a retired section whose content now
> lives in one of the homes below.

## 0. Where the rest of RC lives

| Question | Canonical home |
|---|---|
| The convention as a boundary rule, and the extern boundary | [bounded contexts](../arch/bounded-contexts.md) §3 invariant 2; §4a invariant 8; §4b invariants 3, 5 and 6 |
| Heap word layouts and header | `spec/12-runtime.md` §12.1 (descriptive); the "Heap Object Layouts" and "Heap Classification" sections of [interfaces](../arch/interfaces.md); the offsets are the associated constants beside each `#[repr(C)]` layout, starting with `HeapHeader` in `crates/cranelisp-types/src/heap.rs` |
| Why classification never sees a type variable | [concrete-boundary-type.md](../arch/concrete-boundary-type.md) §2 |
| When a reference is moved, duplicated or dropped | [uniform-counting.md](uniform-counting.md) |
| Release emission and drop glue | [transitive-drop-glue.md](transitive-drop-glue.md) §4 |
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
- The confined non-atomic arm has no consumer since S123 W2
  (`ownership-codegen.md` §5.1), so every emitted RC operation is atomic. The
  ordering policy itself is intrinsics'
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
Every position that receives a heap value consumes it.

- **Caller.** A heap-typed variable argument moves at its binder's last use and
  is duplicated otherwise ([uniform counting](uniform-counting.md) §1). A
  temporary transfers without caller action. A sparked argument is forced at
  its position and transfers as a temporary.
- **Callee.** The callee owns every heap parameter and releases each where it
  dies. A user function's drops are its ownership plan's. An extern releases in
  its Rust body (§3.3). A constructor stores the argument as an owned field
  that the ADT's release discharges later. An inline builtin on scalar
  operands has nothing to release.
- **Temporary closure callee.** After calling a closure that was itself a
  temporary, the caller releases the closure.
- **Balance.** Every reference that enters a call is consumed exactly once,
  by the callee.

The convention is uniform because the split alternative — borrowing for
builtins and externs, with a caller-side release of temporaries — puts a
callee-classification branch at every application site. That is the parallel
structure Principles [7](../arch/principles/07-single-source-of-truth.md) and
[11](../arch/principles/11-single-pipeline-mode-parameters.md) exclude; the
per-extern cost of releasing its own arguments is small and enumerable.

### 3.3 Extern consumption

Every extern primary entry takes ownership of every heap argument, with no
exception ([BC §4a invariant 8](../arch/bounded-contexts.md#4a-primitives--cratescranelisp-primitives)).
For each heap parameter an extern author decides exactly one of:

| Parameter fate | Extern obligation | Declared ownership fact |
|---|---|---|
| Flows out unchanged through the result | Move that same reference into the result | `IntoResult`, with an `AliasOf` result |
| Stored in a structure that outlives the call | Store the transferred reference | `Retained` |
| Only read | Release it before return | `Borrowed` (an analysis fact only; the entry still consumes) |
| Otherwise | Release it before return | `Consumed` |

- The per-primitive record is the declaration row in
  `crates/cranelisp-primitives/src/declarations.rs`: its shim signature takes
  each heap argument owned, and its ownership summary carries the analysis
  fact. There is no separate audit table to keep in step. `string-identity`
  moves its argument into its result (ACT-0974, landed at the S122 close).
- The backend reads no declared ownership fact: every extern argument is
  consumed whatever the fact says.
- Runtime helpers behind an extern are not bound by it; the extern entry is.
  `cranelisp_run_io` consumes the caller's tree while the trampoline it drives
  borrows that tree (§3.5).
- **Vec operations compiled inline.** The operation consumes its Vec operand:
  a read-only one releases it after reading, and a COW one updates in place at
  count 1 or copies and releases the source. The release is rc-checked, so it
  frees only at the last reference.

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

Retired at S123 W2, with §5.5, §5.5.2 and §5.6. Scope exit releases nothing;
every binder is dropped where it dies
([uniform counting](uniform-counting.md) §1).

### 5.5 Captured and borrowed binders

Retired. There are no borrowed binders and no uncounted aliases: a pattern
field binder owns a duplicate, and a capture belongs to its closure
environment, so a use inside the body duplicates
([uniform counting](uniform-counting.md) §3, §4). The hazard this section
guarded — an in-place COW on a value another binder still names — is excluded
because every name that holds the value is counted, so the `rc == 1` probe sees
it. The Sprint 61 reduction `(consume (Box [0]))` stays pinned in
`tests/regression.rs`.

### 5.5.2 Spark-capture borrow (opt-in)

Retired, with `CRANELISP_CAPTURE_BORROW`. Spark captures duplicate
([uniform counting](uniform-counting.md) §3.1).

#### 5.5.2.6 Evidence and measured effect

The S99 workloads' dominant atomic RC traffic was
in-leaf Vec COW, where each copy re-increments every retained element. The
capture borrow removed only hundreds of increments, bounded by the create-gate
budget (`tests/plan/s99-measurement.md` §8–§10). In-place reuse at count 1 is
the lever that reaches that traffic.

### 5.6 Capture-return inc

Retired. A closure body's use of a capture duplicates, so a returned capture
carries its own reference without a special case.
