# Lenient Evaluation Design

Sprint 25 — automatic parallelization of independent `let` bindings.
Sprint 92 (slice 1 of the effect-concurrency track) — widened to independent **apply-arguments** (see §2.5, §4.4), making a general parallel `par-map` expressible.
Sprint 94 (FIXME 0424 limit #2) — widened the `let` path to **dependent bindings** (RHS references an earlier *sparked* binding), sparked as IVars whose dependency references are substituted with on-demand `ivar_force` reads (see §2.6, §4.5). Backend-only, no new runtime, no public-API impact (arch R5). This is the substrate the stdlib `par-*` functions build on.

## 1. Problem

Cranelisp is a pure functional language: all `let` binding expressions are side-effect-free and referentially transparent. When multiple bindings in a `let` block are independent (no binding references an earlier binding's name), they produce the same result regardless of evaluation order. The compiler can evaluate them concurrently without changing program semantics.

Spec §12.4.3 mandates this: an implementation MUST evaluate independent `let` bindings in parallel where a cost heuristic determines it is beneficial.

**The same is true of the arguments of a function application** `(f a₁ … aₙ)`: arguments are pure values (effects flow through `IO`/`bind!`, never through raw argument evaluation), so independent, individually-expensive arguments produce the same result regardless of evaluation order and may be evaluated concurrently. Until Sprint 92 only `let` bindings were sparked, so `(Pair (fib a) (fib b))` ran the two `fib`s serially and a general `par-map` (an `fmap` of an expensive function, where every per-element application is an apply-argument) compiled correctly but ran serially. FIXME 0424(i) is the capability gap; §2.5 + §4.4 are the design. Spec note: §12.4.3 currently scopes the lenient-eval permission to `let` bindings and §12.4.1/§4.11 positively guarantee left-to-right argument evaluation — widening the permission to apply-args is filed as FIXME 0441 (`target: /spec`); see §8.

## 2. Sparkability Analysis

The sparkability analysis is a codegen-internal function. It runs inside `compile_let` at IR generation time, after typechecking is complete. It does not affect the AST, `CheckResult`, or any cross-crate interface.

### 2.1 Algorithm: `find_sparkable_bindings`

Given a `let` block with bindings `[(x0, e0), (x1, e1), ..., (xN, eN)]`:

```rust
fn find_sparkable_bindings(
    bindings: &[(Symbol, Expr)],
    globals: &HashSet<Symbol>,
) -> Vec<usize> {
    let mut bound_names: HashSet<Symbol> = HashSet::new();
    let mut sparkable: Vec<usize> = Vec::new();

    for (i, (name, val_expr)) in bindings.iter().enumerate() {
        let fv = free_vars(val_expr, globals);
        let depends_on_earlier = fv.iter().any(|v| bound_names.contains(v));

        if !depends_on_earlier && is_worth_sparking(val_expr) {
            sparkable.push(i);
        }

        bound_names.insert(name.clone());
    }

    // No point sparking a single binding — need at least 2
    if sparkable.len() < 2 {
        Vec::new()
    } else {
        sparkable
    }
}
```

A binding at index `i` is **sparkable** if:
1. **Independence**: its free variables do not include any name bound by bindings `0..i` in the same `let` block.
2. **Cost threshold**: it is a non-trivial function call (see §2.2).

The full sparkable set must have **at least 2 members**. A single independent binding gains nothing from parallel dispatch — the overhead of IVar creation and thread pool submission exceeds any benefit.

### 2.2 Cost Heuristic: `is_worth_sparking`

A binding expression is worth sparking only if it is a function call (`Expr::Apply`) whose callee is NOT a known-cheap builtin. Known-cheap builtins are:

```
+  -  *  /  =  <  >  <=  >=  not  and  or
```

These operations are single-instruction or near-single-instruction at the hardware level. The cost of IVar creation (~allocation + atomic store), thread pool submission (~deque push), and forcing (~CAS + potential spin) vastly exceeds the cost of evaluating them sequentially.

Expressions that are NOT function calls — literals, variable references, lambda expressions (without application) — are also excluded. Only `Expr::Apply` with a non-cheap callee qualifies.

Non-variable callees (e.g., `((get-fn) arg)` — an application of a computed function) are conservatively treated as worth sparking, since the callee's cost is unknown.

### 2.3 Trace Body Exclusion

Inside `(trace ...)` bodies, sparkability analysis is disabled. Lenient evaluation would interleave traced execution across threads, producing non-deterministic trace output. When `self.in_trace_body` is true, `find_sparkable_bindings` returns an empty vec.

### 2.4 `CRANELISP_NO_LENIENT` Opt-Out

The environment variable `CRANELISP_NO_LENIENT=1` disables automatic sparking entirely. This is a debugging escape hatch — when concurrent evaluation makes a bug harder to reproduce, sequential evaluation restores deterministic binding order.

Implementation: a `LazyLock<bool>` static, checked once per process:

```rust
static LENIENT_DISABLED: LazyLock<bool> =
    LazyLock::new(|| std::env::var("CRANELISP_NO_LENIENT").map_or(false, |v| v == "1"));
```

When `*LENIENT_DISABLED` is true, `compile_let` skips sparkability analysis and compiles all bindings sequentially.

### 2.5 Apply-Argument Sparkability (Sprint 92)

The same decision pass widens to the arguments of a function application `(f a₁ … aₙ)`. The carried-over gates are identical to the `let` path; the only net-new question is per-call-site **argument independence** (the `let` path's "does this binding reference an earlier binding's name" check has no apply analogue — the args of one apply share no binding scope among themselves).

#### 2.5.1 One analysis, two call sites (Principle 7)

The cost heuristic (`is_worth_sparking`), the cheap-builtin/constructor exclusions (`CHEAP_BUILTINS`, the `constructors` set), and the ≥2-candidate gate are **single-source** in `sparkability.rs` and must serve both paths — duplicating them into an apply-specific copy would be the recurring-mirror defect Principle 7 (single source of truth) forbids. The recommendation is therefore **two thin call sites into shared logic**, not one merged analysis:

- `find_sparkable_bindings(bindings, constructors) -> Vec<usize>` stays as-is (the `let` path).
- A sibling `find_sparkable_args(args, constructors) -> Vec<usize>` is added, which **reuses `is_worth_sparking` verbatim** and applies the ≥2 gate, differing only in the independence rule below.

Rationale for a sibling rather than a single generalized function: the two inputs differ in shape (`&[(Symbol, MonoExpr)]` vs `&[MonoExpr]`) and the independence rule differs (sequential-prefix free-var check vs the pairwise rule below). Folding both into one function would force an awkward union signature; a sibling that shares the *gate helpers* (`is_worth_sparking`, the cheap/constructor sets, the ≥2 constant) keeps the single-source property where it matters (the heuristics) while letting each call site state its own independence rule clearly. `is_worth_sparking` is promoted to the shared helper both siblings call.

#### 2.5.2 Argument independence

Apply arguments introduce no bindings visible to their siblings — `a₂` cannot reference a name bound by evaluating `a₁`, because argument evaluation binds nothing into scope. Therefore **all arguments of a single apply are mutually independent by construction** as pure expressions: there is no inter-argument data dependence to analyze. Independence analysis collapses to "is this argument individually worth sparking" (the cost heuristic) — the `depends_on_earlier` free-var check that the `let` path runs has no apply counterpart and is omitted.

Each argument is a sparkable candidate iff `is_worth_sparking(arg, constructors)` holds (a non-trivial `Apply` whose callee is not a cheap builtin or a constructor — literals, var refs, lambdas, and cheap calls are excluded exactly as in the `let` path). The ≥2-candidate gate then applies: spark only when at least two arguments qualify, so a single expensive argument never pays IVar/thread-pool overhead for no concurrency.

#### 2.5.3 Interaction with the callee and resolved-call shapes

Sparkability is decided over the **argument `MonoExpr`s only**; the callee is never sparked (it is evaluated on the calling thread as today). The pass runs at the apply site **before** the existing dispatch fork in `compile_apply` (TCO check, `ResolvedCall` lowering, constructor construction, closure/direct call). A sparked-argument apply must **not** also take the TCO self-call fast path in the same step — a tail self-call jumps to the loop header and would bypass the force barrier — so apply-arg sparking is gated to the non-tail, non-TCO arm (when `find_sparkable_args` returns ≥2 indices and the apply is not a tail self-call). Trace-body exclusion (§2.3) and `CRANELISP_NO_LENIENT` (§2.4) apply unchanged — both are checked at the apply site exactly as at the `let` site.

When `find_sparkable_args` returns ≥2 indices, the sparking is no longer *unconditional*: the backend emits a **create-gate** (§3.6.2) — a runtime `try_reserve` branch that allocates the IVars/thunks only on the budget-granted arm and falls back to the existing sequential arg codegen on the over-budget arm. This is what restores the never-slower-than-serial floor for over-sparking recursion (§3.6.3); the *static* sparkability decision (≥2 expensive args) is necessary but not sufficient, because it cannot see dynamic recursion depth.

### 2.6 Dependent-binding sparks — the `let`-path limit #2 (S94, FIXME 0424)

Apply-arg sparking (§2.5) and the `let`-path independence rule (§2.1) both spark only
**independent** work: the `let` rule rejects a binding whose RHS references an earlier
binding (`depends_on_earlier`). FIXME 0424's remaining generalization (arch R5, S93
user ruling) relaxes exactly this rejection — **limit #2: admit a *dependent* binding
by sparking it as an IVar and forcing its dependency on demand.** This is the substrate
the stdlib `par-map`/`par-reduce`/`par-map-reduce` functions (`/stdlib`, separate wave)
build on for the divide-and-conquer shape, where the second half's binding references
the first. It is **backend-only — no new runtime, no public-API impact** (arch R5): it
reuses the existing IVar create/spark/force machinery (§3) and the create-gate (§3.6)
verbatim; only the sparkability admission rule and the dependent-thunk emission change.

#### 2.6.1 The relaxed admission rule

Today `find_sparkable_bindings` (§2.1) sets `depends_on_earlier` and excludes any
binding whose free vars touch an earlier-bound name. The relaxation keeps the rule but
adds a **dependency-on-sparked carve-out**:

> A binding at index `i` is **sparkable** if it is worth sparking (§2.2) AND every
> earlier-bound free var it references is *itself in the sparkable set* (already
> admitted as a spark at some index `j < i`).

In one pass, left to right, maintaining the running `sparkable` set:

- An **independent** binding (no earlier-bound free var) is admitted iff
  `is_worth_sparking` — unchanged from §2.1.
- A **dependent** binding (references earlier-bound names) is admitted iff
  `is_worth_sparking` AND **all** of its earlier-bound free-var dependencies are
  already in `sparkable`. If it depends on any **non-sparked** earlier binding (a
  cheap one excluded by the cost heuristic, or a literal/var binding), it is **not
  sparkable** — its dependency is bound only as an ordinary `Value` in Phase 2, which a
  concurrently-running thunk created in Phase 1 cannot see (§2.6.3). This is the precise
  minimal relaxation: a dependent spark is admissible exactly when its dependencies are
  available *as IVars to force*.

Because `let` bindings are sequential, dependencies only point backward — there are no
cycles, and source order is already a valid topological order. The ≥2 gate (§2.1) and
the cost heuristic (§2.2) are unchanged and stay single-source.

`find_sparkable_args` (§2.5, the apply path) is **unaffected** — apply arguments bind
nothing into sibling scope, so there is no dependent-argument analogue. Limit #2 is a
`let`-path-only generalization.

#### 2.6.2 The parallelism this actually extracts (and the floor)

For a binding whose RHS depends *entirely and immediately* on one earlier spark
(`(b (f a))` where `a` is sparked), the dependent thunk blocks at the force of `a`
almost immediately — little is gained beyond `a`'s own parallelism. The real win is
**partially-dependent** RHS: in `(b (g (f a) (h c)))` where `c` is independent, the
`(h c)` sub-work runs concurrently while `a` is still computing; the thunk blocks only
at the `(f a)` force. The dependent spark pipelines the independent sub-work of `b`
against `a`'s computation. The **spark-machinery floor** (§3.6.3) is preserved:
forcing `a` is the same work sequential evaluation does, and the create-gate still
bounds total IVar allocation to `O(cap)` (the dependent thunks count toward the same
budget batch).

> **Floor scope (S94 /port ruling + S99 ablation — FIXME 0459).** "Floor" here means the
> **spark-*machinery* overhead** the create-gate genuinely bounds — IVar/thunk allocation, which
> is `O(cap)` regardless of tree size. It does **NOT** bound **per-branch *user-level* contention**:
> the heap allocation + atomic-RC cache-line bouncing (Decision 13) that each of the `cap` live
> branches generates concurrently. Count is the wrong signal for contention — the create-gate
> cannot see it. For allocation-/RC-heavy parallel workloads the never-slower-than-serial floor is
> **VIOLATED**: S99's F2/F4 ablation on release measured parallel **2.3× slower** (F2) to **6–15×
> slower** (F4) than serial even after the in-track cures, because the dominant cost is the in-leaf
> vec-COW leaf-refcount traffic (`s99-measurement.md` §10.3; `ring2-rc.md` §5.5.2.7). The
> user-level-contention floor is a **Phase-H** target (owned-copy mutate-in-place / non-atomic
> thread-local RC), not a create-gate one. See §3.6.3 and `effect-concurrency.md` §3.1.

#### 2.6.3 Why the dependency must be forced, not captured

The current lenient `let` (§4.2) creates+sparks all IVars in **Phase 1** *before* any
binding value is bound (Phase 2). So at the moment a dependent binding's thunk is
built, its dependency `a` is **not yet a `Value` in scope** — it is an unforced IVar.
The thunk therefore cannot capture `a`'s value; it must capture `a`'s **IVar pointer**
and force it on demand. Forcing is safe to do concurrently from both the dependent
thunk and Phase 2's own force of `a`: `ivar_force` (§3.5) is idempotent under its
CAS+spin state machine (whoever wins computes; the other reads the resolved value —
work conservation). The substitution `a → ivar_force(ivar_a)` is the mechanism the arch
brief names; §4.5 is the codegen.

## 3. IVar Runtime Primitives

IVars are write-once synchronization cells. They live in `cranelisp-runtime` as `extern "C"` functions registered as JIT builder symbols.

### 3.1 Heap Layout

IVars are heap-allocated, RC-managed values using the base-pointer convention (arch Decision 10):

```
Base pointer →
  +0   alloc_size: i64   (= 40)
  +8   rc: i64           (initial: 1, atomic)
  +16  state: i64        (atomic — PENDING/EVALUATING/RESOLVED)
  +24  value: i64        (result, valid when state = RESOLVED)
  +32  thunk: i64        (closure pointer — zero-arg thunk)

Total allocation: 40 bytes (16 header + 24 payload)
```

The base pointer points to offset 0 (alloc_size), not the payload. This follows the reimplementation's base-pointer ABI. All field accesses use positive offsets from the base pointer.

### 3.2 State Machine

Three atomic states, using i64 constants:

| State | Value | Meaning |
|---|---|---|
| PENDING | 0 | Thunk has not been evaluated; value field is invalid |
| EVALUATING | 1 | A thread has claimed the thunk and is executing it |
| RESOLVED | 2 | Thunk has been evaluated; value field contains the result |

State transitions:
- `PENDING → EVALUATING`: via CAS in `ivar_force`. Exactly one thread succeeds.
- `EVALUATING → RESOLVED`: via atomic store in `ivar_force`, after storing the result. Only the thread that won the CAS performs this transition.

No other transitions are valid. There is no `PENDING → RESOLVED` shortcut.

### 3.3 `cranelisp_ivar_create`

```rust
#[unsafe(export_name = "cranelisp_ivar_create")]
pub extern "C" fn ivar_create(thunk: i64) -> i64
```

**Semantics**: Allocate an IVar cell. Set `state = PENDING`, store the thunk pointer, return the base pointer.

**Implementation**:
1. Call `alloc_with_rc(24)` — 24 bytes payload (16 header added by allocator = 40 bytes total). The allocator sets `alloc_size = 40` at offset 0 and `rc = 1` at offset 8.
2. Store `PENDING (0)` at offset 16 (state).
3. Store `0` at offset 24 (value — unused until resolved).
4. Store `thunk` at offset 32 (thunk closure pointer).
5. Return the base pointer.

The thunk pointer is a Cranelisp closure with the reimplementation's `HeapClosure` layout: `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`. It is a zero-argument thunk — the code_ptr has signature `extern "C" fn(env_ptr: i64) -> i64`.

### 3.4 `cranelisp_ivar_spark`

```rust
#[unsafe(export_name = "cranelisp_ivar_spark")]
pub extern "C" fn ivar_spark(ivar: i64) -> i64
```

**Semantics**: Submit a force-and-dec task to the rayon global thread pool (incrementing the IVar's RC for the spark task's reference). `ivar_spark` **always spawns** — the spawn-vs-direct decision is no longer taken here. As of Sprint 92 (create-gate, §3.6) the backend has *already decided* this cell is worth sparking, via a runtime budget check emitted **before** the IVar was even allocated; by the time `ivar_spark` runs, the lenient path has been chosen, so the only correct action is to spawn. On spawn-task completion the task **releases one spark-budget permit** via the `InFlightGuard` RAII drop (§3.6).

**Implementation** (always-spawn):
1. Atomically increment RC at `ivar + 8` using `fetch_add(1, SeqCst)`. The spark task needs the IVar to stay alive until it finishes.
2. Call `rayon::spawn(move || { ... })` with a closure that:
   a. Releases one spark-budget permit on completion **or unwind** via the `InFlightGuard` RAII guard (§3.6).
   b. Calls `ivar_force(ivar)` — evaluates the thunk if still PENDING (or hits the RESOLVED fast path if the consuming thread already claim-computed it at the barrier — work conservation, §3.5).
   c. Atomically decrements RC at `ivar + 8` using `fetch_sub(1, SeqCst)`.
   d. If the old RC was 1 (now 0), emits an Acquire fence and frees the IVar.
3. Return 0 (return value unused).

The pre-Sprint-92 "resolve inline when over budget" branch is **removed** — the over-budget case is now handled *before* `ivar_spark` is reached, by the create-gate's direct arm (§3.6), which never allocates the IVar in the first place.

**RC ordering**: All atomic RC operations use `SeqCst` ordering, per arch Decision 13. The sketch uses `Relaxed` for the inc and `Release` for the dec — the reimplementation uses `SeqCst` throughout for consistency with the atomic RC convention established in Ring 1 (`ring2-rc.md` §2.1).

### 3.5 `cranelisp_ivar_force`

```rust
#[unsafe(export_name = "cranelisp_ivar_force")]
pub extern "C" fn ivar_force(ivar: i64) -> i64
```

**Semantics**: Resolve the IVar. Returns the value. May evaluate the thunk (if PENDING), spin-wait (if another thread is EVALUATING), or return immediately (if RESOLVED).

**Implementation**:
1. **Fast path**: Load state from `ivar + 16` with `SeqCst`. If `RESOLVED`, load and return value from `ivar + 24`.
2. **CAS**: Attempt `compare_exchange(PENDING, EVALUATING, SeqCst, SeqCst)` on the state field.
   - **Success** (we won the race):
     a. Load `thunk` from `ivar + 32`.
     b. Load `code_ptr` from `thunk + 16` (closure's code_ptr offset in reimplementation layout).
     c. Call `code_ptr(thunk)` — the thunk evaluates the binding expression, returning the result as i64.
     d. Store result at `ivar + 24`.
     e. Store `RESOLVED` at `ivar + 16` with `SeqCst` ordering — this publishes the result to other threads.
     f. Return the result.
   - **Failure** (another thread claimed it):
     a. Spin-wait: loop loading state with `SeqCst`, calling `spin_loop()` hint, until state becomes `RESOLVED`.
     b. Load and return value from `ivar + 24`.

**CAS ordering**: The sketch uses `AcqRel`/`Acquire` for the CAS. The reimplementation uses `SeqCst`/`SeqCst` for consistency with Decision 13.

**Thunk closure calling convention**: The thunk is a zero-arg closure. The code_ptr is at offset 16 from the base pointer (past the 16-byte heap header). The calling convention is `code_ptr(env_ptr: i64) -> i64`, where `env_ptr` is the closure's base pointer. This matches the reimplementation's closure layout (Decision 11): `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`.

### 3.6 Global In-Flight-Spark Budget — the backend create-gate (Sprint 92)

**Problem.** The sparkability cost heuristic (§2.2) is *syntactic* — it sees "a non-cheap `Apply`" and decides it is worth sparking, with no knowledge of dynamic recursion depth. Once apply-arg sparking ships (§2.5), a naive recursive `(add-i64 (fib a) (fib b))` becomes a two-expensive-argument apply at **every node** of an exponential recursion tree, so it would spark `O(2ⁿ)` IVars. A runtime cap on *concurrency alone* is necessary but **not sufficient** to restore the never-slower-than-serial floor: the backend emits and runs `ivar_create` + `ivar_spark` + (later) `ivar_force` for **every** sparkable argument *before* any in-`ivar_spark` budget check could fire, so even a cap of 0 still pays ≈2 thunk closures + 2 IVar cells per recursion node — measured ≈140× serial for naive `fib(30)` (FIXME 0444). The decision point was downstream of the allocation it needed to prevent.

**The fix — move the budget decision before allocation (a backend create-gate).** The budget query becomes a **codegen concern**: at each spark site the backend emits a runtime branch *before* the IVar/thunk are built. Two cooperating pieces:

1. **A reservation counter + try-reserve primitive** in `ivar.rs` (`cranelisp-intrinsics`), callable from emitted code.
2. **A create-gate** in the backend (`apply.rs`, and symmetrically `let_if.rs`) that calls try-reserve, then branches into a **lenient arm** (build thunks, create+spark IVars, force barrier — as before) or a **direct arm** (the existing sequential arg/binding codegen — no IVars, no thunks, no allocation).

This bounds **total** IVar/thunk allocations to `O(cap)` (not `O(nodes)`): the exponential remainder of an over-sparking tree executes on the direct arm, allocation-free, paying only one cheap atomic per site.

#### 3.6.1 The reservation counter + try-reserve primitive (`cranelisp-intrinsics`)

```rust
// Module-level in ivar.rs. AtomicIsize (not Usize): a stray over-decrement
// goes negative (still < cap ⇒ keeps granting) rather than wrapping to a huge
// value that would silently wedge the budget to permanent-direct.
static IN_FLIGHT_SPARKS: AtomicIsize = AtomicIsize::new(0);

// Default = a small multiple of the rayon pool width (see "Cap" below).
// budget = 0 ⇒ try_reserve always returns 0 ⇒ every site takes the direct arm.
static SPARK_BUDGET: LazyLock<usize> = LazyLock::new(|| { /* env CRANELISP_SPARK_BUDGET, else 4×threads */ });

/// Try to reserve `n` permits for the `n` sparkable arguments/bindings of one
/// spark site. Returns 1 if the whole batch was granted (the caller MUST then
/// create+spark exactly `n` IVars, each of which releases one permit on
/// completion); 0 if over budget (the caller MUST take the direct arm and
/// allocate nothing). Atomic — no TOCTOU window between check and reserve.
#[unsafe(export_name = "cranelisp_spark_budget_try_reserve")]
pub extern "C" fn spark_budget_try_reserve(n: i64) -> i64 {
    let cap = *SPARK_BUDGET as isize;
    // Fast reject (the common case under explosion): a single load, no RMW.
    if IN_FLIGHT_SPARKS.load(SeqCst) + n > cap { return 0; }
    // Commit the whole batch atomically (CAS loop) — all-or-nothing so the cap
    // is a true bound, not a soft target that N concurrent sparkers each blow past.
    loop {
        let cur = IN_FLIGHT_SPARKS.load(SeqCst);
        if cur + n > cap { return 0; }
        if IN_FLIGHT_SPARKS.compare_exchange(cur, cur + n, SeqCst, SeqCst).is_ok() { return 1; }
    }
}
```

- **Try-reserve, not check-only.** A check-only `available()` has a TOCTOU window: between "is there room for `n`?" and the `n` allocations, other threads also check-and-go, so total reservations can exceed `cap` by many batches → the cap stops bounding total in-flight work, which is the whole point. Atomic try-reserve **commits the `n` permits in one CAS**, so `cap` is a genuine bound. Try-reserve is therefore *required*; check-only is insufficient.
- **Batch granularity.** One site reserves all `n` of its sparkable args at once and only takes the lenient arm if the **whole** batch fits. Partial grants would leave some args sparked and others direct within one apply — needless complexity for no benefit; the ≥2 gate already guarantees `n ≥ 2`.
- **Atomic discipline.** SeqCst throughout, consistent with the module's Decision-13 invariant. The over-budget path is **load-only** (no RMW) — on x86 a plain `mov`, on ARM an `ldar` — which is what keeps the per-node floor residual tiny (§3.6.3).

**Release accounting — internal, via `InFlightGuard` (no exported release symbol).** The gate reserves `n` up front; release is **one permit per completing spark**, fired from inside `ivar_spark`'s spawned rayon closure (Rust, not emitted code) by reusing the existing `InFlightGuard` RAII drop (`IN_FLIGHT_SPARKS.fetch_sub(1, SeqCst)`). Reserve `n` (gate) ↔ create+spark `n` IVars (lenient arm) ↔ `n` `InFlightGuard` drops (one per spawn-task end) — balanced by construction. Because every granted batch creates exactly `n` IVars and `ivar_create` cannot fail (allocation abort = process death), there is no emitted path that reserves without sparking, so **no release needs to be callable from emitted code** — release stays a private decrement. The RAII guard makes release fire even on a Rust unwind inside the worker (allocation failure / internal bug); a *leaked* reservation is the dangerous direction (it permanently lowers the effective budget, drifting toward permanent-direct — silent serial degradation), and the guard closes that. Note the main thread may **claim-compute** a granted cell at the barrier before its rayon task runs (work conservation, §3.5); that does not change release accounting — the rayon task still runs (hits the RESOLVED fast path), drops its guard, and releases.

#### 3.6.2 The create-gate (backend codegen)

The gate replaces the *unconditional* Phase-1 emission (§4.2/§4.4) with a runtime branch. At a spark site with `n` sparkable positions (`n ≥ 2`, the existing gate):

```
n_val   = iconst n
granted = call cranelisp_spark_budget_try_reserve(n_val)   // 1 = lenient, 0 = direct
brif granted, lenient_block, direct_block

lenient_block:                       // budget granted
    <Phase 1: create+spark n IVars>  // the only place allocation happens
    <install sparked_args context>
    val_l = <dispatch through the unchanged lowering; barrier forces each sparked
             position at its left-to-right slot — §4.4 Phase 2/3>
    <restore sparked_args context>
    jump join_block(val_l)

direct_block:                        // over budget
    val_d = <dispatch through the unchanged lowering with NO sparked_args installed
             ⇒ every position is compile_expr'd normally — the existing sequential path>
    jump join_block(val_d)

join_block(result: i64):             // both arms produce the call's result value
    ... continues with `result`
```

- **One join point, one block param.** Both arms run the *same* call lowering (`dispatch_apply` for the apply site; `compile_let_sequential` body vs the lenient `let` for the let site) and produce the call/body result as a single i64 `Value`. The two arms `jump join_block(val)`; the gate returns the join block's param. The downstream RC/consuming treatment sees one ordinary i64 either way — no divergence past the join.
- **Both arms produce identical arg values feeding the call.** Lenient arm: sparked positions are forced (§4.4 Phase 2), non-sparked positions `compile_expr`'d in place. Direct arm: *all* positions `compile_expr`'d in place. The forced value of a spark is byte-identical to the directly-evaluated argument (same thunk body, observational equivalence §8); only the schedule differs.
- **Composition with the barrier (load-bearing).** The barrier (force-all-before-call, §4.4 Phase 2) lives **inside the lenient arm** — it is unchanged and still guarantees no path reaches the call instruction with an unforced IVar. The direct arm has no IVars to force. Ferry soundness (§5) is unaffected: the lenient arm is the same structured spark→join-all→call fork-join as before; the direct arm is plain sequential evaluation.
- **Composition with TCO gating (§2.5.3) — unchanged.** The two TCO self-call fast paths still `return` early, *above* the gate, so a tail self-jump never reaches it. A non-self tail call still flows through `dispatch_apply` returning a `Value` (the backend does not emit a true tail-return here — the TCO jump is the only loop-header path), so the join-block-with-param shape is uniform whether or not the apply is in tail position; `in_tail_position` is saved/restored inside each arm exactly as today.
- **Cost of the gate when there is no explosion.** Under any workload that stays at/below `cap`, every site's try-reserve is granted ⇒ every site takes the lenient arm ⇒ behaviour is byte-for-byte the pre-gate behaviour, plus one granted try-reserve per site. The gate engages its direct arm *only* under spark explosion.

#### 3.6.3 Floor-restoration argument

> **Scope of this argument (FIXME 0459 doc-half; S94 /port ruling + S99 ablation).** Everything
> below restores the floor against **spark-*machinery* overhead** — the per-node IVar/thunk
> allocation the create-gate bounds to `O(cap)`. That is the `fib`-explosion this section was built
> for, and the argument is correct **within that scope**. It does **NOT** cover **per-branch
> user-level contention** — the concurrent heap allocation + atomic-RC cache-line bouncing
> (Decision 13) the `cap` live branches generate — which the count-only create-gate cannot see.
> For allocation-/RC-heavy workloads that user-contention floor is **VIOLATED on release**: the S99
> ablation measured F2 parallel **2.3–3× slower** than serial and F4 **6–15× slower**, and the
> three in-track pre-Phase-H levers each moved the dominant term only single-digit percent
> (capture-by-borrow ~0%, saturation gate ~9%, mimalloc user-neutral-to-worse on the clean probe —
> `s99-measurement.md` §8–§10; `ring2-rc.md` §5.5.2.7). The contention floor is restored only by
> **Phase-H** memory-model work. The `ON < 1.3·OFF` acceptance test below is therefore the
> **spark-machinery** floor witness (allocation-/RC-*light* branches), not a universal
> never-slower-than-serial guarantee.
>
> **The contention-aware gate ask (0459) landed opt-in as the *saturation gate*.** 0459 asked for
> a contention-aware gate as the in-track path back toward the floor; Wave 1c delivered it as
> `CRANELISP_SATURATION_GATE=1` (`ivar.rs`, off by default, byte-identical-off), which tightens the
> in-flight cap from `4×threads` to `threads` so saturated subtrees run inline on the current
> thread. It is sound and cheap but recovers only **~9%** of the (b) contention on the clean F2
> probe (it throttles the *number* of bouncers at the margin; it cannot touch the leaf-copy RC
> *volume*). Kept opt-in as honest scheduling hygiene / Phase-H-durable complement; **default-on is
> deferred to Phase-H** (rests on the floor-restoration/honesty argument, not a (b)-cure magnitude).

For a naive over-sparking recursion (`fib`): the first ≈`cap` sites reached at runtime (near the root, as rayon work-steals breadth-first) reserve and spark; once `IN_FLIGHT_SPARKS` saturates, every deeper site's try-reserve returns 0 on a **single load** and takes the direct arm. The direct arm is the existing sequential codegen — it recurses into `fib` whose body again hits the gate at runtime, gets 0 again while the budget stays full, and continues serially with **zero allocation**. As top-level sparks complete they release permits, re-admitting a bounded frontier of new sparks; in-flight sparks stay `O(cap)`, so total IVar/thunk allocation footprint is `O(cap)`, not `O(nodes)`. The whole exponential tail therefore runs at ≈ serial cost.

- **Residual 1 — one atomic per sparkable site.** Each sparkable apply node pays one `try_reserve`, which on the over-budget path is a single SeqCst *load* + compare (no RMW, no allocation). This is ~2 orders of magnitude cheaper than the ≈4 tracked allocations per node it replaces, collapsing the measured ≈140× back toward ≈1×. It is the one irreducible cost of a per-site runtime decision and is the floor residual the acceptance test (`ON < 1.3·OFF`) must tolerate; minimising it is exactly why the over-budget path is load-only.
- **Residual 2 — the top ≈`cap` sites still pay spark overhead.** The frontier sites that *are* granted pay IVar create/spark/force/dealloc + thread-pool overhead. This is acceptable and intended: it is precisely the bounded parallelism the feature exists to extract. The floor guarantee is "never *dramatically* slower than serial," not "zero overhead."

**Two degenerate-to-serial paths (unchanged in spirit).** `CRANELISP_NO_LENIENT=1` suppresses sparking at the *codegen* layer — neither the gate nor any create/spark/force is emitted. `CRANELISP_SPARK_BUDGET=0` degenerates at the *runtime* layer — `try_reserve` always returns 0, so every site takes the direct arm (no allocation). The two are observably equivalent; `=0` is the runtime escape hatch for an already-compiled binary. Note this is a behaviour upgrade over the pre-create-gate `=0` (which still allocated then resolved inline, hence the 140× — now `=0` truly allocates nothing).

**Cap default + knob.** Default `4 × rayon::current_num_threads()` (keep cores fed with slack for load imbalance while holding in-flight work `O(threads)`). `CRANELISP_SPARK_BUDGET=N` overrides; non-parsing values fall back to the default.

**Global scope — bounds both spark clients.** `IN_FLIGHT_SPARKS` is a single process-global; the create-gate is emitted at **both** spark sites — the apply path (§4.4, the explosion source and Slice-1's primary deliverable) and the `let` path (§4.2). Gating both is required, not optional: moving the budget out of `ivar_spark` (now always-spawn, §3.4) removes the only budget the `let` path had, so the `let` site must regain it via its own create-gate or a recursive function with a wide independent `let` could re-explode. The two sites share one gate-emission helper (Principle 7) — the apply and `let` arms differ only in *which* lowering each calls, not in the gate shape. *`let`-path perf-test note for `/qa`:* with the gate, a `let` that would spark more than `cap` bindings now takes its **direct (fully sequential) arm** rather than spawning all N — confirm `lenient_vec_map_reduce_parallelizes` and its control either stay under `4×threads` concurrent on CI hardware or pin `CRANELISP_SPARK_BUDGET` high.

**Public-API impact — ONE new C-ABI symbol (flag for `/arch`).** `cranelisp_spark_budget_try_reserve(n: i64) -> i64` is a new `pub extern "C"` export in `cranelisp-intrinsics` with an `export_name` attribute, so it appears in `cranelisp-intrinsics/public-api.txt` and is registered in `catalog.rs::intrinsics_table()` as an `IntrinsicEntry { param_count: 1, has_return: true, is_runtime: true }` (same mechanism as `cranelisp_ivar_*`). This is a public-API addition against the Phase-2/3 zero-public-API finding and is routed to `/arch` (see §3.6.4). The reservation counter and cap stay module-private statics; **release is internal** (`InFlightGuard`, no export). The backend names the new symbol by string at codegen (`emit_extern_call("cranelisp_spark_budget_try_reserve", …)`) exactly as it names the IVar symbols.

#### 3.6.4 Cross-cutting flags

- **Public-API addition → `/arch`.** Per `design/arch/CLAUDE.md` baseline-diff discipline, the new `cranelisp_spark_budget_try_reserve` export requires, in the implementing change-set: (1) `cranelisp-intrinsics/public-api.txt` regen via the canonical `cargo public-api … -p cranelisp-intrinsics` command; (2) the BC §4b invariant-11 (`intrinsics_table()`) narrative updated to name the symbol; (3) `/arch` approval that this is a legitimate edge evolution, not surface leakage. **`/design`(backend) does not approve it.** The proposed signature is exactly `cranelisp_spark_budget_try_reserve(n: i64) -> i64`; semantics as §3.6.1. Recommendation to `/arch`: approve — it is the minimal possible surface (one symbol; release internal) and is the CPU instance of the FIXME-0442 budget primitive that slice 4 will generalize.
- **Unified CPU+IO budget → `/arch` (FIXME 0442, deferred slice 4).** This try-reserve *is* the CPU instance of the unified budget abstraction FIXME 0442 escalates. The over-budget **actions still differ fundamentally** (CPU = take the direct arm / compute on the caller; I/O = admission-park, since you cannot cheaply "run an I/O effect inline"), so the two may share only the try-reserve *shape* rather than one mechanism. Kept shaped-to-be-subsumed (Principle 8): a plain atomic counter + cap + a **single** try-reserve primitive + a **single** gate-emission helper, so slice 4 can generalize the counter into a per-token/per-kind budget table — not stand up a second throttle. The unify-or-not call stays deferred to slice 4 (unmet trigger).

#### 3.6.5 History (terse)

Sprint 92 Slice 1 first shipped the budget *inside* `ivar_spark` (reserve-then-check; over-budget → resolve inline). It bounded **memory/concurrency** (examples/30 OOM fixed: RSS ~24 MB vs ~14 GB) but **could not restore the floor** for over-sparking recursion, because the IVar + thunk were allocated for every sparkable arg *before* `ivar_spark` ran (≈140× serial for naive `fib`, FIXME 0444). The create-gate above is the resolution (FIXME 0444): the budget decision moves *before* allocation. The in-`ivar_spark` reserve-then-check and its inline fallback are **removed**; `ivar_spark` reverts to always-spawn (§3.4). Retained from the first cut, unchanged: the `IN_FLIGHT_SPARKS` counter + `SPARK_BUDGET` cap + `CRANELISP_SPARK_BUDGET` knob + `InFlightGuard` (now repurposed as the per-spark release), and the independent `ivar_force` claim-compute (work conservation) + first-error-wins ferry save/restore fix (a correct, separate §12.4.3 conformance fix).

## 4. Codegen Path

### 4.1 `compile_let` Decision Point

When `compile_let` processes a `Let` expression:

```
if *LENIENT_DISABLED || self.in_trace_body {
    compile_let_sequential(bindings, body)
} else {
    let sparkable = find_sparkable_bindings(bindings, &self.globals);
    if sparkable.is_empty() {
        compile_let_sequential(bindings, body)
    } else {
        compile_let_lenient(bindings, body, &sparkable, span)
    }
}
```

### 4.2 `compile_let_lenient`

Three phases:

**Phase 1 — Create and spark IVars** (for sparkable bindings only):

For each sparkable index `idx`:
1. Wrap `bindings[idx].1` (the value expression) in a synthetic `Expr::Lambda { params: [], body: val_expr }`.
2. Compile the lambda — this produces a zero-arg thunk closure pointer with captures for any free variables.
3. Emit `call cranelisp_ivar_create(thunk_ptr) -> ivar_ptr`.
4. Emit `call cranelisp_ivar_spark(ivar_ptr)`.
5. Store `(idx, ivar_ptr)` in a map.

**Phase 2 — Process bindings in order** (all bindings, sparkable and non-sparkable):

For each binding `(name, val_expr)` at index `i`:
- If `i` is sparkable: emit `call cranelisp_ivar_force(ivar_map[i]) -> forced_val`. Then emit `emit_dec(ivar_ptr)` — the main thread's reference to the IVar cell is released. Bind `forced_val` to `name`.
- If `i` is non-sparkable: compile `val_expr` normally. Bind the result to `name`.

This is the **barrier model**: all IVars are forced before the body executes. The order of forcing matches the source order of bindings, ensuring deterministic behavior when the forced values are used.

**Phase 3 — Compile body**:

Compile the `let` body expression normally. All bindings are in scope.

### 4.3 Thunk Closure Layout

Thunk closures use the reimplementation's standard `HeapClosure` layout (Decision 11):

```
Base pointer →
  +0   alloc_size: i64
  +8   rc: i64
  +16  code_ptr: i64        (extern "C" fn(env_ptr: i64) -> i64)
  +24  drop_glue_ptr: i64   (or 0 if no heap captures)
  +32  capture_0: i64
  +40  capture_1: i64
  ...
```

The thunk's captures are the free variables of the binding expression that are in scope in the enclosing function. The code_ptr points to a generated function that loads captures from the closure struct, evaluates the expression, and returns the result.

### 4.4 Apply-Argument Lenient Emission (Sprint 92)

`compile_apply` gains a lenient pre-pass symmetric to `compile_let`'s §4.1 decision point, reusing the exact same IVar create/spark/force/dec emission helpers (`emit_extern_call("cranelisp_ivar_create"|"cranelisp_ivar_spark"|"cranelisp_ivar_force", …)`, `emit_rc_dec_for_ivar`). As of the create-gate (§3.6) it also calls **one** new ABI symbol, `cranelisp_spark_budget_try_reserve` (the budget query). The decision is taken at the top of `compile_apply`'s non-tail arm:

```
if !*LENIENT_DISABLED && !self.in_trace_body && not a tail self-call {
    let sparkable = find_sparkable_args(args, &constructors);
    if sparkable.len() >= 2 {
        // create-gate (§3.6.2): runtime branch on the budget
        granted = call cranelisp_spark_budget_try_reserve(sparkable.len())
        brif granted, lenient_arm, direct_arm
        // lenient_arm: spark, barrier-force, dispatch (the three phases below)
        // direct_arm:  dispatch with NO sparked_args (existing sequential apply)
        // join_block(result): both arms produce the call result Value
    }
}
// else: existing sequential apply (unchanged)
```

The **create-gate is the structural change Sprint 92 Slice 1 (create-gate fix) lands** — the three phases below now run **only on the budget-granted (lenient) arm**; the over-budget (direct) arm dispatches through the unchanged lowering with no `sparked_args` installed, so every argument is `compile_expr`'d sequentially and **nothing is allocated** (§3.6.3 floor). Both arms `jump join_block(result)`; `compile_apply` returns the join param. See §3.6.2 for the block structure, the join-point/block-param shape, and the TCO-fast-path composition.

**Three phases (the lenient arm only), mirroring `compile_let_lenient` (§4.2):**

1. **Create + spark** (sparkable arguments only): for each sparkable index, wrap the argument `MonoExpr` in a synthetic zero-arg `Lambda` thunk (`(Fn [] T)` where `T = arg.ty()`), `compile_expr` it to a closure pointer, `cranelisp_ivar_create(thunk) -> ivar`, `cranelisp_ivar_spark(ivar)`, and record `(idx, ivar)`. This is verbatim the §4.2 Phase-1 emission, applied to argument positions instead of binding positions.

2. **Barrier — force all sparked arguments before the call** (the load-bearing structured-fork-join invariant, Phase-2 guard-rail). Build the argument `Value` vector in left-to-right order: a sparkable index emits `cranelisp_ivar_force(ivar) -> forced_val` followed by `emit_rc_dec_for_ivar(ivar)` (release the calling thread's cell reference; the spark task also dec's; the IVar-aware `cranelisp_ivar_dealloc` frees the cell and any ferried error String); a non-sparkable index is `compile_expr`'d in place. **Every sparked argument is forced before any code of the call is emitted** — there is no path on which the call instruction is reached with an unforced argument IVar. This keeps the construct a *structured* fork-join (spark → join-all → call), which is precisely what keeps the ferry-soundness argument (§5) valid; it must not drift toward launch-and-don't-join (that is slice 5's supervised launch-and-continue, out of scope).

3. **Dispatch** the call with the now-forced argument `Value`s through the **existing** apply lowering (`compile_resolved_call` / `compile_var_apply` / constructor / closure / direct call). The forced values are ordinary i64 `Value`s indistinguishable from sequentially-compiled ones, so the downstream RC/consuming-convention treatment is unchanged.

**RC / consuming convention.** The sequential apply path inc's heap-typed *variable* arguments for the consuming convention (`compile_consuming_arg_list`). A sparked argument is necessarily a non-trivial `Apply` (the cost heuristic excludes var refs and literals), so it is a **temporary** at `rc=1` produced by the thunk via the IVar — it transfers ownership into the callee exactly as a sequentially-compiled temporary `Apply` argument would. No consuming inc is owed for sparked positions; non-sparkable positions retain the existing per-argument inc/transfer treatment. `/dev` must preserve this: the force result is the temporary, fed straight into the call arg vector without an extra inc.

**Scope of the change.** The backend half is contained in `cranelisp-backend` (the sparkability sibling in `sparkability.rs`, the create-gate + lenient pre-pass in `apply.rs`/`compile_apply`, and the symmetric gate at the `let` site in `let_if.rs`). The IVar machinery (`cranelisp-intrinsics`) is reused unchanged except for the create-gate's budget primitive: `ivar_spark` reverts to always-spawn (§3.4), the in-`ivar_spark` budget is removed, and **one** new C-ABI symbol `cranelisp_spark_budget_try_reserve` is added (§3.6.1, §3.6.4). That new export is a `cranelisp-intrinsics` `public-api.txt` diff — routed to `/arch` per the baseline-diff discipline (§3.6.4); it is the *only* public-API change and is expected. The sparkability pass and the gate emission stay `pub(crate)` in backend (no backend `public-api.txt` diff).

#### 4.4.1 Capture-by-borrow on the spark thunk (Sprint 99, FIXME 0461)

> **Arch-ratified contract — the RC model is pinned in `ring2-rc.md` §5.5.2; this is the emission
> half.** Wave-1b builds capture-by-borrow behind a toggle (env/feature; ablation study,
> `SPRINT.md` §Wave 1) so the (b)-contention delta is A/B-measurable; the *contract* below is what
> `/dev` implements regardless of the toggle's default. No `cranelisp-types` / public-API impact —
> internal backend RC emission only.

Phase-1 (Create + spark) compiles each sparkable argument's synthetic `(Fn [] T)` thunk via
`this.compile_expr(&thunk_expr)` (`apply.rs:129–135`). That path runs `compile_lambda`, which for
every heap-typed **capture** of the thunk emits `emit_capture_inc` at the capture-store
(`control_flow/lambda.rs:159`) and a matching drop-glue dec in `build_closure_drop_glue`
(`lambda.rs:175`). This inc/dec pair on **shared enclosing-scope cells** — under N workers, on the
*same* parent bindings across all branches — is the (b) atomic-RC cache-line-bouncing term Wave 0
found dominant (`tests/plan/s99-measurement.md`: F2 99% user / F4 ~70%).

**The elision.** Because the apply-arg spark is **structurally joined** — Phase 2's barrier forces
every sparked IVar *before* the call instruction (`apply.rs`, the §4.4 Phase-2 guard-rail), so the
parent frame is provably live across the whole spark→join→call sequence — every capture of the
thunk is a **borrow**, not a retain, per the `ring2-rc.md` §5.5.2 generalisation of the
`borrowed_vars` discipline. Emission contract:

1. **Set the borrow flag around the thunk compile only.** A `FnCompiler` bool (sibling of
   `in_trace_body` / `suppress_spark_gate`, `fn_compiler.rs`), e.g. `spark_capture_borrow`, is set
   `true` immediately before `this.compile_expr(&thunk_expr)` for a sparked argument and restored
   after (save/restore, as `sparked_args` already does at `apply.rs:152,161`). The symmetric `let`
   site (`let_if.rs`, §4.2 Phase 1) and the `ParBind` branch-closure build (`par_bind.rs`) set it
   too. **`launch.rs`'s `LaunchContinue` arm never sets it** — the detached launch keeps the retain
   (`ring2-rc.md` §5.5.2.1 exclusion; the join/detach signal is the `MonoExpr` variant itself,
   Principle 20, read not analysed).

2. **Skip both inc and dec, coarsely, for every heap capture of the thunk.** When the flag is set,
   `lambda.rs`'s capture-store skips `emit_capture_inc` (`lambda.rs:156–160`) **and**
   `build_closure_drop_glue` skips the heap-capture dec (`lambda.rs:183–196`) — symmetric, exactly
   §5.5's borrowed-Var rule. Skipping only one is an under/over-count bug; skip **both** for the
   whole thunk. No per-capture decision (`ring2-rc.md` §5.5.2.2 — the coarse Principle-8 line).

3. **The single retain is the return value, via the unchanged path.** A sparked argument is a
   non-trivial `Apply` (cost heuristic, §2.2), so the thunk's result is a **fresh `rc=1` temporary**
   from the callee under the consuming convention — NOT a borrowed capture — and transfers ownership
   out of the IVar into the joining call exactly as the existing "RC / consuming convention"
   paragraph above states. **This paragraph is unchanged by the borrow:** the borrow elides the
   *capture* incs on the thunk env, not the return-value transfer. The only escape rides Decision 24
   + `ring2-rc.md` §5.6 (the S98-hardened path, FIXME 0497) — no new machinery.

**Soundness + failure mode** are pinned in `ring2-rc.md` §5.5.2.3–.4: parent-outlives-spark makes
the borrow sound; immutability removes the §5.5 COW hazard; a wrong gate (borrowing a detached
capture, or an escape via any path but the audited return value) is a UAF of the S98-bug-#2 class,
structurally precluded here because the design borrows **all** captures uniformly (one flag, no
bespoke escape traversal with blind spots) and retains **only** the return value via already-audited
paths. **Do not** widen "borrow" to a value-flow non-escape analysis — that is Phase H
(`ring2-rc.md` §5.5.2.5), out of scope.

**Carve-out — the §4.5 dependent-thunk `§ivar_a` captures are NOT borrows.** The borrow flag
governs captures of **enclosing-scope owned parent bindings** taken by the *standard*
`compile_lambda` capture-store path. It MUST NOT elide the synthetic `§ivar_a` IVar-pointer captures
that a **dependent** `let` spark takes (§4.5), which are built by the *manual* par_bind-style inner
fn and whose inc is a load-bearing **keepalive** (§4.5 "RC discipline for the captured IVar
pointer": the inc is what keeps `ivar_a` alive until the dependent thunk forces it; eliding it frees
the cell early → UAF). Two reasons the elision does not reach them, and `/dev` must keep both true:
(i) the §4.5 dependency captures are emitted by the manual path, not the flag-reading capture-store
loop; and (ii) an `ivar_a` cell is a *sibling spark's* cell, not a structurally-joined-parent-owned
binding, so the §5.5.2 live-parent guarantee does not cover it. Scope the flag to the standard
capture path only; when the dependent-thunk feature is in play, the manual `§ivar_a` inc/dec stays.

**Test obligations** are enumerated in `ring2-rc.md` §5.5.2.6 (the mandatory `LaunchContinue`
UAF-exclusion guard; the F1–F4 parallel≡serial correctness guard; the `CRANELISP_RC_STATS`
inc-count-drop witness). Wave 1b co-lands them with the `/dev` fix.

### 4.5 Dependent-binding emission (S94, FIXME 0424 limit #2)

`compile_let_lenient` (§4.2) grows to handle sparkable bindings whose thunks reference
earlier sparked bindings. The three-phase barrier model is **unchanged**; only Phase 1
thunk construction changes, and it changes only for *dependent* sparks.

**Phase 1 processes sparkable bindings in source order** (already the case) — this is
the topological order (§2.6.1), so when binding `b`'s thunk is built, every IVar it
depends on (`ivar_a`, …) has already been created in `ivar_map`. For a dependent
sparkable binding `b` at index `i` with sparked dependencies `{a, …}`:

1. **Make each dependency IVar addressable inside the thunk.** The dependency `a` is
   not a `Value` in scope at Phase 1, so the generic `compile_lambda` capture path
   (which captures only names already in `self.variables`) cannot capture it. Bind a
   fresh synthetic capture name per dependency (e.g. `§ivar_a`) to the IVar `Value`
   already in `ivar_map[idx_a]`, marked `AlwaysHeap` so the capture inc fires.
2. **Force the dependencies in a thunk-body prologue, then compile the *unmodified*
   RHS.** **Stay backend-internal — do NOT introduce a new `MonoExpr` variant or a
   synthetic intrinsic-call node.** A new `MonoExpr` shape would touch `cranelisp-types`
   (arch-owned) and risk a public-API edit, breaching R5's "no public-API impact."
   Instead, build the dependent thunk's inner fn the way `par_bind.rs` builds its
   continuation closure — **manually**, not via `compile_expr(Lambda)`: capture the
   `§ivar_a` IVar pointers, and at the inner-fn entry emit, per dependency, a force +
   bind:

   ```
   §ivar_a_cap = load capture(§ivar_a)         ; the captured IVar pointer
   a_val       = call cranelisp_ivar_force(§ivar_a_cap)   ; the SAME extern the barrier emits
   bind a -> a_val in the inner-fn variable env
   ```

   then `compile_expr` the **original, unrewritten** RHS, whose `Var(a)` now resolves to
   the forced `a_val`. This reuses the existing `cranelisp_ivar_force` extern (IVar
   machinery single-source, §3.5) with **zero** boundary-type change, and it is the same
   manual-inner-fn pattern `par_bind.rs` already establishes. (If a future refactor
   prefers a MonoExpr-level rewrite, it must be confirmed with `/arch` first — it is not
   needed for limit #2 and is explicitly avoided here to honour R5.)
3. **Create+spark the thunk's IVar** exactly as §4.2 Phase 1 — the only difference is
   the prologue-forcing inner fn and its IVar-pointer captures.

**RC discipline for the captured IVar pointer (the one new rule /dev MUST get right).**
A dependent thunk captures `ivar_a` (a heap-allocated, atomic-RC IVar cell), so:

- The capture must **inc** `ivar_a`'s RC when stored into the thunk env (the closure
  env holds its own reference) — the standard `emit_capture_inc` for a heap-typed
  capture (`lambda.rs`). Treat the synthetic `§ivar_a` as `AlwaysHeap` so the inc fires.
- The thunk's **drop glue must dec** `ivar_a` (standard `build_closure_drop_glue`
  capture-dec). This balances the capture inc.
- This inc is what keeps `ivar_a` alive for the dependent thunk even though Phase 2
  dec's the main thread's `ivar_a` reference after forcing `a` for `a`'s own binding
  (§4.2). With the capture inc, `a`'s Phase-2 dec brings rc from (1 main + 1 spark-task
  + 1 per dependent capture) down by one — the cell survives until the dependent
  thunk(s) and the spark task have all dec'd. The existing RC-to-0 dealloc path
  (`dealloc_ivar`, §5) frees the cell (and any ferried error String) when the last
  reference goes.

**Phase 2 and Phase 3 are unchanged.** Phase 2 still forces every sparked IVar in
source order and binds the forced value to its name; a dependent binding `b` is forced
exactly like any other spark (its thunk, when it runs, forces its own dependencies). The
barrier (force-all-before-body) is intact, so the structured fork-join invariant (§5)
holds and the ferry stays sound (§2.6.4 below).

#### 4.5.1 Observational equivalence + ferry soundness (restating §5/§8 for the dependent case)

A dependent spark is observationally equivalent to sequential evaluation:

- **Value.** Forcing `ivar_a` yields the identical value sequential evaluation of `a`
  produces; the dependent thunk computes `b` from that same value. Pure args, no
  order-observable difference (§8).
- **First-error-wins.** If `a`'s thunk panics, both Phase 2's force of `a` (at index
  `idx_a < i`) and the dependent thunk's force of `ivar_a` observe the ferried error
  (§5). Because the barrier forces in **source order**, `a` (earlier index) surfaces
  its error before `b` — matching a left-to-right sequential evaluation that aborts on
  `a` first. No new ferry mechanism is needed; the dependent force is just another
  reader of `ivar_a`'s resolved/errored cell.
- **Non-termination** preserved: if `a` diverges, the dependent thunk's force of
  `ivar_a` never completes, exactly where sequential evaluation of `a` would hang.

## 5. IVar Drop Glue

**Not needed under the barrier model.** All IVars are created, sparked, and then forced within the same `let` compilation. After forcing, the main thread dec's the IVar (Phase 2). The spark task also dec's the IVar when it finishes (§3.4). One of these dec's brings the RC to zero and frees the cell.

Because IVars are always forced before scope exit, there is no scenario where an IVar is dropped while still PENDING. The barrier model guarantees this structurally.

If a future enhancement moves to per-use-site forcing (Phase 8 in the sketch's roadmap), IVar drop glue would be needed to handle the case where an IVar is never forced. That is out of scope for the current design.

**Thunk panic behaviour (as-built — the fork-join error-slot ferry).** A sparked thunk's runtime panic is **ferried** from the worker thread to the joining thread, so a panicking spark is observationally equivalent to a sequential evaluation that raised the same error (spec §12.4.3, first-error-wins). The mechanism (`ivar.rs`, `io.rs`; `design/arch/test-discovery.md` §6):

1. The IVar cell carries a sixth field, `error` at offset +40 (cell is 48 bytes, not 40). It is published together with `value` under the single `state = RESOLVED` SeqCst store.
2. **Worker-side stash**: the claiming thread (won the `PENDING → EVALUATING` CAS) calls the thunk, then `panic::take_runtime_error()`. A `Some(msg)` is allocated as a heap String and stored into the IVar's `error` field before the `RESOLVED` publish; the sentinel `value` (0) is published as-is.
3. **Join-side re-raise**: every reader of the resolved IVar — the claimant after evaluating, and any spin-waiter — calls `reraise_ferried_error`, which decodes a non-zero `error` field (without consuming it, so every joiner sees the same message) and re-raises it into its own thread's slot via `panic::set_runtime_error` (first-error-wins, idempotent per reader).
4. **Worker-slot hygiene**: `ivar_spark`'s rayon closure clears its own throwaway worker slot after `ivar_force` returns (the joining thread re-raises independently from the IVar field), so a ferried panic does not pollute later rayon work on the same worker.
5. **Cleanup**: the ferried error String (always `rc=1`, never shared) is freed with the cell — both dealloc paths (`ivar_spark`'s RC-to-0 branch and the backend's `emit_rc_dec_for_ivar` → `cranelisp_ivar_dealloc`) route through `dealloc_ivar`, which frees the String before the cell.

Soundness rests on the **structured fork-join invariant**: every spark joins (is forced) inside the dynamic extent of any enclosing `catch-runtime-error` bracket, so the re-raised error is observed at the same point sequential evaluation would observe it. The earlier Sprint-25 "remains in EVALUATING / spins indefinitely" disposition is superseded.

**The apply site is a new ferry entry point (Sprint 92), covered by construction.** Apply-arg sparking (§4.4) is a new place a sparked thunk can panic. No new ferry mechanism is needed: it reuses the identical IVar create/spark/force path, so the worker-side stash and join-side re-raise above apply verbatim. The ferry stays sound **because §4.4 Phase 2 forces every sparked argument before the call is emitted** — the apply is the same structured spark → join-all → call fork-join as the lenient `let`, so each sparked argument joins inside the dynamic extent of any enclosing `catch-runtime-error`, and first-error-wins selection at the apply matches a left-to-right sequential evaluation that raised the first argument's error. **What `/dev` must NOT break:** the barrier-before-call invariant. If any code path reached the call instruction with an unforced (or never-forced) argument IVar — e.g. by hoisting the dispatch ahead of a force, or by taking the TCO self-call fast path past the barrier — the construct would stop being a structured fork-join, a panicking spark could be silently dropped or observed out of order, and the ferry's soundness argument would no longer hold. The barrier is the load-bearing invariant, not an optimization detail. (Existing ferry tests cover the `let`/`Par` entry points only; the apply site needs its own panicking-sparked-argument test — see §9.)

## 6. RC Lifecycle

The full RC lifecycle of an IVar and its thunk:

1. Thunk closure compiled with `rc = 1` (normal closure compilation).
2. `ivar_create(thunk)` — IVar cell allocated with `rc = 1`. Thunk pointer stored in the cell. Thunk ownership is conceptually transferred to the IVar (the thunk's rc remains 1; the IVar holds the sole reference).
3. `ivar_spark(ivar)` — IVar `rc` incremented to 2 (spark task holds a reference).
4. One thread calls `ivar_force`:
   - Thunk is called, producing a result value (with `rc = 1` if heap-allocated).
   - Result stored in the IVar's value field.
   - State set to `RESOLVED`.
5. Main thread forces the IVar (may be the same or different from step 4): gets the result value.
6. Main thread dec's the IVar: `rc` goes from 2 to 1 (or 1 to 0 if spark already finished).
7. Spark task dec's the IVar: `rc` goes from 1 to 0 (or was already 0 if main dec'd second).
8. Whichever dec brings `rc` to 0 frees the IVar cell.
9. The forced result value is bound to the `let` variable with `rc = 1` and tracked in `scope_stack` for normal RC cleanup.

**Note**: The thunk closure is consumed by `ivar_force` (it is called exactly once). After forcing, the thunk pointer in the IVar cell is stale. This is safe because the IVar is freed before the thunk pointer could be reused, and no code reads the thunk pointer after forcing.

**Note**: The forced value's RC is not affected by the IVar mechanism. The thunk produces a result with `rc = 1`, and that value is returned through the IVar cell. It is then bound to the `let` variable and managed by the normal scope cleanup.

## 7. Sketch Comparison

### 7.1 What the Sketch Does

The sketch implements lenient evaluation with the same barrier-force model:

- `find_sparkable_bindings()` (`sketch/src/codegen/expr.rs:42-65`): same algorithm — free variable check, same `CHEAP_BUILTINS` list, same minimum-2 threshold.
- `compile_let_lenient()` (`sketch/src/codegen/expr.rs:735+`): three-phase compilation — create/spark IVars, force in order, compile body.
- `cranelisp_ivar_create/spark/force` (`sketch/cranelisp-runtime/src/intrinsics.rs:369-460`): same IVar state machine (PENDING/EVALUATING/RESOLVED), same CAS-based claiming, same spin-wait.
- `CRANELISP_NO_LENIENT` env var (`sketch/src/codegen/expr.rs:17-18`): identical mechanism.

### 7.2 Where the Reimplementation Follows

- **Sparkability algorithm**: identical. Same independence check, same cost heuristic, same cheap-builtins list, same minimum-2 requirement.
- **Barrier model**: identical. All IVars forced before body executes. No per-use-site forcing.
- **IVar state machine**: identical states and transitions (PENDING=0, EVALUATING=1, RESOLVED=2).
- **No IVar drop glue**: same decision, for the same reason (barrier model guarantees all IVars are forced).
- **Rayon global pool**: same thread pool choice.

### 7.3 Where the Reimplementation Diverges

| Aspect | Sketch | Reimplementation | Rationale |
|---|---|---|---|
| **Base pointer convention** | Interior pointer (payload pointer returned by `alloc_with_rc`) — IVar fields at offsets 0, 8, 16 from payload ptr; RC at payload-8 | Base pointer (offset 0 = alloc_size, offset 8 = rc, offset 16+ = payload) — IVar fields at offsets 16, 24, 32 from base ptr | Arch Decision 10. Positive offsets throughout; consistent with all other heap types. |
| **RC atomics ordering** | `Relaxed` for inc, `Release` for dec, `AcqRel`/`Acquire` for CAS | `SeqCst` for all atomic operations | Arch Decision 13. Consistency with the atomic RC convention used for all heap objects. Slightly more conservative but eliminates a class of ordering bugs. |
| **Closure layout** | `[code_ptr(8) \| captures...]` at payload pointer; no drop_glue_ptr | `[header(16) \| code_ptr(8) \| drop_glue_ptr(8) \| captures...]` at base pointer; `CAPTURES_START = 32` | Arch Decision 11. Embedded drop_glue_ptr enables self-contained closure dec without side tables. code_ptr is at offset 16 (not 0). |
| **Thunk code_ptr offset** | Offset 0 from payload pointer | Offset 16 from base pointer | Follows from the two divergences above. `ivar_force` reads code_ptr from `thunk + 16`. |
| **IVar alloc size** | `alloc_with_rc(24)` — 24 bytes payload, header size implicit | `alloc_with_rc(24)` — 24 bytes payload (allocator adds 16-byte header = 40 total) | `alloc_with_rc` takes payload size, not total size. Both sketch and reimplementation pass 24. |
| **`ivar_spark` RC access** | `(ivar as *mut i64).sub(1)` — negative offset to reach RC | `ivar + 8` — positive offset | Base-pointer convention: RC at fixed offset +8. |

> Note: the §7.3 "IVar alloc size" row describes the original Sprint-25 5-field cell (40 bytes). The as-built cell carries a sixth `error` field for the fork-join ferry → `alloc_with_rc(32)` = 48 bytes total (§5; `ivar.rs`). The sketch comparison is left as the historical Sprint-25 record.

## 8. Observational Equivalence, Evaluation Order, and the Spec Note (Sprint 92)

Apply-arg sparking is **observationally equivalent to sequential evaluation**, for the same reason the lenient `let` is (§2.5.2):

- **Pure arguments, unobservable order.** Argument expressions are pure values; side effects flow exclusively through the `IO` task tree and `bind!` (§10), never through raw argument evaluation. Two pure arguments have no observable evaluation-order dependence, so evaluating them concurrently yields byte-identical observable behaviour to any sequential order.
- **First-error-wins on panic.** The only order-sensitive observable is which runtime error surfaces when more than one argument would panic. The structured fork-join + IVar ferry (§5) re-raises the first ferried error at the join (the barrier, before the call), matching a left-to-right sequential evaluation that aborts on the first argument's error. `catch-runtime-error` enclosing the apply observes the panic identically in both modes.
- **Non-termination** is likewise preserved: if a sparked argument's thunk diverges, the barrier force on that IVar never completes, so the program hangs exactly where a sequential evaluation of that argument would.

**Normative finding — a spec note IS needed (FIXME 0441 filed, `target: /spec`).** This is the gap the Phase-3 brief asked to check for. The spec does not currently authorize apply-arg parallelization:

- §12.4.1 (Strict Evaluation) positively states *"Function arguments are evaluated left-to-right before the function body executes."*; §4.11's evaluation-order table and §2's grammar repeat the left-to-right guarantee for `(f arg1 … argN)`.
- §12.4.3 (Lenient Evaluation) grants the parallelization permission **only for `let` bindings** — there is no apply-argument carve-out, exactly as there was none before §12.4.3 was added for `let`.

The semantics are sound (observationally equivalent), but the *literal* §12.4.1/§4.11 left-to-right statements have no §12.4.3 exception authorizing apply-arg sparking — so the conformance suite could read those rows as forbidding it. **FIXME 0441** asks `/spec` to widen §12.4.3's permission to independent apply-arguments (mirroring the `let` carve-out) and to forward-note in §12.4.1/§4.11 that the left-to-right guarantee is the *observable* order. This is a permission-widening, not a behaviour change: a sequential implementation still conforms. It does **not** block slice-1 implementation (the capability is observationally equivalent), but the spec text should be brought into line.

## 9. Testability and Acceptance Criteria (Sprint 92)

What `/qa` and `/dev` should target (unit test mandatory per fix; e2e assessed and warranted here because the behaviour crosses `--run`/`--link`/REPL and is observable end-to-end):

**Correctness / equivalence (`/qa` integration):**
- A two-expensive-argument apply (e.g. `(Pair (fib a) (fib b))`) produces the identical result to the sequential build, and to the same program under `CRANELISP_NO_LENIENT=1` (the opt-out is the equivalence oracle).
- A general `par-map` (`fmap` of an expensive function over a collection) produces the identical result to sequential, validating FIXME 0424(i)'s closure.
- Single-expensive-argument and all-cheap-argument applies do **not** spark (the ≥2 gate + cost heuristic hold at the apply site) — a negative test.

**New ferry entry point (Phase-2 test discipline — mandatory):**
- A **panicking sparked apply-argument**: one of ≥2 sparked arguments raises a runtime error; the panic is ferried and surfaces on the joining thread (not silently dropped), and a `catch-runtime-error` enclosing the apply observes it. First-error-wins when two arguments would panic. This is the apply-site analogue of the existing `let`/`Par` ferry tests (which do not cover the apply entry point).
- Unit-tier: `find_sparkable_args` returns the expected indices for representative shapes (≥2 expensive args spark; cheap/constructor/literal/var args excluded; <2 candidates → empty), mirroring `sparkability_tests.rs`.

**Barrier invariant (the load-bearing guard):**
- A test that would fail if a sparked argument reached the call unforced — e.g. asserting equivalence under a tail-position apply with sparkable arguments (apply-arg sparking must be gated off the TCO self-call fast path, §2.5.3), so no path bypasses the barrier.

**Performance (demo / acceptance, per SPRINT.md):**
- A `par-map` / parallel benchmark showing near-linear speedup to N cores for ≥1µs/element work; observational equivalence with the serial result; **never slower than serial** (the overhead-bounded floor — the ≥2 gate + cost heuristic must keep cheap work on the sequential path).

**Spark budget — the create-gate (§3.6, Sprint 92 — `/dev`(backend)+`/dev`(intrinsics)+`/qa` targets):**
- *Floor restored under explosion (the create-gate's reason to exist):* naive recursive `(add-i64 (fib a) (fib b))` with the default budget is **not dramatically slower than serial** — the over-budget remainder takes the direct arm and allocates nothing (`ON < 1.3·OFF`, the loose CI witness). This is now *achievable* (it was architecturally unachievable with the in-`ivar_spark` budget, FIXME 0444) because the budget decision precedes allocation. `examples/30` likewise completes in test time.
- *Three-regime equivalence:* serial (`CRANELISP_NO_LENIENT=1`), under-cap (default budget, all sites granted), and over-cap (low budget, some sites direct) all produce byte-identical results — granted-vs-direct is a scheduling choice only (§8).
- *Degenerate-to-serial:* `CRANELISP_SPARK_BUDGET=0` ⇒ `try_reserve` always returns 0 ⇒ every site takes the direct arm, allocating nothing; result equals the `CRANELISP_NO_LENIENT=1` result.
- *Knob:* default cap = `4 × current_num_threads()`; `CRANELISP_SPARK_BUDGET=N` overrides; non-parsing values fall back to the default.
- *No permit leak (unit, mandatory):* after a workload — including one whose **sparked thunk panics** — `IN_FLIGHT_SPARKS` returns to 0 (the `InFlightGuard` release runs on completion and on unwind). Reserve `n` ↔ `n` spawned tasks ↔ `n` guard drops.
- *Try-reserve unit (`ivar` tests):* `try_reserve(n)` returns 1 and bumps the counter by `n` when `cur + n ≤ cap`; returns 0 and leaves the counter unchanged when `cur + n > cap` (the atomic all-or-nothing batch property — no TOCTOU partial grant); each spawned spark releases exactly one permit on completion.
- *Gate unit (`/dev`(backend) sparkability/codegen tier):* a ≥2-sparkable-arg apply emits the `try_reserve` branch with a lenient arm (create+spark) and a direct arm (no IVar emission); a `<2` apply emits neither gate nor IVars (the existing sequential path).
- *`let`-path regression re-validation:* per §3.6, confirm the existing `let` perf tests are not perturbed by the gate's direct arm (or re-pin their budget) — same surface SPRINT.md flags for naive-fib.

**Dependent-binding spark — limit #2 (§2.6, §4.5; S94 FIXME 0424 — `/dev`(backend)+`/qa` targets):**

- *Sparkability unit (`sparkability_tests.rs`, mandatory):* `find_sparkable_bindings`
  now admits a dependent binding when **all** its earlier-bound dependencies are
  themselves sparked (`[(a (fib n)) (b (g a (fib m)))]` → both `a` and `b` sparkable);
  and **excludes** a dependent binding when any dependency is non-sparked
  (`[(a (id x)) (b (g a (fib m)))]` where `a` is a cheap/var binding → `b` not
  sparkable). The ≥2 gate and cost heuristic still hold (a lone dependent spark → empty).
- *Sequential identity (equivalence oracle, `/qa` integration):* a `let` with a
  dependent sparkable binding produces the **byte-identical** result to the same program
  under `CRANELISP_NO_LENIENT=1` and to a hand-sequentialized rewrite — across `--run`
  and REPL. Granted-vs-direct (under-cap vs over-cap budget) and serial all agree
  (§3.6 three-regime equivalence, extended to the dependent shape).
- *Parallelism achieved (acceptance):* a partially-dependent binding whose independent
  sub-work is expensive (`(b (g (h c) (f a)))`, `c` independent, `a` sparked) overlaps
  `(h c)` with `a`'s computation — measured faster than serial for ≥1µs/element work,
  never slower than serial (the §2.6.2 floor).
- *Captured-IVar RC (unit, mandatory — the one new RC rule, §4.5):* after a workload
  with a dependent spark (including one whose **dependency thunk panics**),
  `IN_FLIGHT_SPARKS` returns to 0 and no IVar cell leaks — the dependent thunk's capture
  inc is balanced by its drop-glue dec, and the dependency cell is freed exactly once
  when its last reference (main Phase-2 dec / spark-task dec / dependent-capture dec)
  goes. Inspect the dependent thunk's CLIF on a shrunk single-dependency repro to
  confirm the captured `§ivar_a` is inc'd once at capture and the thunk inner-fn
  prologue forces it via `cranelisp_ivar_force` before the RHS uses `a` (not a stale
  value load).
- *Ferry first-error-wins for the dependent case (`/qa` integration):* when a sparked
  dependency `a` panics, the error surfaces at the source-order barrier (before the
  dependent binding), and a `catch-runtime-error` enclosing the `let` observes it —
  identical to sequential left-to-right (§4.5.1).
